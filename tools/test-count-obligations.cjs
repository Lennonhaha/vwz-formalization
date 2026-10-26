#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
//
// Regression tests for tools/count-obligations.cjs.
//
// Every case is a fixture tree in a temporary directory, run through the real CLI
// with `--root`, so the test exercises the same code path the guard workflow uses.
//
// The cases are deliberately paired: for each way of writing a `sorry` that must be
// caught there is one that must be ignored (comment, string, cartouche).  A counter
// that cannot tell them apart is either blind or noisy, and both are useless.
//
// Exit status: 0 all cases passed, 1 at least one failed.

'use strict';

const fs = require('fs');
const os = require('os');
const path = require('path');
const { execFileSync } = require('child_process');

const SCRIPT = path.join(__dirname, 'count-obligations.cjs');
const ROOT = fs.mkdtempSync(path.join(os.tmpdir(), 'vwz-count-test-'));

const LEDGER_PATH = 'aligned/VWZ_ObligationsAligned.thy';
const ledger = (body) => [
  'theory VWZ_ObligationsAligned',
  'imports Main',
  'begin',
  '',
  'section \\<open>T0 -- rewriting\\<close>',
  '',
  body,
  '',
  'end'
].join('\n');

let failures = 0;
let run = 0;

function caseDir(name) {
  const dir = path.join(ROOT, name.replace(/[^a-z0-9]+/gi, '-'));
  fs.mkdirSync(dir, { recursive: true });
  return dir;
}

function write(dir, rel, content) {
  const p = path.join(dir, rel);
  fs.mkdirSync(path.dirname(p), { recursive: true });
  fs.writeFileSync(p, content, 'utf8');
}

function runCounter(dir, extra = []) {
  try {
    const stdout = execFileSync(process.execPath, [SCRIPT, '--root', dir].concat(extra), {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe']
    });
    return { code: 0, stdout };
  } catch (e) {
    // The CLI reports some failures on stderr (a missing ledger, a bad --root);
    // assertions should see both streams.
    return {
      code: e.status === undefined ? -1 : e.status,
      stdout: String(e.stdout || '') + String(e.stderr || '')
    };
  }
}

function check(name, dir, expect) {
  run++;
  const r = runCounter(dir, expect.args || []);
  const problems = [];
  if (r.code !== expect.code) problems.push('exit ' + r.code + ' != ' + expect.code);
  for (const s of expect.has || []) if (!r.stdout.includes(s)) problems.push('missing: ' + s);
  for (const s of expect.hasNot || []) if (r.stdout.includes(s)) problems.push('unexpected: ' + s);
  if (problems.length) {
    failures++;
    console.log('FAIL ' + name);
    for (const p of problems) console.log('     ' + p);
    console.log('     --- output ---');
    console.log(r.stdout.split('\n').map((l) => '     | ' + l).join('\n'));
  } else {
    console.log('PASS ' + name);
  }
}

// 1. A whole-line sorry in the ledger is the happy path.
{
  const d = caseDir('ledger-whole-line');
  write(d, LEDGER_PATH, ledger('lemma a: "P" \u2039proof\u203a\nsorry\n'));
  check('ledger whole-line sorry is counted as an obligation', d, {
    code: 0,
    has: ['ledger: 1, scaffolding: 0, outside: 0', 'OK: every sorry proof step is an obligation'],
    hasNot: ['FAIL:']
  });
}

// 2. An inline sorry in the ledger is still an obligation (this used to be invisible).
{
  const d = caseDir('ledger-inline');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  check('ledger inline sorry is counted as an obligation', d, {
    code: 0,
    has: ['1 lemmas,  1 sorry', 'ledger: 1, scaffolding: 0, outside: 0'],
    hasNot: ['FAIL:']
  });
}

// 3. A whole-line sorry outside the ledger must fail.
{
  const d = caseDir('outside-whole-line');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  write(d, 'aligned/Other.thy', 'theory Other\nimports Main\nbegin\nlemma b: "Q"\nsorry\nend\n');
  check('whole-line sorry outside the ledger fails', d, {
    code: 1,
    has: ['outside: 1', 'aligned/Other.thy:5', 'FAIL:'],
    hasNot: ['OK: every sorry proof step']
  });
}

// 4. The A6 blind spot: an inline sorry outside the ledger must fail too.
{
  const d = caseDir('outside-inline');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  write(d, 'aligned/Other.thy', 'theory Other\nimports Main\nbegin\nlemma b: "Q" sorry\nend\n');
  check('inline sorry outside the ledger fails (A6)', d, {
    code: 1,
    has: ['outside: 1', 'aligned/Other.thy:4  (inline)', 'FAIL:'],
    hasNot: ['OK: every sorry proof step']
  });
}

// 5. Comments are not proof steps, including nested ones.
{
  const d = caseDir('comments');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  write(d, 'aligned/Notes.thy', [
    'theory Notes',
    'imports Main',
    'begin',
    '(* lemma b: "Q" sorry *)',
    '(* outer (* inner sorry *) still a comment *)',
    'lemma c: "R"',
    '\u2039proof\u203a',
    '\u2039qed\u203a',
    'end'
  ].join('\n'));
  check('sorry inside comments is not a proof step', d, {
    code: 0,
    has: ['outside: 0', 'raw "sorry" tokens'],
    hasNot: ['FAIL:']
  });
}

// 6. Prose carried by a cartouche is not a proof step, whether in `text` or `\<comment>`.
{
  const d = caseDir('cartouche');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  write(d, 'aligned/Notes.thy', [
    'theory Notes',
    'imports Main',
    'begin',
    'text \\<open>we leave this as sorry for now\\<close>',
    'lemma c: "R"',
    '  \\<comment> \\<open>the inner bound is checked elsewhere, not sorry\\<close>',
    '  \\<proof\\>',
    '  \\<qed\\>',
    'end'
  ].join('\n'));
  check('sorry inside a cartouche is not a proof step', d, {
    code: 0,
    has: ['outside: 0'],
    hasNot: ['FAIL:']
  });
}

// 7. The scaffolding directory is reported, counted, and does not fail the build.
{
  const d = caseDir('scaffolding');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  write(d, 'skeleton/Smoke.thy', 'theory Smoke\nimports Main\nbegin\nlemma s1: "A" sorry\nlemma s2: "B" sorry\nend\n');
  check('scaffolding is counted separately and does not fail', d, {
    code: 0,
    args: ['--list-scaffolding'],
    has: ['ledger: 1, scaffolding: 2, outside: 0', 'declared scaffolding (not a failure)', 'skeleton/Smoke.thy:4  (inline)'],
    hasNot: ['FAIL:']
  });
}

// 7b. Without the flag the per-line dump stays out, but the count is still named.
{
  const d = caseDir('scaffolding-quiet');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  write(d, 'skeleton/Smoke.thy', 'theory Smoke\nimports Main\nbegin\nlemma s1: "A" sorry\nlemma s2: "B" sorry\nend\n');
  check('scaffolding detail is opt-in', d, {
    code: 0,
    has: ['scaffolding: 2'],
    hasNot: ['declared scaffolding (not a failure)', 'skeleton/Smoke.thy:4']
  });
}

// 8. CRLF files are handled, and the reported line number is the real one.
{
  const d = caseDir('crlf');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  write(d, 'aligned/Crlf.thy', 'theory Crlf\r\nimports Main\r\nbegin\r\nlemma b: "Q" sorry\r\nend\r\n');
  check('CRLF inline sorry is detected at the right line', d, {
    code: 1,
    has: ['aligned/Crlf.thy:4  (inline)'],
    hasNot: ['OK:']
  });
}

// 9. A string literal is not a proof step (a term may mention the word).
{
  const d = caseDir('string-literal');
  write(d, LEDGER_PATH, ledger('lemma a: "P" sorry\n'));
  write(d, 'aligned/Quoted.thy', [
    'theory Quoted',
    'imports Main',
    'begin',
    'definition msg where "msg = (STR \'\'sorry\'\')"',
    'end'
  ].join('\n'));
  check('sorry inside a string literal is not a proof step', d, {
    code: 0,
    has: ['outside: 0'],
    hasNot: ['FAIL:']
  });
}

// 10. Missing ledger is a distinct failure, not a silent pass.
{
  const d = caseDir('missing-ledger');
  write(d, 'aligned/Other.thy', 'theory Other\nimports Main\nbegin\nend\n');
  check('missing ledger exits 2', d, { code: 2, has: ['ledger not found'] });
}

console.log('\n' + (run - failures) + '/' + run + ' cases passed');
if (failures) {
  console.log('FAILED');
  process.exit(1);
}
console.log('OK: the counter distinguishes proof steps from prose');
