#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
//
// count-obligations.cjs -- the counter cited by the paper.
//
// Reports two things and keeps them separate on purpose:
//
//   * the obligation ledger, tier by tier (parsed from the `section` headings of
//     aligned/VWZ_ObligationsAligned.thy);
//   * repository totals across every .thy file (lemmas, theorems, sorry steps,
//     file count and bytes).
//
// What counts as a `sorry` proof step
//   A `sorry` token in *code* position, whether it is a line of its own or sits at
//   the end of a statement (`lemma x: "P" sorry`).  Occurrences inside comments
//   (`(* ... *)`, nested), inside strings, or inside cartouches (`\<open> ... \<close>`,
//   which is how `text` and `\<comment>` carry prose) are not proof steps; the raw
//   token count is reported separately so the two numbers cannot be confused.
//
// Three places a proof step can be, and they are not the same thing:
//   ledger        aligned/VWZ_ObligationsAligned.thy -- the obligations the paper counts
//   scaffolding   skeleton/ -- deliberately unproved statements used as a toolchain smoke test
//   outside       everywhere else -- an error
//
// Exit status
//   0  no `sorry` outside the ledger and the declared scaffolding directory
//   1  a `sorry` proof step was found outside them
//   2  the ledger file is missing
//
// Usage: node tools/count-obligations.cjs [--root <dir>] [--list-scaffolding]

'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = (() => {
  const at = process.argv.indexOf('--root');
  if (at !== -1) {
    const v = process.argv[at + 1];
    if (!v) {
      console.error('--root needs a directory');
      process.exit(2);
    }
    return path.resolve(v);
  }
  return path.resolve(__dirname, '..');
})();

// The per-line scaffolding dump is opt-in: the summary already names the count, and 37
// lines of noise would bury the ledger when the output is pasted into a document.
const LIST_SCAFFOLDING = process.argv.includes('--list-scaffolding');

const LEDGER = path.join(ROOT, 'aligned', 'VWZ_ObligationsAligned.thy');
const SKIP_DIRS = new Set(['.git', 'heaps', 'node_modules']);
const SCAFFOLDING_DIRS = new Set(['skeleton']);

if (!fs.existsSync(LEDGER)) {
  console.error('ledger not found: ' + LEDGER);
  process.exit(2);
}

function theoryFiles(dir, acc = []) {
  for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
    if (SKIP_DIRS.has(ent.name)) continue;
    const p = path.join(dir, ent.name);
    if (ent.isDirectory()) theoryFiles(p, acc);
    else if (ent.name.endsWith('.thy')) acc.push(p);
  }
  return acc;
}

// Replace everything that is not code with spaces, preserving line breaks and the
// exact byte offsets, so that a match position still maps to the original line.
function maskNonCode(text) {
  const out = [];
  const n = text.length;
  let i = 0;
  let commentDepth = 0;
  let cartoucheDepth = 0;
  let inString = false;

  const blank = (ch) => out.push(ch === '\n' || ch === '\r' ? ch : ' ');
  const open = '\\<open>';
  const close = '\\<close>';

  while (i < n) {
    const ch = text[i];
    const two = text.slice(i, i + 2);

    if (commentDepth > 0) {
      if (two === '(*') { commentDepth++; blank(ch); blank(text[i + 1]); i += 2; continue; }
      if (two === '*)') { commentDepth--; blank(ch); blank(text[i + 1]); i += 2; continue; }
      blank(ch); i++; continue;
    }

    if (inString) {
      if (ch === '\\' && i + 1 < n) { blank(ch); blank(text[i + 1]); i += 2; continue; }
      if (ch === '"') { inString = false; blank(ch); i++; continue; }
      blank(ch); i++; continue;
    }

    if (cartoucheDepth > 0) {
      if (text.startsWith(open, i)) {
        cartoucheDepth++;
        for (let k = 0; k < open.length; k++) blank(text[i + k]);
        i += open.length;
        continue;
      }
      if (text.startsWith(close, i)) {
        cartoucheDepth--;
        for (let k = 0; k < close.length; k++) blank(text[i + k]);
        i += close.length;
        continue;
      }
      blank(ch); i++; continue;
    }

    if (two === '(*') { commentDepth = 1; blank(ch); blank(text[i + 1]); i += 2; continue; }
    if (ch === '"') { inString = true; blank(ch); i++; continue; }
    if (text.startsWith(open, i)) {
      cartoucheDepth = 1;
      for (let k = 0; k < open.length; k++) blank(text[i + k]);
      i += open.length;
      continue;
    }
    out.push(ch); i++;
  }

  return out.join('');
}

const isLemma = (line) => /^lemma\s/.test(line.trim());
const isTheorem = (line) => /^theorem\s/.test(line.trim());
const sorryTokens = (line) => line.match(/\bsorry\b/g) || [];

const categoryOf = (file) => {
  const rel = path.relative(ROOT, file).replace(/\\/g, '/');
  if (path.resolve(file) === path.resolve(LEDGER)) return 'ledger';
  const top = rel.split('/')[0];
  if (SCAFFOLDING_DIRS.has(top)) return 'scaffolding';
  return 'outside';
};

// ---- ledger, tier by tier -------------------------------------------------
const ledgerText = fs.readFileSync(LEDGER, 'utf8');
const ledgerMasked = maskNonCode(ledgerText);
const tiers = {};
let current = '[prelude]';
const ledgerLines = ledgerMasked.split(/\r?\n/);
const rawLedgerLines = ledgerText.split(/\r?\n/);
for (let i = 0; i < ledgerLines.length; i++) {
  const line = ledgerLines[i];
  const m = rawLedgerLines[i].match(/^section \\<open>([^\\]*)/);
  if (m) current = m[1].trim();
  tiers[current] = tiers[current] || { lemmas: 0, sorry: 0 };
  if (isLemma(line)) tiers[current].lemmas++;
  tiers[current].sorry += sorryTokens(line).length;
}

let ledgerLemmas = 0;
let ledgerSorry = 0;
for (const k of Object.keys(tiers)) {
  ledgerLemmas += tiers[k].lemmas;
  ledgerSorry += tiers[k].sorry;
}

// ---- repository totals ----------------------------------------------------
let files = 0, bytes = 0, lemmas = 0, theorems = 0, rawSorry = 0;
const proofSteps = { ledger: 0, scaffolding: 0, outside: 0 };
const detail = { scaffolding: [], outside: [] };

for (const f of theoryFiles(ROOT).sort()) {
  const text = fs.readFileSync(f, 'utf8');
  files++;
  bytes += Buffer.byteLength(text);
  rawSorry += (text.match(/\bsorry\b/g) || []).length;

  const category = categoryOf(f);
  const rel = path.relative(ROOT, f).replace(/\\/g, '/');
  const lines = maskNonCode(text).split(/\r?\n/);
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (isLemma(line)) lemmas++;
    if (isTheorem(line)) theorems++;
    const hits = sorryTokens(line).length;
    if (!hits) continue;
    proofSteps[category] += hits;
    if (category === 'outside' || category === 'scaffolding') {
      const rest = line.replace(/\bsorry\b/g, '').trim();
      const where = rel + ':' + (i + 1) + (rest ? '  (inline)' : '');
      detail[category].push(where + (hits > 1 ? '  x' + hits : ''));
    }
  }
}

const totalSteps = proofSteps.ledger + proofSteps.scaffolding + proofSteps.outside;

// ---- report ---------------------------------------------------------------
console.log('=== obligation ledger ===');
for (const k of Object.keys(tiers)) {
  if (!tiers[k].lemmas) continue;
  console.log('  ' + k.padEnd(56) + String(tiers[k].lemmas).padStart(3) + ' lemmas, '
    + String(tiers[k].sorry).padStart(2) + ' sorry');
}
console.log('  ' + 'TOTAL'.padEnd(56) + String(ledgerLemmas).padStart(3) + ' lemmas, '
  + String(ledgerSorry).padStart(2) + ' sorry');

console.log('\n=== repository totals ===');
console.log('  theory files          ' + files);
console.log('  bytes                 ' + bytes);
console.log('  lemmas                ' + lemmas);
console.log('  theorems              ' + theorems);
console.log('  sorry proof steps     ' + totalSteps + '  (ledger: ' + proofSteps.ledger
  + ', scaffolding: ' + proofSteps.scaffolding + ', outside: ' + proofSteps.outside + ')');
console.log('  raw "sorry" tokens    ' + rawSorry + '  (includes prose and comments)');

if (proofSteps.scaffolding && LIST_SCAFFOLDING) {
  console.log('\n=== declared scaffolding (not a failure) ===');
  for (const s of detail.scaffolding) console.log('  ' + s);
}

if (proofSteps.outside) {
  console.log('\n=== sorry outside the ledger ===');
  for (const s of detail.outside) console.log('  ' + s);
  console.log('\nFAIL: a proof step is sorry outside the obligation ledger and the scaffolding directory.');
  process.exit(1);
}

if (lemmas !== ledgerLemmas) {
  console.log('\nnote: repository lemmas (' + lemmas + ') differ from ledger lemmas ('
    + ledgerLemmas + '); the difference is supporting infrastructure (auxiliary library,');
  console.log('      field definitions, elementary row operations, smoke and negative sessions).');
}

console.log('\nOK: every sorry proof step is an obligation in the ledger or declared scaffolding.');
