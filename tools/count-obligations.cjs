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
// Exit status
//   0  no `sorry` outside the ledger
//   1  a `sorry` proof step was found outside the ledger
//   2  the ledger file is missing
//
// A `sorry` step is a line whose trimmed content is exactly `sorry`, optionally
// followed by a trailing `(* ... *)` comment.  Occurrences of the word inside
// prose or inside comments are NOT counted: the raw token count is reported
// separately so that the two numbers cannot be confused.

'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const LEDGER = path.join(ROOT, 'aligned', 'VWZ_ObligationsAligned.thy');
const SKIP_DIRS = new Set(['.git', 'heaps', 'node_modules']);

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

const isSorryStep = (line) => /^sorry\s*(\(\*.*\*\))?\s*$/.test(line.trim());
const isLemma = (line) => /^lemma\s/.test(line.trim());
const isTheorem = (line) => /^theorem\s/.test(line.trim());

// ---- ledger, tier by tier -------------------------------------------------
const ledgerText = fs.readFileSync(LEDGER, 'utf8');
const tiers = {};
let current = '[prelude]';
for (const line of ledgerText.split(/\r?\n/)) {
  const m = line.match(/^section \\<open>([^\\]*)/);
  if (m) current = m[1].trim();
  tiers[current] = tiers[current] || { lemmas: 0, sorry: 0 };
  if (isLemma(line)) tiers[current].lemmas++;
  if (isSorryStep(line)) tiers[current].sorry++;
}

let ledgerLemmas = 0;
let ledgerSorry = 0;
for (const k of Object.keys(tiers)) {
  ledgerLemmas += tiers[k].lemmas;
  ledgerSorry += tiers[k].sorry;
}

// ---- repository totals ----------------------------------------------------
let files = 0, bytes = 0, lemmas = 0, theorems = 0, sorry = 0, rawSorry = 0;
let sorryOutside = [];

for (const f of theoryFiles(ROOT).sort()) {
  const text = fs.readFileSync(f, 'utf8');
  files++;
  bytes += Buffer.byteLength(text);
  rawSorry += (text.match(/\bsorry\b/g) || []).length;
  let lineNo = 0;
  for (const line of text.split(/\r?\n/)) {
    lineNo++;
    if (isLemma(line)) lemmas++;
    if (isTheorem(line)) theorems++;
    if (isSorryStep(line)) {
      sorry++;
      if (path.resolve(f) !== path.resolve(LEDGER)) {
        sorryOutside.push(path.relative(ROOT, f).replace(/\\/g, '/') + ':' + lineNo);
      }
    }
  }
}

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
console.log('  sorry proof steps     ' + sorry + '  (ledger: ' + ledgerSorry + ', outside: ' + sorryOutside.length + ')');
console.log('  raw "sorry" tokens    ' + rawSorry + '  (includes prose and comments)');

if (sorryOutside.length) {
  console.log('\n=== sorry outside the ledger ===');
  for (const s of sorryOutside) console.log('  ' + s);
  console.log('\nFAIL: a proof step is sorry outside the obligation ledger.');
  process.exit(1);
}

if (lemmas !== ledgerLemmas) {
  console.log('\nnote: repository lemmas (' + lemmas + ') differ from ledger lemmas ('
    + ledgerLemmas + '); the difference is supporting infrastructure (auxiliary library,');
  console.log('      field definitions, elementary row operations, smoke and negative sessions).');
}

console.log('\nOK: every sorry proof step is an obligation in the ledger.');
