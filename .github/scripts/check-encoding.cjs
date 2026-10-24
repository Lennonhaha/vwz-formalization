#!/usr/bin/env node
// Byte-level guard for the tracked text files: no BOM, no U+FFFD, no NUL,
// no private-use characters. Encoding drift is invisible in a diff, so it is
// checked instead of reviewed.
//
// The private-use range catches the residue of a lossy GBK <-> UTF-8 round trip:
// those lines carry no U+FFFD, so the replacement-character check alone misses them.
//
// Exit status: 0 clean, 1 defects found, 2 nothing scanned (a vacuous pass is an error).
const { execSync } = require('child_process');
const fs = require('fs');

const TEXT = /\.(md|txt|tex|thy|cff|yml|yaml|json|cjs|js|sh|gitignore|html)$/i;
const SKIP = /^(paper\/main-zh\.pdf|docs\/main-zh\.pdf)$/;
const PUA = /[\uE000-\uF8FF]/;

const files = execSync('git ls-files', { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 })
  .split('\n').map(f => f.trim()).filter(Boolean)
  .filter(f => !SKIP.test(f))
  .filter(f => TEXT.test(f) || f === '.gitignore');

if (files.length === 0) {
  console.log('FAIL: nothing scanned -- refusing to report a vacuous pass');
  process.exit(2);
}

const problems = [];
for (const f of files) {
  let buf;
  try { buf = fs.readFileSync(f); } catch { continue; }
  if (buf.length >= 3 && buf[0] === 0xEF && buf[1] === 0xBB && buf[2] === 0xBF) problems.push(f + ': UTF-8 BOM');
  if (buf.includes(0x00)) problems.push(f + ': NUL byte');
  const s = buf.toString('utf8');
  const bad = (s.match(/\uFFFD/g) || []).length;
  if (bad) problems.push(f + ': ' + bad + ' x U+FFFD');
  const pua = s.match(PUA);
  if (pua) problems.push(f + ': private-use character U+' + pua[0].codePointAt(0).toString(16).toUpperCase());
}

console.log('checked ' + files.length + ' tracked text files');
if (problems.length) {
  for (const p of problems) console.log('  ' + p);
  console.log('FAIL: encoding problems found');
  process.exit(1);
}
console.log('OK: no BOM, no NUL, no U+FFFD, no private-use characters');
