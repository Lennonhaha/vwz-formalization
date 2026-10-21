#!/usr/bin/env node
// Byte-level guard for the tracked text files: no BOM, no U+FFFD, no NUL.
// Encoding drift is invisible in a diff, so it is checked instead of reviewed.
const { execSync } = require('child_process');
const fs = require('fs');

const TEXT = /\.(md|txt|tex|thy|cff|yml|yaml|json|cjs|js|sh|gitignore|html)$/i;
const SKIP = /^(paper\/main-zh\.pdf|docs\/main-zh\.pdf)$/;

const files = execSync('git ls-files', { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 })
  .split('\n').map(f => f.trim()).filter(Boolean)
  .filter(f => !SKIP.test(f))
  .filter(f => TEXT.test(f) || f === '.gitignore');

const problems = [];
for (const f of files) {
  let buf;
  try { buf = fs.readFileSync(f); } catch { continue; }
  if (buf.length >= 3 && buf[0] === 0xEF && buf[1] === 0xBB && buf[2] === 0xBF) problems.push(f + ': UTF-8 BOM');
  if (buf.includes(0x00)) problems.push(f + ': NUL byte');
  const s = buf.toString('utf8');
  const bad = (s.match(/\uFFFD/g) || []).length;
  if (bad) problems.push(f + ': ' + bad + ' x U+FFFD');
}

console.log('checked ' + files.length + ' tracked text files');
if (problems.length) {
  for (const p of problems) console.log('  ' + p);
  console.log('FAIL: encoding problems found');
  process.exit(1);
}
console.log('OK: no BOM, no NUL, no U+FFFD');
