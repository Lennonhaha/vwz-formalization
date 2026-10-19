const fs = require('fs');
const p = 'aligned/VWZ_ObligationsAligned.thy';
const lines = fs.readFileSync(p, 'utf8').split(/\r?\n/);
let cur = '[prelude]';
const sec = {};
function bump(k) { (sec[cur] = sec[cur] || { lemmas: 0, sorry: 0 })[k]++; }
for (const ln of lines) {
  const m = ln.match(/^section \\<open>([^\\]*)/);
  if (m) cur = m[1].trim();
  if (/^lemma /.test(ln)) bump('lemmas');
  if (/^\s*sorry\s*$/.test(ln)) bump('sorry');
}
let tl = 0, ts = 0;
for (const k in sec) { tl += sec[k].lemmas; ts += sec[k].sorry; }
console.log(JSON.stringify(sec, null, 1));
console.log('TOTAL lemmas =', tl, '| TOTAL sorry =', ts);
const raw = (fs.readFileSync(p, 'utf8').match(/\bsorry\b/g) || []).length;
console.log('raw sorry token count =', raw);
console.log('bytes =', Buffer.byteLength(fs.readFileSync(p)));
