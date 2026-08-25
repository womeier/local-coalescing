// Compare exports.f(arg) between two modules for a few arguments.
import * as fs from 'fs';
const run = async (file, arg) => {
  const o = await WebAssembly.instantiate(new Uint8Array(fs.readFileSync(file)), { env: {} });
  return o.instance.exports.f(arg);
};
let bad = 0;
for (const arg of [0, 1, 2]) {
  const a = await run(process.argv[2], arg), b = await run(process.argv[3], arg);
  if (a !== b) { console.log(`  arg=${arg}: original=${a} optimized=${b}  MISMATCH`); bad++; }
}
if (bad) { console.log(`FAILED (${bad})`); process.exit(1); }
console.log(`  ${process.argv[2]}: behaviour identical`);
