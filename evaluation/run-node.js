// Runs one CertiRocq benchmark binary under Node and prints its timings.
//
// Trimmed copy of
// https://github.com/womeier/certicoqwasm-testing/blob/master/evaluation/run-node.js
// The backwards-compatibility paths for older CertiCoq-wasm binaries are
// dropped: every binary in before/ and after/ exports `result`, `mem_ptr`,
// `out_of_mem` and `memory`, and none of them imports anything.
//
// Usage: node run-node.js before demo1

import { print_i63, print_bool, print_nat_sexp, print_list_sexp, print_option,
         print_prod, print_N_sexp, print_Z_sexp, print_compcert_byte_sexp } from './pp.js';

import * as fs from 'fs';
import * as path from 'path';

const pp_map = {
    "demo1": (val, dataView) => print_list_sexp(val, dataView, print_bool),
    "demo2": (val, dataView) => print_list_sexp(val, dataView, print_bool),
    "list_sum": print_nat_sexp,
    "vs_easy": print_bool,
    "vs_hard": print_bool,
    "binom": print_nat_sexp,
    "color": (val, dataView) => print_prod(val, dataView, print_Z_sexp, print_Z_sexp),
    "sha_fast": (val, dataView) => print_list_sexp(val, dataView, print_compcert_byte_sexp),
    "ack_3_9": print_nat_sexp,
    "even_10000": print_bool,
    "sm_gauss_nat": (val, dataView) => print_option(val, dataView, print_nat_sexp),
    "sm_gauss_N": (val, dataView) => print_option(val, dataView, print_N_sexp),
    "sm_gauss_PrimInt": (val, dataView) => print_option(val, dataView, print_i63),
};

const args = process.argv.slice(2);
if (args.length != 2) {
    console.log("Expected two args: 0: folder containing the wasm file (before|after), 1: program.");
    console.log("e.g.: $ node run-node.js before vs_easy");
    process.exit(1);
}
const folder = args[0];
const program = args[1];

const fn_pp = pp_map[program];
if (fn_pp == undefined) {
    console.log(`Please specify a pp function for ${program} in run-node.js.`);
    process.exit(1);
}

const wasm_path = path.join(folder, `CertiRocq.Benchmarks.wasm.tests.${program}.wasm`);

(async () => {
    const start_startup = Date.now();
    const bytes = fs.readFileSync(wasm_path);
    const obj = await WebAssembly.instantiate(new Uint8Array(bytes), { env: {} });
    const time_startup = Date.now() - start_startup;

    try {
        const start_main = Date.now();
        obj.instance.exports.main_function();
        const time_main = Date.now() - start_main;

        if (obj.instance.exports.out_of_mem.value == 1) {
            console.log(`Ran out of memory running ${wasm_path}.`);
            process.exit(1);
        }

        const bytes_used = obj.instance.exports.mem_ptr.value;
        const dataView = new DataView(obj.instance.exports.memory.buffer);
        const res_value = obj.instance.exports.result.value;

        process.stdout.write("====> ");
        const start_pp = Date.now();
        fn_pp(res_value, dataView);
        const time_pp = Date.now() - start_pp;

        console.log(`\nBenchmark ${wasm_path}: {{"time_startup": "${time_startup}", "time_main": "${time_main}", "time_pp": "${time_pp}", "bytes_used": "${bytes_used}", "program": "${program}"}} ms, bytes.`);
    } catch (error) {
        console.log(error);
        process.exit(1);
    }
})();
