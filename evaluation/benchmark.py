#!/usr/bin/env python3
#
# Benchmarks the binaries in before/ against the ones in after/, i.e. the
# CertiRocq benchmarks before and after local coalescing (see local_coalesce.py,
# which produces after/ from before/).  The two references it is measured
# against are binaryen: before/ run through `wasm-opt -O2` and through
# `wasm-opt --coalesce-locals`, the latter being binaryen's version of the very
# optimization this pass implements.  Both are generated on demand into
# before-O2/ and before-cl/, so the table compares
#
#   before | before-O2 | before-cl | after
#
# --after-o2 adds a fifth column, after/ run through -O2, i.e. the pass used as
# a prepass to binaryen rather than as a replacement for part of it.
#
# This is a trimmed copy of
# https://github.com/womeier/certicoqwasm-testing/blob/master/evaluation/benchmark.py
# -- refer to that file for the full version.
# Usage: python3 benchmark.py [--runs N] [--warmup N] [--memory-usage]
#                            [--binary-size] [--no-wasm-opt] [--after-o2]
#                            [--json FILE]

import json
import os
import pathlib
import shutil
import subprocess

import click

CWD = os.path.abspath(os.path.dirname(__file__))
os.chdir(CWD)

NODE = "node"
WASM_OPT = "wasm-opt"
BEFORE = "before"
AFTER = "after"
BEFORE_O2 = "before-O2"
BEFORE_CL = "before-cl"
AFTER_O2 = "after-O2"

# (folder, how it is generated, description).  The second field is None for the
# two folders that are checked in, and (source folder, wasm-opt flags) for the
# ones built on demand by running wasm-opt over another folder.  Order here is
# the column order of the results table.  after-O2/ is off unless --after-o2.
VARIANTS = [
    (BEFORE, None, "local coalescing not applied"),
    (BEFORE_O2, (BEFORE, ["-O2"]), "wasm-opt -O2 applied to before/"),
    (BEFORE_CL, (BEFORE, ["--coalesce-locals"]), "wasm-opt --coalesce-locals on before/"),
    (AFTER, None, "local coalescing applied"),
    (AFTER_O2, (AFTER, ["-O2"]), "local coalescing, then wasm-opt -O2"),
]

measurements = ["time_startup", "time_main", "time_pp", "bytes_used"]

programs = [
    "demo1",
    "demo2",
    "list_sum",
    "vs_easy",
    "vs_hard",
    "binom",
    "color",
    "sha_fast",
    "even_10000",
    "ack_3_9",
    "sm_gauss_nat",
    "sm_gauss_N",
    "sm_gauss_PrimInt",
]


def wasm_path(folder, program):
    return os.path.join(folder, f"CertiRocq.Benchmarks.wasm.tests.{program}.wasm")


def get_engine_version():
    r = subprocess.run([NODE, "--version"], capture_output=True)
    return f"Node.js ({r.stdout.decode('ascii').strip()})"


def build_wasm_opt_binaries(source, folder, args):
    """Run `wasm-opt args` over source/ into folder/, skipping up-to-date outputs."""
    os.makedirs(folder, exist_ok=True)
    for program in programs:
        src = wasm_path(source, program)
        dst = wasm_path(folder, program)

        if not os.path.exists(src):
            continue
        if os.path.exists(dst) and os.stat(dst).st_mtime >= os.stat(src).st_mtime:
            continue

        # --all-features because CertiCoq emits return_call_indirect, which
        # wasm-opt rejects at validation unless tail calls are enabled.
        r = subprocess.run(
            [WASM_OPT, "--all-features", *args, src, "-o", dst], capture_output=True
        )
        if r.returncode != 0:
            print(f"{WASM_OPT} failed on {src}: {r.stderr.decode(errors='replace')}")
            exit(1)


def comparison_table(all_results, folders, baselines, memory_usage, binary_size):
    """Per program: run time of every variant, and optionally memory and size.

    folders[0] is the leftmost column; every other one also gets a change
    column, against the folder baselines maps it to -- the folder wasm-opt was
    run on for the generated ones, before/ for the rest.
    """
    first, others = folders[0], folders[1:]

    columns = [("time_main", "main time (ms)")]
    if memory_usage:
        columns.append(("bytes_used", "memory (KB)"))
    if binary_size:
        columns.append(("binary_size_in_kb", "bin size (KB)"))

    width = max(map(len, programs))
    col = max([8] + [len(f) for f in folders])
    chg = max([8] + [len(f"vs {baselines[f]}") for f in others])

    for key, label in columns:
        print(f"\n{label}:")
        header = f"{'':>{width}}   {first:>{col}}"
        for f in others:
            header += f" {f:>{col}} {f'vs {baselines[f]}':>{chg}}"
        print(header)

        for program in programs:
            if any(program not in all_results[f] for f in folders):
                continue

            row = f"{program:>{width}} : {all_results[first][program][key]:>{col}}"
            for f in others:
                a = all_results[f][program][key]
                b = all_results[baselines[f]][program][key]
                if isinstance(b, int) and isinstance(a, int) and b != 0:
                    change = f"{100 * (a - b) / b:+.1f}%"
                else:
                    change = "N/A"
                row += f" {a:>{col}} {change:>{chg}}"
            print(row)


def single_run_node(folder, program, verbose):
    r = subprocess.run([NODE, "./run-node.js", folder, program], capture_output=True)

    if r.returncode != 0:
        print(
            f"Running {wasm_path(folder, program)} returned non-0 returncode, stderr: {r.stderr}"
        )
        exit(1)

    if verbose:
        print("STDOUT: " + r.stdout.decode("ascii"))
        print("STDERR: " + r.stderr.decode("ascii"))

    res = "{" + r.stdout.decode("ascii").split("{{")[1].split("}}")[0] + "}"
    return json.loads(res)


@click.command()
@click.option("--runs", type=int, help="Number of runs.", default=10)
@click.option(
    "--warmup",
    type=int,
    default=3,
    show_default=True,
    help="Discarded runs before the measured ones, per program.",
)
@click.option(
    "--memory-usage", is_flag=True, help="Print linear memory usage.", default=False
)
@click.option("--binary-size", is_flag=True, help="Print binary size.", default=False)
@click.option(
    "--wasm-opt/--no-wasm-opt",
    default=True,
    show_default=True,
    help="Also benchmark the binaryen reference variants (before-O2, before-cl).",
)
@click.option(
    "--after-o2",
    is_flag=True,
    default=False,
    help="Add a column for after/ run through `wasm-opt -O2`.",
)
@click.option(
    "--json",
    "json_path",
    type=click.Path(),
    default=None,
    help="Write the measurements to this file, for figure.typ to plot.",
)
@click.option("--verbose", is_flag=True, help="Print debug information.", default=False)
def measure(
    runs, warmup, memory_usage, binary_size, wasm_opt, after_o2, json_path, verbose
):
    if runs <= 0:
        print("Expected at least one run.")
        exit(1)

    if warmup < 0:
        print("Expected a non-negative number of warmup runs.")
        exit(1)

    if wasm_opt and shutil.which(WASM_OPT) is None:
        print(f"Didn't find {WASM_OPT} on PATH, skipping the binaryen variants.\n")
        wasm_opt = False

    variants = [
        (f, gen, desc)
        for f, gen, desc in VARIANTS
        if (wasm_opt or gen is None) and (after_o2 or f != AFTER_O2)
    ]
    for folder, generated_from, _ in variants:
        if generated_from is not None:
            source, args = generated_from
            build_wasm_opt_binaries(source, folder, args)

    all_results = dict()

    for f, _, description in variants:
        f_name = pathlib.PurePath(f).name
        print(
            f"Running {f_name} ({description}), "
            f"avg. of {runs} runs with {get_engine_version()}"
            + (f", after {warmup} warmup runs." if warmup else ".")
        )

        folder_results = dict()
        for program in programs:
            path = wasm_path(f, program)

            if not os.path.exists(path):
                print(f"Didn't find {path}, skipping.")
                continue

            # Each run is a fresh node process, so this doesn't warm a JIT --
            # it warms the page cache for the binary and lets the CPU clock
            # settle, which is what the first run of a program otherwise pays.
            for _ in range(warmup):
                single_run_node(f, program, verbose)

            values = []
            for run in range(runs):
                values.append(single_run_node(f, program, verbose))

            result = {meas: list() for meas in measurements}
            for val in values:
                for meas in measurements:
                    if meas == "bytes_used" and val[meas] is None:
                        result[meas].append(None)
                    else:
                        result[meas].append(int(val[meas]))

            time_startup = round(
                sum(result["time_startup"]) / len(result["time_startup"])
            )
            time_main = round(sum(result["time_main"]) / len(result["time_main"]))
            time_pp = round(sum(result["time_pp"]) / len(result["time_pp"]))

            memory_in_kb = (
                int(result["bytes_used"][0] / 1000)
                if result["bytes_used"][0] is not None
                else "N/A"
            )
            binary_size_in_kb = int(os.stat(path).st_size / 1000)

            folder_results[program] = {
                "time_startup": time_startup,
                "time_main": time_main,
                "time_pp": time_pp,
                "sum": time_startup + time_main,
                "bytes_used": memory_in_kb,
                "binary_size_in_kb": binary_size_in_kb,
            }

            # count spaces instead of using \t
            program_pp = (max(map(len, programs)) - len(program)) * " " + program

            print(
                f"{program_pp} : "
                f"startup: {time_startup:>4}, main: {time_main:>3}, sum: {time_startup + time_main:>4}"
                f" (pp: {time_pp:>2}, sum_total: {time_startup + time_main + time_pp:>4})"
                + (f", memory used: {memory_in_kb} KB" if memory_usage else "")
                + (f", bin size: {binary_size_in_kb:>4} KB" if binary_size else "")
            )

        all_results[f_name] = folder_results
        print("")

    # Every variant is compared against the binaries it was produced from:
    # before/ for after/, and the folder wasm-opt ran on for the generated ones.
    baselines = {
        f: (gen[0] if gen else BEFORE) for f, gen, _ in variants if f != BEFORE
    }
    comparison_table(
        all_results, [f for f, _, _ in variants], baselines, memory_usage, binary_size
    )
    print("")

    if json_path is not None:
        with open(json_path, "w") as f:
            json.dump(
                {
                    "engine": get_engine_version(),
                    "runs": runs,
                    "warmup": warmup,
                    "programs": [p for p in programs if p in all_results[BEFORE]],
                    "variants": [
                        {"folder": folder, "description": desc}
                        for folder, _, desc in variants
                    ],
                    "results": all_results,
                },
                f,
                indent=2,
            )
        print(f"Wrote {json_path}.\n")


if __name__ == "__main__":
    measure()
