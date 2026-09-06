#!/usr/bin/env python3
#
# Benchmarks the binaries in before/ against the ones in after/, i.e. the
# CertiRocq benchmarks before and after local coalescing (see local_coalesce.py,
# which produces after/ from before/).
#
# This is a trimmed copy of
# https://github.com/womeier/certicoqwasm-testing/blob/master/evaluation/benchmark.py
# -- refer to that file for the full version.
# Usage: python3 benchmark.py [--runs N] [--memory-usage] [--binary-size]

import json
import os
import pathlib
import subprocess

import click

CWD = os.path.abspath(os.path.dirname(__file__))
os.chdir(CWD)

NODE = "node"
FOLDERS = ["before", "after"]
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


def comparison_table(all_results, memory_usage, binary_size):
    """before vs. after, per program: run time, and optionally memory and size."""
    before, after = all_results["before"], all_results["after"]

    columns = [("sum", "run time (ms)")]
    if memory_usage:
        columns.append(("bytes_used", "memory (KB)"))
    if binary_size:
        columns.append(("binary_size_in_kb", "bin size (KB)"))

    width = max(map(len, programs))
    for key, label in columns:
        print(f"\n{label}:")
        print(f"{'':>{width}}   {'before':>8} {'after':>8} {'change':>8}")
        for program in programs:
            if program not in before or program not in after:
                continue
            b, a = before[program][key], after[program][key]
            if isinstance(b, int) and isinstance(a, int) and b != 0:
                change = f"{100 * (a - b) / b:+.1f}%"
            else:
                change = "N/A"
            print(f"{program:>{width}} : {b:>8} {a:>8} {change:>8}")


@click.command()
@click.option("--runs", type=int, help="Number of runs.", default=10)
@click.option(
    "--memory-usage", is_flag=True, help="Print linear memory usage.", default=False
)
@click.option("--binary-size", is_flag=True, help="Print binary size.", default=False)
@click.option("--verbose", is_flag=True, help="Print debug information.", default=False)
def measure(runs, memory_usage, binary_size, verbose):
    if runs <= 0:
        print("Expected at least one run.")
        exit(1)

    all_results = dict()

    for f in FOLDERS:
        f_name = pathlib.PurePath(f).name
        print(
            f"Running {f_name} (local coalescing {'applied' if f_name == 'after' else 'not applied'}), "
            f"avg. of {runs} runs with {get_engine_version()}."
        )

        folder_results = dict()
        for program in programs:
            path = wasm_path(f, program)

            if not os.path.exists(path):
                print(f"Didn't find {path}, skipping.")
                continue

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

    comparison_table(all_results, memory_usage, binary_size)
    print("")


if __name__ == "__main__":
    measure()
