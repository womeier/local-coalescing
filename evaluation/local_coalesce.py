#!/usr/bin/env python3
import subprocess
from pathlib import Path

import click
from tqdm import tqdm

BEFORE = Path(__file__).resolve().parent / "before"
AFTER = Path(__file__).resolve().parent / "after"
TOOL = "result/bin/wasm-opt-cert"


@click.command()
@click.option(
    "--tool",
    default=TOOL,
    show_default=True,
    help="Path to the wasm-opt-cert executable.",
)
@click.option(
    "--before",
    type=click.Path(path_type=Path),
    default=BEFORE,
    show_default=True,
    help="Directory containing the input binaries.",
)
@click.option(
    "--after",
    type=click.Path(path_type=Path),
    default=AFTER,
    show_default=True,
    help="Directory to write the optimized binaries to.",
)
def main(tool: str, before: Path, after: Path) -> None:
    """Apply local coalescing to the binaries in before/ and save them in after/."""
    after.mkdir(parents=True, exist_ok=True)

    print("The following is quite slow. TODO make faster.")
    inputs = sorted(
        (p for p in before.iterdir() if p.suffix == ".wasm"),
        key=lambda p: p.stat().st_size,
    )
    for src in tqdm(inputs, desc="Local coalescing", unit="file"):
        dst = after / src.name
        subprocess.run([tool, str(src), str(dst)], check=True)


if __name__ == "__main__":
    main()
