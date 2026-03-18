#!/usr/bin/env python3

from dataclasses import dataclass
from argparse import Namespace
import argparse
import os
import shutil
import subprocess
from pathlib import Path

# Run in repo root
os.chdir(Path(__file__).parent.parent)


@dataclass
class Args(Namespace):
    force: bool
    nomeld: bool


parser = argparse.ArgumentParser(
    description="Interactively create, fix, and remove *.out.expected files "
    "based on their corresponding *.out.produced files."
)
parser.add_argument(
    "--force",
    "-f",
    action="store_true",
    help="automatically accept all suggested changes without user interaction",
)
parser.add_argument(
    "--nomeld",
    "-M",
    action="store_true",
    help="diff files instead of using meld to merge them",
)
args = parser.parse_args(namespace=Args)


use_meld = not args.nomeld
try:
    subprocess.run(["meld", "--version"], check=True, stdout=subprocess.DEVNULL)
except (subprocess.CalledProcessError, FileNotFoundError):
    print("meld not found, falling back to --nomeld behavior")
    use_meld = False


def prompt(message: str, options: str = "Yn") -> str:
    default: str | None = None
    for c in options:
        if c.isupper():
            default = c.lower()
            break

    options = options.lower()
    options_display = "/".join(c.upper() if c == default else c for c in options)

    if args.force and default:
        print(f"{message} [{options_display}]: selected {default} due to --force")
        return default

    while True:
        response = input(f"{message} [{options_display}]: ").strip().lower()
        if not response and default:
            return default
        elif response in options.lower():
            return response
        else:
            print(f"Please enter {options_display}.")


def remove_file(file: Path, reason: str) -> None:
    print()
    print()
    print(f"{reason} but {file} exists.")
    if prompt(f"Remove {file}?") == "y":
        file.unlink()


def compare_and_merge(
    produced_file: Path,
    expected_file: Path,
) -> None:
    produced = produced_file.read_bytes()
    expected = expected_file.read_bytes()

    if produced == expected:
        return

    print()
    print()
    print(f"{produced_file} differs from {expected_file}")

    if args.force:
        print(f"Automatically updating {expected_file} due to --force")
        shutil.copy(produced_file, expected_file)
        return

    if not use_meld:
        subprocess.run(
            [
                "diff",
                "-au",
                "--strip-trailing-cr",
                "--color=always",
                expected_file,
                produced_file,
            ]
        )
        if prompt(f"Apply diff to {expected_file}?") == "y":
            shutil.copy(produced_file, expected_file)
        return

    # This is the opposite direction of the tests' diff output, but meld puts
    # the cursor into the right file by default, and only saves the file with
    # the cursor when pressing Ctrl+S, so this order is more convenient for
    # quickly fixing many files.
    subprocess.run(["meld", produced_file, expected_file])


def create_or_ignore(
    produced_file: Path,
    expected_file: Path,
    ignored_file: Path,
) -> None:
    print()
    print()
    print(f"{produced_file} is not empty.")
    answer = prompt("Create expected file, ignore, or do nothing?", "Ein")
    if answer == "e":
        shutil.copy(produced_file, expected_file)
    elif answer == "i":
        ignored_file.touch()


for produced_file in sorted(Path().rglob("*.out.produced")):
    expected_file = produced_file.with_suffix(".expected")
    ignored_file = produced_file.with_suffix(".ignored")
    no_test_file = produced_file.with_suffix("").with_suffix(".no_test")

    if no_test_file.exists():
        if expected_file.exists():
            remove_file(expected_file, f"{no_test_file} exists")
        if ignored_file.exists():
            remove_file(ignored_file, f"{no_test_file} exists")
        continue

    produced = produced_file.read_bytes()
    if not produced:
        if expected_file.exists():
            remove_file(expected_file, f"{produced_file} is empty")
        if ignored_file.exists():
            remove_file(ignored_file, f"{produced_file} is empty")
        continue

    if ignored_file.exists():
        if expected_file.exists():
            remove_file(expected_file, f"{ignored_file} exists")
        continue

    if expected_file.exists():
        compare_and_merge(produced_file, expected_file)
    else:
        create_or_ignore(produced_file, expected_file, ignored_file)
