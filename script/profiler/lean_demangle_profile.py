#!/usr/bin/env python3
"""
Lean name demangler for samply / Firefox Profiler profiles.

Reads a profile JSON (plain or gzipped), demangles Lean function names
in the string table, and writes the result back.

Usage:
    python lean_demangle_profile.py profile.json -o profile-demangled.json
    python lean_demangle_profile.py profile.json.gz -o profile-demangled.json.gz
"""

import argparse
import gzip
import json
import sys

from lean_demangle import demangle_lean_name


def _demangle_string_array(string_array):
    """Demangle Lean names in a string array in-place. Returns count."""
    count = 0
    for i, s in enumerate(string_array):
        if not isinstance(s, str):
            continue
        demangled = demangle_lean_name(s)
        if demangled != s:
            string_array[i] = demangled
            count += 1
    return count


def rewrite_profile(profile):
    """
    Demangle Lean names in a Firefox Profiler profile dict (in-place).

    Handles two profile formats:
    - Newer: shared.stringArray (single shared string table)
    - Older/samply: per-thread stringArray (each thread has its own)
    """
    count = 0

    # Shared string table (newer Firefox Profiler format)
    shared = profile.get("shared")
    if shared is not None:
        sa = shared.get("stringArray")
        if sa is not None:
            count += _demangle_string_array(sa)

    # Per-thread string tables (samply format)
    for thread in profile.get("threads", []):
        sa = thread.get("stringArray")
        if sa is not None:
            count += _demangle_string_array(sa)

    return count


def process_profile_file(input_path, output_path):
    """Read a profile, demangle names, write it back."""
    is_gzip = input_path.endswith('.gz')

    if is_gzip:
        with gzip.open(input_path, 'rt', encoding='utf-8') as f:
            profile = json.load(f)
    else:
        with open(input_path, 'r', encoding='utf-8') as f:
            profile = json.load(f)

    count = rewrite_profile(profile)

    out_gzip = output_path.endswith('.gz') if output_path else is_gzip

    if output_path:
        if out_gzip:
            with gzip.open(output_path, 'wt', encoding='utf-8') as f:
                json.dump(profile, f, ensure_ascii=False)
        else:
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(profile, f, ensure_ascii=False)
    else:
        json.dump(profile, sys.stdout, ensure_ascii=False)
        sys.stdout.write('\n')

    return count


def main():
    parser = argparse.ArgumentParser(
        description="Demangle Lean names in samply/Firefox Profiler profiles")
    parser.add_argument('input', help='Input profile (JSON or .json.gz)')
    parser.add_argument('-o', '--output',
                        help='Output path (default: stdout for JSON, '
                             'or input with -demangled suffix)')
    args = parser.parse_args()

    output = args.output
    if output is None and not sys.stdout.isatty():
        output = None  # write to stdout
    elif output is None:
        # Generate output filename
        inp = args.input
        if inp.endswith('.json.gz'):
            output = inp[:-8] + '-demangled.json.gz'
        elif inp.endswith('.json'):
            output = inp[:-5] + '-demangled.json'
        else:
            output = inp + '-demangled'

    count = process_profile_file(args.input, output)
    if output:
        print(f"Demangled {count} names, wrote {output}", file=sys.stderr)


if __name__ == '__main__':
    main()
