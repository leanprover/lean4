#!/usr/bin/env python3
"""
Symbolicate a raw samply profile using samply's symbolication API,
then demangle Lean names.

Usage:
    python symbolicate_profile.py --server http://127.0.0.1:3000/TOKEN \
        raw-profile.json.gz -o symbolicated-demangled.json.gz
"""

import argparse
import gzip
import json
import sys
import urllib.request

from lean_demangle import demangle_lean_name


def symbolicate_and_demangle(profile, server_url):
    """
    Symbolicate a raw samply profile via the symbolication API,
    then demangle Lean names. Modifies the profile in-place.
    Returns the number of names resolved.
    """
    libs = profile.get("libs", [])
    memory_map = [[lib["debugName"], lib["breakpadId"]] for lib in libs]

    count = 0
    for thread in profile.get("threads", []):
        count += _process_thread(thread, libs, memory_map, server_url)

    return count


def _process_thread(thread, libs, memory_map, server_url):
    """Symbolicate and demangle one thread. Returns count of resolved names."""
    sa = thread.get("stringArray")
    ft = thread.get("frameTable")
    func_t = thread.get("funcTable")
    rt = thread.get("resourceTable")

    if not all([sa, ft, func_t, rt]):
        return 0

    # Build mapping: func_index -> (lib_index, address)
    # A function may be referenced by multiple frames; pick any address.
    func_info = {}  # func_idx -> (lib_idx, address)
    for i in range(ft.get("length", 0)):
        addr = ft["address"][i]
        func_idx = ft["func"][i]
        if func_idx in func_info:
            continue
        res_idx = func_t["resource"][func_idx]
        if res_idx < 0 or res_idx >= rt.get("length", 0):
            continue
        lib_idx = rt["lib"][res_idx]
        if lib_idx < 0 or lib_idx >= len(libs):
            continue
        func_info[func_idx] = (lib_idx, addr)

    if not func_info:
        return 0

    # Batch symbolication: group by lib, send all addresses at once
    frames_to_symbolicate = []
    func_order = []  # track which func each frame corresponds to
    for func_idx, (lib_idx, addr) in func_info.items():
        frames_to_symbolicate.append([lib_idx, addr])
        func_order.append(func_idx)

    # Call the symbolication API
    symbols = _call_symbolication_api(
        server_url, memory_map, frames_to_symbolicate)

    if not symbols:
        return 0

    # Update stringArray with demangled names
    count = 0
    for func_idx, symbol_name in zip(func_order, symbols):
        if symbol_name is None:
            continue
        demangled = demangle_lean_name(symbol_name)
        name_idx = func_t["name"][func_idx]
        if name_idx < len(sa):
            sa[name_idx] = demangled
            count += 1

    return count


def _call_symbolication_api(server_url, memory_map, frames):
    """
    Call the Firefox Profiler symbolication API v5.
    frames: list of [lib_index, address]
    Returns: list of symbol names (or None for unresolved frames).
    """
    url = server_url.rstrip("/") + "/symbolicate/v5"

    # Send all frames as one "stack" in one job
    req_body = json.dumps({
        "memoryMap": memory_map,
        "stacks": [frames],
    }).encode()

    req = urllib.request.Request(
        url,
        data=req_body,
        headers={"Content-Type": "application/json"},
    )

    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            result = json.loads(resp.read())
    except Exception as e:
        print(f"Symbolication API error: {e}", file=sys.stderr)
        return None

    if "error" in result:
        print(f"Symbolication API error: {result['error']}", file=sys.stderr)
        return None

    # Extract symbol names from result
    results = result.get("results", [])
    if not results:
        return None

    stacks = results[0].get("stacks", [[]])
    if not stacks:
        return None

    symbols = []
    for frame_result in stacks[0]:
        if isinstance(frame_result, dict):
            symbols.append(frame_result.get("function"))
        elif isinstance(frame_result, str):
            symbols.append(frame_result)
        else:
            symbols.append(None)

    return symbols


def process_file(input_path, output_path, server_url):
    """Read a raw profile, symbolicate + demangle, write it back."""
    is_gzip = input_path.endswith('.gz')

    if is_gzip:
        with gzip.open(input_path, 'rt', encoding='utf-8') as f:
            profile = json.load(f)
    else:
        with open(input_path, 'r', encoding='utf-8') as f:
            profile = json.load(f)

    count = symbolicate_and_demangle(profile, server_url)

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
        description="Symbolicate a raw samply profile and demangle Lean names")
    parser.add_argument('input', help='Raw profile (JSON or .json.gz)')
    parser.add_argument('-o', '--output', help='Output path')
    parser.add_argument('--server', required=True,
                        help='Samply server URL (e.g., http://127.0.0.1:3000/TOKEN)')
    args = parser.parse_args()

    output = args.output
    if output is None:
        inp = args.input
        if inp.endswith('.json.gz'):
            output = inp[:-8] + '-demangled.json.gz'
        elif inp.endswith('.json'):
            output = inp[:-5] + '-demangled.json'
        else:
            output = inp + '-demangled'

    count = process_file(args.input, output, args.server)
    print(f"Symbolicated and demangled {count} names, wrote {output}",
          file=sys.stderr)


if __name__ == '__main__':
    main()
