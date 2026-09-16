#!/usr/bin/env python3
"""Produce a Perfetto/Chrome trace of test-suite timings.

ctest reports an accurate *duration* per test (`... Passed X.XX sec`) but no
sub-second per-test *start* time in any of its output formats, so a real parallel
timeline has to be anchored externally. By default this runs the real `ctest` and
timestamps its own output stream: the `Start <id>: <name>` line gives each test's
launch time and the result line gives its exact duration. This adds no measurement
overhead, so the timeline reflects a genuine run.

The `--strace` mode instead traces every process (execve/exit via seccomp-bpf) to
show per-process structure (each `lean`, `grep`, ... within a test). It is useful
for drilling into one test, but its ptrace overhead inflates and serializes
process-heavy tests (e.g. lake), so it is not the way to measure real timings.

Output is Chrome Trace Event Format JSON, loadable at https://ui.perfetto.dev or
chrome://tracing. Slices are packed into lanes (one trace "thread" each) via greedy
interval partitioning, so the number of occupied lanes at any instant is the actual
concurrency.

Usage:
  tests/trace_timings.py -o trace.json                 # whole suite (-j defaults to nproc)
  tests/trace_timings.py -o trace.json -R 'elab/'      # a subset
  tests/trace_timings.py --strace -R 'lake/.*hello' -o proc.json            # per-process detail
  tests/trace_timings.py --strace --processes -R 'elab/abst' -o proc.json   # every process
  tests/trace_timings.py --strace --log _tmp_strace.log --json _tmp_ctest_tests.json -o t.json

Unrecognized arguments (e.g. -R <regex>, -j <n>, -E <regex>) are passed to ctest.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time

# --- ctest stdout parsing (default collector) ---
START = re.compile(r'^\s*Start\s+(\d+):\s+(.+?)\s*$')
RESULT = re.compile(r'Test\s+#(\d+):\s')
DURATION = re.compile(r'([\d.]+)\s+sec\s*$')

# --- strace parsing (--strace collector) ---
# `PID TIMESTAMP rest` produced by `strace -f -ttt`.
LINE = re.compile(r'^(\d+)\s+(\d+\.\d+)\s+(.*)$')
# `execve("<path>", ` up to (but not including) the argv `[`.
EXECVE_HEAD = re.compile(r'execve\("(?:[^"\\]|\\.)*",\s*\[')
EXIT = re.compile(r'(?:exit_group|exit)\((\d+)')
CHDIR = re.compile(r'^chdir\("((?:[^"\\]|\\.)*)"\)')
# A completed clone/fork (possibly `<... clone resumed>`) returns the child pid.
CLONE_RET = re.compile(r'(?:clone3?|vfork|fork)\b.*=\s*(\d+)\s*$')
SYSCALLS = 'execve,clone,clone3,vfork,fork,chdir,exit,exit_group'


def category(name):
    return name.split('/', 1)[0] if '/' in name else name


# ---------------------------------------------------------------------------
# Collector 1: timestamp ctest's own output (default; no measurement overhead)
# ---------------------------------------------------------------------------
def collect_via_ctest(build_dir, passthrough):
    cmd = ['stdbuf', '-oL', 'ctest', '--test-dir', build_dir] + passthrough
    print('running:', ' '.join(cmd), file=sys.stderr)
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, bufsize=1)
    starts = {}   # test id -> (start_s, name)
    items = []
    for line in proc.stdout:
        ts = time.monotonic()
        sys.stdout.write(line)  # echo so the user sees live progress
        sys.stdout.flush()
        sm = START.match(line)
        if sm:
            starts[int(sm.group(1))] = (ts, sm.group(2))
            continue
        rm = RESULT.search(line)
        if not rm:
            continue
        tid = int(rm.group(1))
        dm = DURATION.search(line)
        start, name = starts.pop(tid, (None, None))
        if name is None:  # result without a seen Start: recover from the line
            nm = re.search(r'Test\s+#\d+:\s+(\S+)', line)
            name = nm.group(1) if nm else f'test#{tid}'
        dur = float(dm.group(1)) if dm else None
        if start is None:
            start = ts - (dur or 0.0)
        end = start + dur if dur is not None else ts
        items.append({'name': name, 'cat': category(name), 'start': start, 'end': end,
                      'code': 0 if ' Passed ' in line else 1,
                      'args': {'duration_s': round(end - start, 3),
                               'status': 'Passed' if ' Passed ' in line else line.split('***')[-1].split('  ')[0].strip() or 'failed',
                               'test_id': tid}})
    proc.wait()
    return items


# ---------------------------------------------------------------------------
# Collector 2: strace (per-process detail; --strace)
# ---------------------------------------------------------------------------
def extract_argv(rest):
    """Return the argv list of an execve line, or None if this line has no argv."""
    m = EXECVE_HEAD.search(rest)
    if not m:
        return None
    i = m.end() - 1  # index of '['
    args, depth, inq, n = [], 0, False, len(rest)
    buf = []
    while i < n:
        c = rest[i]
        if inq:
            if c == '\\':
                buf.append(rest[i + 1] if i + 1 < n else '')
                i += 2
                continue
            if c == '"':
                inq = False
                args.append(''.join(buf))
                buf = []
                while i + 1 < n and rest[i + 1] not in ',]':  # skip a `"foo"...` truncation marker
                    i += 1
            else:
                buf.append(c)
        else:
            if c == '"':
                inq = True
            elif c == '[':
                depth += 1
            elif c == ']':
                depth -= 1
                if depth == 0:
                    return args
        i += 1
    return args


def parse_strace(log_path):
    """Reconstruct one slice per process lifetime: (pid, argv, start, end, code, cwd).

    Each slice spans a PID's first execve to its exit, so an intra-PID exec chain
    (bash exec'ing `./test.sh`) stays one slice identified by ctest's command. cwd is
    tracked via clone() inheritance plus chdir(), which tells apart tests with
    identical command lines (lake's `./test.sh`, run in different dirs). PID reuse is
    handled by closing a PID's slice at its exit.
    """
    open_slice = {}   # pid -> (start_s, argv, cwd); present only while alive
    cwd = {}
    slices = []
    last_ts = {}
    with open(log_path, errors='replace') as f:
        for line in f:
            m = LINE.match(line)
            if not m:
                continue
            pid, ts, rest = int(m.group(1)), float(m.group(2)), m.group(3)
            last_ts[pid] = ts
            if rest.startswith('execve('):
                if pid in open_slice:  # exec chain within one lifetime: keep the first
                    continue
                argv = extract_argv(rest)
                if argv is not None:
                    open_slice[pid] = (ts, argv, cwd.get(pid))
            elif rest.startswith('chdir('):
                cm = CHDIR.match(rest)
                if cm:
                    cwd[pid] = cm.group(1)
            elif rest.startswith(('exit_group(', 'exit(')):
                em = EXIT.match(rest)
                prev = open_slice.pop(pid, None)
                if prev:
                    slices.append((pid, tuple(prev[1]), prev[0], ts,
                                   int(em.group(1)) if em else None, prev[2]))
                cwd.pop(pid, None)
            else:
                cm = CLONE_RET.search(rest)
                if cm:  # parent line; child inherits parent's cwd
                    cwd[int(cm.group(1))] = cwd.get(pid)
    for pid, (start, argv, wd) in open_slice.items():  # killed without a traced exit
        slices.append((pid, tuple(argv), start, last_ts.get(pid, start), None, wd))
    return slices


def load_test_map(json_path):
    """Build a lookup from a process's (argv, cwd) to its ctest test name."""
    d = json.load(open(json_path))
    by_argv, by_argv_cwd, by_sig = {}, {}, {}
    for t in d['tests']:
        argv = tuple(t['command'])
        props = {p['name']: p['value'] for p in t.get('properties', [])}
        wd = os.path.normpath(props['WORKING_DIRECTORY']) if 'WORKING_DIRECTORY' in props else None
        by_argv.setdefault(argv, set()).add(t['name'])
        if wd is not None:
            by_argv_cwd[(argv, wd)] = t['name']
            by_sig.setdefault((argv[0] if argv else None, len(argv), wd), set()).add(t['name'])

    def lookup(argv, cwd):
        names = by_argv.get(argv)
        if names and len(names) == 1:
            return next(iter(names))
        if cwd is None:
            return None
        ncwd = os.path.normpath(cwd)
        if (argv, ncwd) in by_argv_cwd:
            return by_argv_cwd[(argv, ncwd)]
        cand = by_sig.get((argv[0] if argv else None, len(argv), ncwd))  # argv truncated by -s
        return next(iter(cand)) if cand and len(cand) == 1 else None

    return lookup


def short_name(argv):
    base = os.path.basename(argv[0]) if argv else '?'
    rest = next((a for a in argv[1:] if not a.startswith('-')), '')
    return f'{base} {os.path.basename(rest)}'.strip()


def strace_items(slices, lookup, processes_mode):
    items = []
    for pid, argv, start, end, code, wd in slices:
        name = lookup(argv, wd)
        if name is not None:
            cat = category(name)
        elif processes_mode:
            name = short_name(list(argv))
            cat = os.path.basename(argv[0]) if argv else '?'
        else:
            continue
        items.append({'name': name, 'cat': cat, 'start': start, 'end': max(end, start),
                      'code': code, 'args': {'os_pid': pid, 'argv': ' '.join(argv)}})
    return items


# ---------------------------------------------------------------------------
# Shared: lane packing, Perfetto emission, summary
# ---------------------------------------------------------------------------
def assign_lanes(items):
    """Greedy interval partitioning; returns (lane per item, lane count)."""
    import heapq
    order = sorted(range(len(items)), key=lambda i: items[i]['start'])
    free, next_lane, lanes = [], 0, [0] * len(items)
    for i in order:
        if free and free[0][0] <= items[i]['start']:
            _, lane = heapq.heappop(free)
        else:
            lane, next_lane = next_lane, next_lane + 1
        lanes[i] = lane
        heapq.heappush(free, (items[i]['end'], lane))
    return lanes, next_lane


def emit_trace(items, out_path, proc_name):
    t0 = min(it['start'] for it in items)
    lanes, nlanes = assign_lanes(items)
    # Lanes map to trace "threads" tid = lane + 1: Perfetto treats tid 0 as the
    # kernel idle task and merges it with another track, which would overlap slices.
    events = [{'ph': 'M', 'name': 'process_name', 'pid': 1, 'tid': 0,
               'args': {'name': proc_name}}]
    for lane in range(nlanes):
        events.append({'ph': 'M', 'name': 'thread_name', 'pid': 1, 'tid': lane + 1,
                       'args': {'name': f'lane {lane}'}})
    for it, lane in zip(items, lanes):
        events.append({'name': it['name'], 'cat': it['cat'], 'ph': 'X',
                       'ts': round((it['start'] - t0) * 1e6, 3),
                       'dur': round((it['end'] - it['start']) * 1e6, 3),
                       'pid': 1, 'tid': lane + 1,
                       'args': {**it['args'], 'exit_code': it['code']}})
    with open(out_path, 'w') as f:
        json.dump({'traceEvents': events, 'displayTimeUnit': 'ms'}, f)
    return nlanes


def print_summary(items, kind):
    t0 = min(it['start'] for it in items)
    t1 = max(it['end'] for it in items)
    wall = t1 - t0
    busy = sum(it['end'] - it['start'] for it in items)
    fails = [it for it in items if it['code'] not in (0, None)]
    print(f'\n{len(items)} {kind}, wall {wall:.1f}s, summed {busy:.1f}s '
          f'({busy / wall:.1f}x concurrency), {len(fails)} nonzero exit')
    print(f'top {min(15, len(items))} slowest:')
    for it in sorted(items, key=lambda x: x['end'] - x['start'], reverse=True)[:15]:
        print(f'  {it["end"] - it["start"]:8.2f}s  {it["name"]}')


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('-o', '--out', default='test_suite_trace.json', help='output trace JSON')
    ap.add_argument('--build-dir', default='build/release/stage1', help='ctest build dir')
    ap.add_argument('--strace', action='store_true',
                    help='trace every process via strace (per-process detail; adds overhead)')
    ap.add_argument('--processes', action='store_true',
                    help='with --strace, emit every process, not just tests')
    ap.add_argument('--log', help='--strace: reuse an existing strace log (skip running)')
    ap.add_argument('--json', help='--strace: reuse an existing ctest json')
    ap.add_argument('--keep', action='store_true', help='--strace: keep intermediate log / json')
    args, extra = ap.parse_known_args()

    build_dir = os.path.abspath(args.build_dir)
    out = os.path.abspath(args.out)
    passthrough = [a for a in extra if a != '--']
    if not any(a == '-j' or a.startswith('-j') for a in passthrough):
        passthrough += ['-j', str(os.cpu_count())]

    if not args.strace:
        items = collect_via_ctest(build_dir, passthrough)
        if not items:
            sys.exit('no test results parsed from ctest output')
        nlanes = emit_trace(items, out, 'test suite')
        print(f'\nwrote {out}  ({os.path.getsize(out) // 1024} KiB, {len(items)} tests, {nlanes} lanes)')
        print_summary(items, 'tests')
        return

    # --strace path
    if args.log:
        log_path, json_path = args.log, (args.json or 'ctest_tests.json')
    else:
        log_path = os.path.abspath('_tmp_strace.log')
        json_path = os.path.abspath('_tmp_ctest_tests.json')
        with open(json_path, 'w') as jf:
            subprocess.run(['ctest', '--test-dir', build_dir, '--show-only=json-v1'],
                           stdout=jf, check=True)
        cmd = ['strace', '-f', '-ttt', '--seccomp-bpf', '-e', f'trace={SYSCALLS}',
               '-s', '256', '-qq', '-o', log_path, 'ctest', '--test-dir', build_dir] + passthrough
        print('running:', ' '.join(cmd), file=sys.stderr)
        subprocess.run(cmd)

    lookup = load_test_map(json_path)
    slices = parse_strace(log_path)
    print(f'parsed {len(slices)} process slices from {log_path}', file=sys.stderr)
    items = strace_items(slices, lookup, args.processes)
    if not items:
        sys.exit('no slices matched; nothing to write')
    nlanes = emit_trace(items, out, 'process timeline' if args.processes else 'test suite')
    print(f'wrote {out}  ({os.path.getsize(out) // 1024} KiB, {len(items)} slices, {nlanes} lanes)')
    print_summary(items, 'processes' if args.processes else 'tests')
    if not args.log and not args.keep:
        for p in (log_path, json_path):
            try:
                os.remove(p)
            except OSError:
                pass


if __name__ == '__main__':
    main()
