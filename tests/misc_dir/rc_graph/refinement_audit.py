"""Well-typed collector mutations must fail both a named theorem and the compiled candidate."""
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys


def run(args, **kwargs):
    return subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **kwargs)


def checked(args, **kwargs):
    result = run(args, **kwargs)
    if result.returncode:
        raise AssertionError(f"{args}: failed before the regression check\n{result.stdout}")
    return result


generator, source = (Path(p).resolve() for p in sys.argv[1:])
original = source.read_text()
cases = [
    (
        "stale-sticky-check", "ConcurrentRefinement.lean", "shared_release_refines",
        "    let sharedRC ← read",
        "    let sharedRC := rc",
    ),
    (
        "snapshot-last-reference", "ConcurrentRefinement.lean", "shared_release_refines",
        "      return (← fetchAdd) == Int32.ofUInt32 0xFFFFFFFF",
        "      let _ ← fetchAdd\n"
        "      return sharedRC == Int32.ofUInt32 0xFFFFFFFF",
    ),
    (
        "queue-tail", "Refinement.lean", "release_refines",
        "    a.writeNext o todo",
        "    a.writeNext o a.empty",
    ),
    (
        "queue-head", "Refinement.lean", "release_refines",
        "    a.work o",
        "    pure todo",
    ),
    (
        "cursor-advance", "Refinement.lean", "scan_refines",
        "    scan next release (remaining - 1) (next cursor) todo",
        "    scan next release (remaining - 1) cursor todo",
    ),
    (
        "thunk-order", "Refinement.lean", "visitThunk_refines",
        "  let todo ← release a (← a.readThunkClosure o) todo\n"
        "  let todo ← release a (← a.readThunkValue o) todo",
        "  let todo ← release a (← a.readThunkValue o) todo\n"
        "  let todo ← release a (← a.readThunkClosure o) todo",
    ),
    (
        "shared-entry", "Refinement.lean", "entry_refines",
        "    loop a (a.object r) a.empty",
        "    return a.empty",
    ),
    (
        "direct-child", "Refinement.lean", "runLoop_cons",
        "        loop a (a.object r) todo",
        "        resume todo",
    ),
    (
        "direct-pending", "Refinement.lean", "runLoop_cons",
        "        loop a (a.object r) todo",
        "        loop a (a.object r) a.empty",
    ),
    (
        "direct-slot", "Refinement.lean", "runLoop_cons",
        "      let r ← a.readField first",
        "      let r ← a.readField (a.fieldNext first)",
    ),
    (
        "native-entry", "Refinement.lean", "native_entry_uses_shared",
        "  let _ ← Lean.Runtime.GC.decRefCold adapter o",
        "  pure ()",
    ),
    (
        "native-thunk-slot", "Refinement.lean", "native_entry_uses_shared",
        "    readThunkClosure, readThunkValue, dispose",
        "    readThunkClosure := readThunkValue, readThunkValue, dispose",
    ),
    (
        "array-tag", "Dispatch.lean", "classify_refines",
        "  | 246 => .array",
        "  | 246 => .closure",
    ),
    (
        "array-count", "Dispatch.lean", "field_count_dispatch_refines",
        "  | .array => p.arrayCount o",
        "  | .array => pure 0",
    ),
    (
        "array-begin", "Dispatch.lean", "field_begin_dispatch_refines",
        "  | .array => p.arrayBegin o",
        "  | .array => p.closureBegin o",
    ),
    (
        "external-finalizer", "Dispatch.lean", "dispose_dispatch_refines",
        "  | .external => do p.finalizeExternal o; p.freeSmall o",
        "  | .external => p.freeSmall o",
    ),
    (
        "native-array-count", "Dispatch.lean", "native_dispatch_uses_shared",
        "  { ctorCount, ctorBegin, closureCount, closureBegin, "
        "arrayCount, arrayBegin, refBegin",
        "  { ctorCount, ctorBegin, closureCount, closureBegin, "
        "arrayCount := closureCount, arrayBegin, refBegin",
    ),
]
for name, module, theorem, before, after in cases:
    assert original.count(before) == 1, f"{name}: mutation no longer matches exactly once"
    directory = Path("_tmp") / f"refinement-{name}"
    directory.mkdir(exist_ok=True)
    path = directory / "Collector.lean"
    path.write_text(original.replace(before, after))
    checked(["lean", f"--root={directory}", "-o", str(path.with_suffix(".olean")), str(path)])

    # Require an error inside the intended theorem, not an import, syntax, or generator failure.
    refinement = Path(module).read_text()
    start = refinement.index(f"theorem {theorem} ")
    boundary = re.search(r"\n(?:private )?(?:theorem |def |end\b)", refinement[start + 1:])
    end = start + 1 + boundary.start() if boundary else len(refinement)
    first_line = refinement.count("\n", 0, start) + 1
    last_line = refinement.count("\n", 0, end) + 1
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(directory), "_tmp"]))
    proof = run(["lean", "--json", module], env=env)
    diagnostics = [json.loads(line) for line in proof.stdout.splitlines() if line.startswith("{")]
    assert proof.returncode and any(
        d.get("severity") == "error" and first_line <= d["pos"]["line"] <= last_line
        for d in diagnostics
    ), f"{name}: expected {theorem} to reject mutation\n{proof.stdout}"
    (directory / "proof.jsonl").write_text(proof.stdout)

    # Each mutant still passes the allocation audit. Correctness is a separate contract.
    checked(["lean", "--run", str(generator), str(path), str(directory / "object_gc.inc")])
    binary = directory / "candidate"
    checked(["leanc", *shlex.split(os.environ.get("LEANC_OPTS", "")),
             f"-I{directory}", "-o", str(binary), "candidate.c"])
    native = run([str(binary)])
    assert native.returncode == 1 and "(seed " in native.stdout, (
        f"{name}: expected a candidate assertion failure\n{native.stdout}"
    )
    (directory / "candidate.log").write_text(native.stdout)
    print(f"{name}: rejected by {theorem} and compiled candidate", flush=True)
