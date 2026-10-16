"""The allocation audit must reject well-typed changes that violate its native boundary."""
from pathlib import Path
import subprocess
import sys

generator, source = map(Path, sys.argv[1:])
original = source.read_text()
entry = '@[export lean_gc_dec_ref_cold] def decRefCold'
prefix = original[:original.index(entry)]
cases = {
    "allocation": (
        prefix + entry + """ (o : USize) : BaseIO (List USize) := pure [o]

end
end Native
end Lean.Runtime.GC
""",
        "uses a potentially allocated type",
    ),
    "foreign": (
        original.replace(
            entry,
            '@[extern "lean_gc_unapproved"] opaque unapproved (o : USize) : BaseIO USize\n\n'
            + entry,
        ).replace(
            "  let _ ← Lean.Runtime.GC.decRefCold adapter o",
            "  let o ← unapproved o\n  let _ ← Lean.Runtime.GC.decRefCold adapter o",
        ),
        "unapproved foreign call",
    ),
    "changed-foreign": (
        original.replace('extern "lean_gc_read_rc"', 'extern "lean_gc_unapproved"'),
        "changed foreign definition",
    ),
    "boxed-literal": (
        original.replace("Int32.ofUInt32 1", "(1 : Int32)"),
        "uses a potentially allocated type",
    ),
    "initializer": (
        original.replace("Int32.ofUInt32 1", "one").replace(
            "@[always_inline] public def releaseLast",
            "@[noinline] public def one : Int32 := Int32.ofUInt32 1\n\n"
            "@[always_inline] public def releaseLast",
        ),
        "needs a global initializer",
    ),
}
for name, (text, expected) in cases.items():
    path = Path("_tmp") / f"audit-{name}.lean"
    output = path.with_suffix(".inc")
    path.write_text(text)
    # A failing audit must not replace an existing generated artifact.
    output.write_text("unchanged\n")
    result = subprocess.run(
        ["lean", "--run", str(generator), str(path), str(output)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if result.returncode == 0 or "collector audit:" not in result.stdout or expected not in result.stdout:
        raise AssertionError(f"{name}: expected audit rejection '{expected}'\n{result.stdout}")
    assert output.read_text() == "unchanged\n", f"{name}: replaced output before audit passed"
    print(f"{name}: rejected")
