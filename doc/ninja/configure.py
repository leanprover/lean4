import os
import glob
import ninja_syntax

script_path = os.path.dirname(__file__)


def ignore(d):
    return d.startswith("build") or d.startswith("lean_packages") or \
        d.startswith("log") or d.startswith("__pycache__") or d.startswith("docs")


def createNinja(f):
    ninja = ninja_syntax.Writer(f)
    ninja.rule(name="book", command="mdbook build ..")
    os.chdir(os.path.join(script_path, ".."))
    alectryon = "alectryon --frontend lean4+markup $in --backend webpage -o $out"
    if "lakefile.lean" in os.listdir():
        alectryon += " --lake lakefile.lean"

    ninja.rule(name="alectryon", command=alectryon)
    print("collecting .lean source files in Examples and Monads folders...")
    all_files = []
    for d in ["."] + os.listdir():
        if os.path.isdir(d) and not ignore(d):
            print(f"collecting lean files in {d}")
            for path in glob.glob(f"{d}/*.lean"):
                n = path.replace('\\', '/')
                if "lakefile.lean" not in n:
                    ninja.build(outputs=f"../{n}.md", rule="alectryon", inputs=f"../{n}")
                    all_files += [f"../{n}.md"]

    print("collecting all other md files...")
    for path in glob.glob("**/*.md", recursive=True):
        if not ignore(path) and not path.endswith(".lean.md"):
            n = path.replace('\\', '/')
            if n not in all_files:
                all_files += [f"../{n}"]

    all_files += ["../book.toml"]
    ninja.build(outputs="../out/index.html", rule="book", inputs=all_files)


if __name__ == '__main__':
    with open("build.ninja", 'w') as f:
        createNinja(f)
    print("Now you can run 'ninja' to build the docs then you can open ../out/index.html in your browser.")
