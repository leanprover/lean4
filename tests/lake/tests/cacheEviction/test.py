"""Recover from cache eviction through the existing LAKE_CACHE_DIR interface."""

import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import time
import unittest


@unittest.skipUnless(os.name == "posix", "native workspace fixtures use POSIX permissions")
class NativeWorkspaces(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        executable = shutil.which(os.environ.get("LAKE", "lake"))
        self.assertIsNotNone(executable, "the test harness must provide Lake on PATH or through LAKE")
        self.lake = pathlib.Path(executable).resolve()
        prefix = pathlib.Path(subprocess.check_output(
            [os.environ.get("LEAN", "lean"), "--print-prefix"], text=True).strip())
        self.original = prefix / "bin/lake"
        elan = self.root / "elan"
        install = elan / "toolchains/leanprover--lean4---v0.0.0-cache-fixture"
        install.mkdir(parents=True)
        # A directory-based fixture distribution uses the current test compiler's
        # files without requiring an independently downloaded release toolchain.
        for name in ("bin", "lib", "src", "include", "share"):
            if (prefix / name).exists():
                if name == "bin":
                    (install / name).mkdir()
                    for binary in (prefix / name).iterdir():
                        (install / name / binary.name).symlink_to(binary)
                else:
                    (install / name).symlink_to(prefix / name, target_is_directory=True)
        self.install = install
        self.env = dict(os.environ, ELAN_HOME=str(elan),
                        ELAN_TOOLCHAIN="leanprover/lean4:v0.0.0-cache-fixture",
                        LEAN_SYSROOT=str(install), LEAN=str(install / "bin/lean"),
                        LAKE_OVERRIDE_LEAN="1",
                        LAKE_CACHE_DIR=str(self.root / "cache"),
                        LAKE_ARTIFACT_CACHE="1", LAKE_RESTORE_ARTIFACTS="1")
        for key in ("LEAN_GITHASH", "LAKE_SHARED_CACHE_ROOT", "LAKE_SHARED_CACHE_FALLBACK"):
            self.env.pop(key, None)
        self.first = self.project("first")
        self.second = self.project("second")


    def project(self, name):
        project = self.root / name
        project.mkdir()
        (project / "lakefile.toml").write_text('name = "shared_fixture"\n[[lean_lib]]\nname = "Example"\n')
        (project / "Example.lean").write_text("module\npublic def answer : Nat := 42\n")
        return project


    def run_lake(self, project, *args, env=None):
        result = subprocess.run([str(self.lake), *args], cwd=project, env=env or self.env,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertEqual(result.returncode, 0, result.stdout)
        return result.stdout




    def test_archive_disappearance_before_unpack_is_a_recoverable_miss(self):
        self.archive_disappearance(existing_trace=False)

    def test_archive_disappearance_with_existing_trace_rebuilds(self):
        self.archive_disappearance(existing_trace=True)

    def archive_disappearance(self, *, existing_trace):
        mapping = self.root / "outputs.jsonl"
        self.run_lake(self.first, "build", "+Example", "-o", str(mapping))
        self.run_lake(self.first, "cache", "add", str(mapping))
        if existing_trace:
            self.run_lake(self.second, "build", "Example")
            self.assertTrue(list((self.second / ".lake/build").rglob("*.trace")))
            (self.second / ".lake/build/lib/lean/Example.olean").unlink()
            for artifact in (self.root / "cache/artifacts").glob("*.olean"):
                artifact.unlink()
            self.run_lake(self.first, "cache", "add", str(mapping))
        marker = self.root / "archive-removed"
        wrapper = self.install / "bin/leantar"
        wrapper.unlink()
        wrapper.write_text(f'''#!{sys.executable}
import json, os, pathlib, subprocess, sys
original = {str(self.original.with_name("leantar"))!r}
if "-x" in sys.argv and "-j" in sys.argv:
    data = sys.stdin.buffer.read()
    for entry in json.loads(data):
        path = pathlib.Path(entry["file"])
        if path.is_relative_to({str(self.root / "cache")!r}):
            path.unlink()
            pathlib.Path({str(marker)!r}).touch()
    raise SystemExit(subprocess.run([original, *sys.argv[1:]], input=data).returncode)
os.execv(original, [original, *sys.argv[1:]])
''')
        wrapper.chmod(0o755)
        self.run_lake(self.second, "build", "Example")
        self.assertTrue(marker.exists(), "build did not exercise cache archive unpack")
        self.assertTrue((self.second / ".lake/build/lib/lean/Example.olean").is_file())


    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "link interposition needs Linux and cc")
    def test_eviction_after_lookup_is_a_recoverable_miss(self):
        self.eviction_after_lookup(clear_store=False)


    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "link interposition needs Linux and cc")
    def test_clearing_store_during_restore_is_a_recoverable_miss(self):
        self.eviction_after_lookup(clear_store=True)


    def eviction_after_lookup(self, *, clear_store):
        self.run_lake(self.first, "build", "Example")
        pause = self.root / "pause"
        pause.mkdir()
        library = self.root / "pause.so"
        compile_result = subprocess.run(["cc", "-shared", "-fPIC", "-o", str(library),
                                         "pause_link.c", "-ldl"], capture_output=True, text=True,
                                        env={k: v for k, v in os.environ.items() if k != "LD_LIBRARY_PATH"})
        self.assertEqual(compile_result.returncode, 0, compile_result.stderr)
        env = dict(self.env, LD_PRELOAD=str(library), TEST_CACHE_PREFIX=str(self.root / "cache"),
                   TEST_LINK_PAUSE_DIR=str(pause))
        child = subprocess.Popen([str(self.lake), "build", "Example"], cwd=self.second,
                                 env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        try:
            deadline = time.monotonic() + 60
            while not (pause / "source").exists() and child.poll() is None and time.monotonic() < deadline:
                time.sleep(0.01)
            self.assertTrue((pause / "source").exists(), "restore did not enter the controlled race window")
            source = pathlib.Path((pause / "source").read_text())
            if clear_store:
                shutil.rmtree(self.root / "cache")
            else:
                source.unlink()
        finally:
            (pause / "release").touch()
            output, _ = child.communicate(timeout=60)
        self.assertEqual(child.returncode, 0, output)
        self.assertTrue((self.second / ".lake/build/lib/lean/Example.olean").is_file())


if __name__ == "__main__":
    unittest.main()
