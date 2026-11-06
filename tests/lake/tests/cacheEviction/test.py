"""Recover from cache eviction through the existing LAKE_CACHE_DIR interface."""

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
        for key in ("LEAN_GITHASH",):
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

    def test_partial_archive_restore_forces_a_clean_rebuild(self):
        mapping = self.root / "outputs.jsonl"
        self.run_lake(self.first, "build", "+Example", "-o", str(mapping))
        self.run_lake(self.first, "cache", "add", str(mapping))
        expected = (self.first / ".lake/build/lib/lean/Example.olean").read_bytes()
        marker = self.root / "partial-unpack"
        wrapper = self.install / "bin/leantar"
        wrapper.unlink()
        # Leave every output and its matching trace present, but truncate one output.
        # A stale trace must not turn this incomplete restore into a cache hit.
        wrapper.write_text(f'''#!{sys.executable}
import json, os, pathlib, subprocess, sys
original = {str(self.original.with_name("leantar"))!r}
if "-x" in sys.argv and "-j" in sys.argv:
    data = sys.stdin.buffer.read()
    result = subprocess.run([original, *sys.argv[1:]], input=data)
    if result.returncode == 0:
        path = pathlib.Path(".lake/build/lib/lean/Example.olean")
        path.chmod(0o644)
        path.write_bytes(b"partial output")
        pathlib.Path({str(marker)!r}).touch()
        raise SystemExit(1)
    raise SystemExit(result.returncode)
os.execv(original, [original, *sys.argv[1:]])
''')
        wrapper.chmod(0o755)
        output = self.run_lake(self.second, "-v", "--wfail", "build", "Example")
        self.assertTrue(marker.exists(), output)
        self.assertIn("could not restore module from cache", output)
        self.assertEqual((self.second / ".lake/build/lib/lean/Example.olean").read_bytes(), expected)
        third = self.project("third")
        self.run_lake(third, "build", "Example")
        self.assertEqual((third / ".lake/build/lib/lean/Example.olean").read_bytes(), expected)

    def test_cache_write_errors_are_reported(self):
        artifacts = self.root / "cache/artifacts"
        artifacts.mkdir(parents=True)
        artifacts.chmod(0o555)
        try:
            result = subprocess.run([str(self.lake), "build", "Example"], cwd=self.first,
                                    env=self.env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("failed to cache artifact", result.stdout)
        finally:
            artifacts.chmod(0o755)

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "link interposition needs Linux and cc")
    def test_eviction_after_lookup_is_a_recoverable_miss(self):
        self.eviction_after_lookup(clear_store=False)

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "link interposition needs Linux and cc")
    def test_clearing_store_during_restore_is_a_recoverable_miss(self):
        self.eviction_after_lookup(clear_store=True)

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "link interposition needs Linux and cc")
    def test_static_library_eviction_after_lookup_rebuilds(self):
        self.eviction_after_lookup(clear_store=False, target="Example:static", extension=".a")

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "link interposition needs Linux and cc")
    def test_read_only_cache_eviction_after_lookup_rebuilds(self):
        self.eviction_after_lookup(clear_store=False, read_only=True)

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "write interposition needs Linux and cc")
    def test_partial_static_library_restore_forces_a_clean_rebuild(self):
        target = "Example:static"
        self.run_lake(self.first, "build", target)
        self.run_lake(self.second, "build", target)
        first = self.first / self.run_lake(self.first, "query", target).strip().splitlines()[-1]
        second = self.second / self.run_lake(self.second, "query", target).strip().splitlines()[-1]
        expected = first.read_bytes()
        second.unlink()
        library = self.root / "fail-write.so"
        subprocess.run(["cc", "-shared", "-fPIC", "-o", str(library), "pause_link.c", "-ldl"], check=True,
                       env={k: v for k, v in os.environ.items() if k != "LD_LIBRARY_PATH"})
        marker = self.root / "partial-write"
        env = dict(self.env, LD_PRELOAD=str(library), TEST_CACHE_PREFIX=str(self.root / "cache"),
                   TEST_ARTIFACT_EXTENSION=".a", TEST_RESTORE_WRITE_FAIL=str(marker),
                   TEST_WRITE_TARGET_PREFIX=str(self.second))
        output = self.run_lake(self.second, "-v", "--wfail", "build", target, env=env)
        self.assertTrue(marker.exists(), output)
        self.assertIn("could not restore artifact from cache", output)
        self.assertEqual(second.read_bytes(), expected)
        third = self.project("third")
        self.run_lake(third, "build", target)
        path = third / self.run_lake(third, "query", target).strip().splitlines()[-1]
        self.assertEqual(path.read_bytes(), expected)

    def eviction_after_lookup(self, *, clear_store, target="Example", extension=".olean", read_only=False):
        self.run_lake(self.first, "build", target)
        if read_only:
            self.env.pop("LAKE_ARTIFACT_CACHE")
        pause = self.root / "pause"
        pause.mkdir()
        library = self.root / "pause.so"
        compile_result = subprocess.run(["cc", "-shared", "-fPIC", "-o", str(library),
                                         "pause_link.c", "-ldl"], capture_output=True, text=True,
                                        env={k: v for k, v in os.environ.items() if k != "LD_LIBRARY_PATH"})
        self.assertEqual(compile_result.returncode, 0, compile_result.stderr)
        env = dict(self.env, LD_PRELOAD=str(library), TEST_CACHE_PREFIX=str(self.root / "cache"),
                   TEST_LINK_PAUSE_DIR=str(pause), TEST_ARTIFACT_EXTENSION=extension)
        child = subprocess.Popen([str(self.lake), "-v", "--wfail", "build", target], cwd=self.second,
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
        self.assertIn("could not restore", output)
        def artifact(project):
            if extension == ".a":
                return project / self.run_lake(project, "query", target).strip().splitlines()[-1]
            return project / ".lake/build/lib/lean/Example.olean"
        self.assertEqual(artifact(self.second).read_bytes(), artifact(self.first).read_bytes())
        # A third workspace must also consume the recovered cache mapping successfully.
        third = self.project("third")
        self.run_lake(third, "build", target)
        self.assertEqual(artifact(third).read_bytes(), artifact(self.first).read_bytes())

if __name__ == "__main__":
    unittest.main()
