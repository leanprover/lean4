"""Exercise opt-in shared-cache selection, compatibility and reuse."""

import http.server
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import threading
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
                        LAKE_SHARED_CACHE_ROOT=str(self.root / "shared"),
                        LAKE_CACHE_DIR=str(self.root / "private"),
                        LAKE_SHARED_CACHE_FALLBACK=str(self.root / "private"),
                        LAKE_ARTIFACT_CACHE="1", LAKE_RESTORE_ARTIFACTS="1")
        self.env.pop("LEAN_GITHASH", None)
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


    def test_explicit_sysroot_with_colocated_lake(self):
        prefix = self.root / "colocated"
        (prefix / "bin").mkdir(parents=True)
        shutil.copy2(self.lake, prefix / "bin/lake")
        compiler = self.original.parent.parent
        (prefix / "bin/lean").symlink_to(compiler / "bin/lean")
        (prefix / "lib").symlink_to(compiler / "lib", target_is_directory=True)
        selections = []
        for override in ("0", "1"):
            result = subprocess.run([str(prefix / "bin/lake"), "--shared-cache-dir"], cwd=self.first,
                                    env=dict(self.env, LAKE_OVERRIDE_LEAN=override),
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            selections.append(result.stdout.strip())
        self.assertEqual(selections[0], selections[1])
        self.assertTrue(selections[1].startswith(str(self.root / "shared/toolchains")))


    def test_toolchain_revision_namespaces_are_separate(self):
        first = self.run_lake(self.first, "--shared-cache-dir").strip()
        install = self.install.with_name("leanprover--lean4---v0.0.1-cache-fixture")
        install.mkdir()
        for name in ("bin", "lib", "src", "include", "share"):
            if (self.install / name).exists():
                (install / name).symlink_to(self.install / name, target_is_directory=True)
        env = dict(self.env, ELAN_TOOLCHAIN="leanprover/lean4:v0.0.1-cache-fixture",
                   LEAN_SYSROOT=str(install), LEAN=str(install / "bin/lean"))
        second = self.run_lake(self.first, "--shared-cache-dir", env=env).strip()
        self.assertTrue(second)
        self.assertNotEqual(first, second)
        self.run_lake(self.first, "build", "Example", env=env)


    def test_forwarding_sysroot_shares_without_bypassing_compiler_wrapper(self):
        expected = self.run_lake(self.first, "--shared-cache-dir").strip()
        proxy = self.root / "forwarding"
        (proxy / "bin").mkdir(parents=True)
        for name in ("lib", "src", "include", "share"):
            if (self.install / name).exists():
                (proxy / name).symlink_to(self.install / name, target_is_directory=True)
        for binary in (self.install / "bin").iterdir():
            if binary.name != "lean":
                (proxy / "bin" / binary.name).symlink_to(binary)
        marker = self.root / "wrapper-used"
        compiler = self.original.with_name("lean")
        wrapper = proxy / "bin/lean"
        wrapper.write_text(f'''#!{sys.executable}
import os, pathlib, sys
if sys.argv[1:] == ["--print-prefix"]:
    print({str(proxy)!r})
    raise SystemExit(0)
if any(arg.endswith("Example.lean") for arg in sys.argv[1:]):
    pathlib.Path({str(marker)!r}).touch()
os.execv({str(compiler)!r}, [{str(compiler)!r}, *sys.argv[1:]])
''')
        wrapper.chmod(0o755)
        env = dict(self.env, LEAN=str(wrapper))
        env.pop("LEAN_SYSROOT")
        selected = self.run_lake(self.first, "--shared-cache-dir", env=env).strip()
        self.assertEqual(selected, expected)
        self.run_lake(self.first, "build", "Example", env=env)
        self.assertTrue(marker.exists(), "cache sharing bypassed the compiler wrapper")
        self.run_lake(self.second, "build", "Example")
        self.assertEqual((self.first / ".lake/build/lib/lean/Example.olean").stat().st_ino,
                         (self.second / ".lake/build/lib/lean/Example.olean").stat().st_ino)


    def test_linked_and_overridden_toolchains_keep_private_storage(self):
        self.assertEqual(self.run_lake(self.first, "--shared-cache-dir",
                                      env=dict(self.env, LEAN_GITHASH="local-edit")).strip(), "")
        target = self.install.with_name("local-build")
        self.install.rename(target)
        self.install.symlink_to(target, target_is_directory=True)
        self.assertEqual(self.run_lake(self.first, "--shared-cache-dir").strip(), "")
        self.run_lake(self.first, "build", "Example")


    def test_reuse_rebuild_and_private_rollback(self):
        selected = self.run_lake(self.first, "--shared-cache-dir").strip()
        self.assertTrue(selected.startswith(str(self.root / "shared/toolchains")))
        self.run_lake(self.first, "build", "Example")
        result = self.run_lake(self.second, "build", "Example")
        self.assertNotIn("Built Example", result)
        first = self.first / ".lake/build/lib/lean/Example.olean"
        second = self.second / ".lake/build/lib/lean/Example.olean"
        self.assertEqual(first.stat().st_ino, second.stat().st_ino)
        before = first.read_bytes()
        (self.second / "Example.lean").write_text("module\npublic def changed : Nat := 43\n")
        self.run_lake(self.second, "build", "Example")
        self.assertEqual(first.read_bytes(), before)
        self.assertNotEqual(second.read_bytes(), before)
        self.run_lake(self.second, "build", "Example", env=dict(self.env, LAKE_SHARED_CACHE_ROOT=""))
        self.assertTrue(list((self.root / "private/artifacts").glob("*.olean")))


    def test_old_child_retains_private_fallback(self):
        if self.original.resolve() == self.lake:
            self.skipTest("a distinct stock Lake executable is not available")
        old = self.original
        result = self.run_lake(self.first, "env", str(old), "env", "printenv", "LAKE_CACHE_DIR")
        self.assertEqual(result.strip().splitlines()[-1], str(self.root / "private"))
        private = self.run_lake(self.first, "--shared-cache-dir", env=dict(self.env, LAKE_RESTORE_ARTIFACTS="0"))
        self.assertEqual(private.strip(), "")
        override = self.run_lake(self.first, "--shared-cache-dir", env=dict(self.env, LAKE_CACHE_DIR=str(self.root / "override")))
        self.assertEqual(override.strip(), "")
        (self.first / "lakefile.toml").unlink()
        (self.first / "lakefile.lean").write_text(
            'import Lake\nopen Lake DSL\npackage shared_fixture\nlean_lib Example\n')
        self.run_lake(self.first, "env", str(old), "build", "Example")


    def test_cached_configuration_survives_stock_patched_alternation(self):
        if self.original.resolve() == self.lake:
            self.skipTest("a distinct stock Lake executable is not available")
        config = '''import Lake
open Lake DSL
initialize do
  let (elan, lean, lake) ← findInstall?
  let env ← (Env.compute lake.get! lean.get! elan).toIO IO.userError
  unless env.cacheKey? == some "abi-fixture" do
    throw <| IO.userError "cached Lake.Env field layout changed"
  unless env.cacheArtifactEndpoint? == some "https://fixture.invalid" do
    throw <| IO.userError "cached Lake.Env endpoint field layout changed"
package shared_fixture
lean_lib Example
'''
        env = dict(self.env, LAKE_CACHE_KEY="abi-fixture",
                   LAKE_CACHE_ARTIFACT_ENDPOINT="https://fixture.invalid")
        for project, binaries in ((self.first, (self.original, self.lake, self.original)),
                                  (self.second, (self.lake, self.original, self.lake))):
            (project / "lakefile.toml").unlink()
            (project / "lakefile.lean").write_text(config)
            timestamp = None
            for binary in binaries:
                result = subprocess.run([str(binary), "env", "true"], cwd=project, env=env,
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                installed, = (project / ".lake").rglob("lakefile.olean")
                if timestamp is not None:
                    self.assertEqual(installed.stat().st_mtime_ns, timestamp)
                timestamp = installed.stat().st_mtime_ns


    def test_existing_executable_keeps_execute_permission_after_sharing(self):
        source = self.root / "downloaded-executable"
        target = self.root / "existing-executable"
        source.write_bytes(b"#!/bin/sh\nexit 0\n")
        target.write_bytes(source.read_bytes())
        target.chmod(0o755)
        probe = pathlib.Path(__file__).with_name("Probe.lean").resolve()
        self.run_lake(self.first, "env", "lean", "--run", str(probe), "restore-exe",
                      str(self.root / "exe-cache"), str(source), str(target))
        self.assertTrue(os.access(target, os.X_OK))
        canonical = next((self.root / "exe-cache/artifacts").glob("*.exe"))
        self.assertEqual(target.stat().st_ino, canonical.stat().st_ino)


    def test_up_to_date_private_build_seeds_and_joins_native_store(self):
        private = dict(self.env, LAKE_SHARED_CACHE_ROOT="", LAKE_ARTIFACT_CACHE="0")
        self.run_lake(self.first, "build", "Example", env=private)
        self.run_lake(self.second, "build", "Example", env=private)
        first = self.first / ".lake/build/lib/lean/Example.olean"
        second = self.second / ".lake/build/lib/lean/Example.olean"
        self.assertNotEqual(first.stat().st_ino, second.stat().st_ino)
        self.run_lake(self.first, "build", "Example")
        self.run_lake(self.second, "build", "Example")
        self.assertEqual(first.stat().st_ino, second.stat().st_ino)


    def test_unwritable_shared_metadata_uses_private_cache(self):
        body = b"native fallback artifact"
        mapping = self.root / "mapping.jsonl"
        probe = pathlib.Path(__file__).with_name("Probe.lean").resolve()
        self.run_lake(self.first, "env", "lean", "--run", str(probe), "map", str(mapping), body.decode())
        selected = pathlib.Path(self.run_lake(self.first, "--shared-cache-dir").strip())
        outputs = selected / "outputs"
        outputs.mkdir(exist_ok=True)
        def permissions(mode):
            outputs.chmod(mode)
            for directory in outputs.rglob("*"):
                if directory.is_dir():
                    directory.chmod(mode)
        self.addCleanup(lambda: permissions(0o755))

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self):
                permissions(0o555)
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, *_):
                pass

        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        config = self.root / "services.toml"
        config.write_text('[[cache.service]]\nname = "fixture"\nkind = "s3"\n'
                          f'artifactEndpoint = "http://127.0.0.1:{server.server_port}"\n'
                          f'revisionEndpoint = "http://127.0.0.1:{server.server_port}"\n')
        try:
            self.run_lake(self.first, "cache", "get", str(mapping), "--service", "fixture", "--scope", "fixture", "--wfail",
                          env=dict(self.env, LAKE_CONFIG=str(config)))
        finally:
            server.shutdown()
            server.server_close()
            thread.join()
        payloads = list((self.root / "private/artifacts").glob("*.art"))
        self.assertEqual(len(payloads), 1)
        self.assertEqual(payloads[0].read_bytes(), body)
        self.assertEqual(self.run_lake(self.first, "--shared-cache-dir").strip(), "")
        self.run_lake(self.first, "build", "Example")


    def test_leantar_overwrite_does_not_modify_a_shared_inode(self):
        env = dict(self.env, LAKE_SHARED_CACHE_ROOT="", LAKE_ARTIFACT_CACHE="0")
        self.run_lake(self.first, "build", "+Example:ltar", env=env)
        original = self.first / ".lake/build/lib/lean/Example.olean"
        canonical = self.root / "canonical.olean"
        os.link(original, canonical)
        before = canonical.read_bytes()
        (self.second / "Example.lean").write_text("module\npublic def changed : Nat := 43\n")
        self.run_lake(self.second, "build", "+Example:ltar", env=env)
        archive = self.second / ".lake/build/ir/Example.ltar"
        result = subprocess.run([str(self.original.with_name("leantar")), "-f", "-x", "-j", "-"],
                                input=json.dumps([dict(file=str(archive), hash="0123456789abcdef",
                                                       base=[str(self.first / ".lake/build/lib/lean"),
                                                             str(self.first / ".lake/build/ir")])]),
                                cwd=self.first, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(canonical.read_bytes(), before)
        self.assertNotEqual(original.read_bytes(), before)
        self.assertNotEqual(original.stat().st_ino, canonical.stat().st_ino)


    def test_archive_disappearance_before_unpack_is_a_recoverable_miss(self):
        mapping = self.root / "outputs.jsonl"
        self.run_lake(self.first, "build", "+Example", "-o", str(mapping))
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
        if path.is_relative_to({str(self.root / "shared")!r}):
            path.unlink()
            pathlib.Path({str(marker)!r}).touch()
    raise SystemExit(subprocess.run([original, *sys.argv[1:]], input=data).returncode)
os.execv(original, [original, *sys.argv[1:]])
''')
        wrapper.chmod(0o755)
        self.run_lake(self.second, "build", "Example")
        self.assertTrue(marker.exists(), "build did not exercise shared archive unpack")
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
                                         str(pathlib.Path(__file__).resolve().parent.parent / "cacheEviction/pause_link.c"), "-ldl"], capture_output=True, text=True,
                                        env={k: v for k, v in os.environ.items() if k != "LD_LIBRARY_PATH"})
        self.assertEqual(compile_result.returncode, 0, compile_result.stderr)
        env = dict(self.env, LD_PRELOAD=str(library), TEST_CACHE_PREFIX=str(self.root / "shared"),
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
                shutil.rmtree(self.root / "shared")
            else:
                source.unlink()
        finally:
            (pause / "release").touch()
            output, _ = child.communicate(timeout=60)
        self.assertEqual(child.returncode, 0, output)
        self.assertTrue((self.second / ".lake/build/lib/lean/Example.olean").is_file())


if __name__ == "__main__":
    unittest.main()
