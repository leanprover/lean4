/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Util.Profiler
public import Std.Http
import Init.System.Platform
import Init.System.IO

/-!
# Trace profiler HTTP server

Serves a Firefox Profiler-compatible profile over HTTP on an ephemeral local port and open the
corresponding `https://profiler.firefox.com/from-url/...` URL in the user's default browser, so the
profile is loaded with a single command (a la `samply`).
-/

namespace Lean.Firefox

open Std Async Http

/-- Best-effort: spawn the platform-specific "open this URL in the default browser" command. -/
def openInBrowser (url : String) : IO Unit := do
  let args : IO.Process.SpawnArgs :=
    if System.Platform.isWindows then
      { cmd := "cmd", args := #["/c", "start", "", url] }
    else if System.Platform.isOSX then
      { cmd := "open", args := #[url] }
    else
      { cmd := "xdg-open", args := #[url] }
  try
    let child ← IO.Process.spawn { args with stdout := .null, stderr := .null, stdin := .null }
    discard child.wait
  catch _ =>
    -- Browser launch is opportunistic; the URL is also printed for the user to copy.
    pure ()

/--
Serve the JSON-encoded `profile` over HTTP on an ephemeral `127.0.0.1` port and open it in the
user's default browser via `https://profiler.firefox.com`. Shuts down once the profile has been
fetched (reloads inside the viewer are not supported); the user can also Ctrl+C as usual.
-/
public def Profile.serve (profile : String) : IO Unit := Async.block do
  let done ← IO.Promise.new
  let handler := Server.Handler.ofFn fun _req => do
    let r ← Response.ok
      |>.header! "Access-Control-Allow-Origin" "*"
      |>.json profile
    done.resolve ()
    return r
  let addr : Net.SocketAddress := .v4 (.mk (.ofParts 127 0 0 1) 0)
  let server ← Server.serve addr handler
  let some localAddr := server.localAddr
    | throw <| IO.userError "trace.profiler.serve: server did not report a bound address"
  let profileUrl := s!"http://127.0.0.1:{localAddr.port}/profile.json"
  let encodedProfileUrl := profileUrl.replace ":" "%3A" |>.replace "/" "%2F"
  let viewerUrl := s!"https://profiler.firefox.com/from-url/{encodedProfileUrl}/"
  IO.eprintln s!"trace.profiler: serving profile at {profileUrl}"
  IO.eprintln s!"trace.profiler: opening {viewerUrl}"
  -- Open the browser without blocking the server loop.
  let _ ← IO.asTask (prio := .dedicated) (openInBrowser viewerUrl)
  -- Wait for initial (and only) request
  let _ ← Async.ofAsyncTask (.ofPurePromise done)
  -- The handler signals `doneCh` before the response body is written; brief pause so the writer
  -- can drain before `shutdownAndWait` cancels its task.
  Async.sleep 200
  server.shutdownAndWait
