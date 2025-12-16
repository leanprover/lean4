import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

open Std.Internal.IO Async
open Std Http

/-- Test cancelling a slow request handler -/
def testCancelSlowHandler : IO Unit := do
  let res ← Async.block do
    let (client, server) ← Mock.new

    let ctx ← CancellationContext.new

    -- Start the server in the background
    let op := ContextAsync.background do
      Std.Http.Server.serveConnection server (fun _req => do
        -- Simulate a slow handler that should be cancelled
        Async.sleep 10000
        return Response.ok "should not complete"
      ) (config := { lingeringTimeout := 1000 }) |>.run

    -- Send a simple request
    client.send (String.toUTF8 "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")

    -- Wait a bit for the request to start processing
    Async.sleep 2000

    op ctx

    -- Cancel the context
    ctx.cancel .cancel

    -- Try to receive response - should get nothing or partial response
    -- The important thing is that the handler was cancelled
    client.recv?

  IO.println <| res.map (String.fromUTF8! · |>.quote)

/--
info: (some ("HTTP/1.1 408 Request Timeout\x0d\nContent-Length: 0\x0d\nconnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"))
-/
#guard_msgs in
#eval testCancelSlowHandler

/-- Test server shutdown during request processing -/
def testServerShutdownDuringRequest : IO Unit := do

  let res ← Async.block do
    let (client, server) ← Mock.new

    let ctx ← CancellationContext.new

    -- Start the server
    let op := ContextAsync.background do
      Std.Http.Server.serveConnection server (fun _req => do
        -- Handler that sleeps for a long time
        Async.sleep 100000
        return Response.ok "should not complete"
      ) (config := { lingeringTimeout := 3000 }) |>.run

    op.runIn ctx

    -- Send a request
    client.send (String.toUTF8 "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")


    -- Shutdown the server (simulating server shutdown)
    ctx.cancel .shutdown

    -- The connection should be terminated
    client.recv?

  IO.println <| res.map (String.fromUTF8! · |>.quote)

/--
info: (some ("HTTP/1.1 503 Service Unavailable\x0d\nContent-Length: 0\x0d\nconnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"))
-/
#guard_msgs in
#eval testServerShutdownDuringRequest

/-- Test cancelling during response streaming -/
def testCancelDuringStreaming : IO Unit := Async.block do
  let (client, server) ← Mock.new

  let ctx ← CancellationContext.new

  -- Start the server with a streaming handler
  background do
    Std.Http.Server.serveConnection server (fun _req => do
      Response.new
        |>.status .ok
        |>.stream (fun s => do
          -- Write some chunks
          for i in [0:100] do
            let ctx ← ContextAsync.getContext
            if ← ctx.isCancelled then
              -- Check if we were cancelled
              break
            s.writeChunk (Chunk.mk s!"chunk {i}\n".toUTF8 #[])
            Async.sleep 50
          s.close
        )
    ) (config := { lingeringTimeout := 3000 }) |>.run

  -- Send request
  client.send (String.toUTF8 "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")

  -- Wait for streaming to start
  Async.sleep 200

  -- Cancel while streaming
  ctx.cancel .cancel

  -- Try to receive remaining data
  let _ ← client.recv?

#eval testCancelDuringStreaming

/-- Test that CancellationContext.fork creates cancellable child contexts -/
def testContextFork : IO Unit := Async.block do
  let (client, server) ← Mock.new

  let parentCtx ← CancellationContext.new

  -- Start the server with forked contexts
  background do
    Std.Http.Server.serveConnection server (fun _req => do
      ContextAsync.fork do
        -- This runs in a forked context
        Async.sleep 10000
        return Response.ok "should not complete"
    ) (config := { lingeringTimeout := 3000 }) |>.run parentCtx

  -- Send request
  client.send (String.toUTF8 "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")

  -- Wait a bit
  Async.sleep 100

  -- Cancel parent context - should cancel forked child
  parentCtx.cancel .cancel

  let _ ← client.recv?

#eval testContextFork

/-- Test race with cancellation -/
def testRaceWithCancellation : IO Unit := Async.block do
  let (client, server) ← Mock.new

  let ctx ← CancellationContext.new

  -- Start server with a race condition
  background do
    Std.Http.Server.serveConnection server (fun _req => do
      -- Race two operations, one should win before cancellation
      ContextAsync.race
        (do Async.sleep 50; return Response.ok "fast")
        (do Async.sleep 10000; return Response.ok "slow")
    ) (config := { lingeringTimeout := 3000 }) |>.run

  -- Send request
  client.send (String.toUTF8 "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")

  -- Wait for the fast operation to complete
  Async.sleep 200

  -- The fast operation should have won
  let response ← client.recv?
  let responseData := String.fromUTF8! (response.getD .empty)

  -- Check that we got a response (not cancelled)
  if !responseData.contains "fast" then
    throw <| IO.userError s!"Expected response with 'fast', got: {responseData}"

#eval testRaceWithCancellation

/-- Test handler that checks for cancellation -/
def testHandlerChecksCancellation : IO Unit := Async.block do
  let (client, server) ← Mock.new

  let ctx ← CancellationContext.new

  -- Start server with handler that checks cancellation
  background do
    Std.Http.Server.serveConnection server (fun _req => do
      -- Loop that checks for cancellation
      for _ in [0:100] do
        if ← ContextAsync.isCancelled then
          -- Handler detected cancellation and exits early
          return Response.new |>.status .serviceUnavailable |>.body "cancelled"
        Async.sleep 50

      return Response.ok "completed"
    ) (config := { lingeringTimeout := 3000 }) |>.run

  -- Send request
  client.send (String.toUTF8 "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")

  -- Wait a bit
  Async.sleep 100

  -- Cancel
  ctx.cancel .cancel

  -- The handler should have detected cancellation
  let _ ← client.recv?

#eval testHandlerChecksCancellation

/-- Test multiple concurrent requests with cancellation -/
def testMultipleConcurrentRequestsWithCancel : IO Unit := Async.block do
  let (client1, server1) ← Mock.new
  let (client2, server2) ← Mock.new

  let ctx ← CancellationContext.new

  -- Start two server connections
  background do
    Std.Http.Server.serveConnection server1 (fun _req => do
      Async.sleep 10000
      return Response.ok "server1"
    ) (config := { lingeringTimeout := 3000 }) |>.run

  background do
    Std.Http.Server.serveConnection server2 (fun _req => do
      Async.sleep 10000
      return Response.ok "server2"
    ) (config := { lingeringTimeout := 3000 }) |>.run

  -- Send requests to both
  client1.send (String.toUTF8 "GET /1 HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")
  client2.send (String.toUTF8 "GET /2 HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")

  -- Wait a bit
  Async.sleep 100

  -- Cancel all - both should be cancelled
  ctx.cancel .cancel

  let _ ← client1.recv?
  let _ ← client2.recv?

#eval testMultipleConcurrentRequestsWithCancel

/-- Test deadline-based cancellation -/
def testDeadlineCancellation : IO Unit := Async.block do
  let (client, server) ← Mock.new

  let ctx ← CancellationContext.new

  -- Start server
  background do
    Std.Http.Server.serveConnection server (fun _req => do
      Async.sleep 10000
      return Response.ok "should timeout"
    ) (config := { lingeringTimeout := 3000 }) |>.run

  -- Send request
  client.send (String.toUTF8 "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")

  -- Wait a bit
  Async.sleep 100

  -- Cancel with deadline reason (simulating timeout)
  ctx.cancel .deadline

  -- Should get cancellation reason
  let reason ← ctx.getCancellationReason
  if reason != some .deadline then
    throw <| IO.userError s!"Expected deadline cancellation, got: {reason}"

  let _ ← client.recv?

#eval testDeadlineCancellation

/-- Test that completed requests don't get affected by cancellation -/
def testCompletedRequestNotAffected : IO Unit := Async.block do
  let (client, server) ← Mock.new

  let ctx ← CancellationContext.new

  -- Start server with fast handler
  background do
    Std.Http.Server.serveConnection server (fun _req => do
      -- Fast handler that completes before cancellation
      return Response.ok "completed"
    ) (config := { lingeringTimeout := 3000 }) |>.run

  -- Send request
  client.send (String.toUTF8 "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n")

  -- Wait for completion
  Async.sleep 200

  -- Get response before cancellation
  let response ← client.recv?
  let responseData := String.fromUTF8! (response.getD .empty)

  -- Now cancel (should not affect already completed request)
  ctx.cancel .cancel

  -- Verify we got the expected response
  if !responseData.contains "200 OK" then
    throw <| IO.userError s!"Expected 200 OK response, got: {responseData}"

#eval testCompletedRequestNotAffected
