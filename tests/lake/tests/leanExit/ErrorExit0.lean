def bad : Nat := "not a Nat"

-- The diagnostics of `bad` are emitted by the driver's asynchronous reporting
-- loop (`SnapshotTree.runAndReport`), which races with a process exit
-- triggered while elaborating. Give the reporting loop a chance to flush
-- before exiting so that the `Type mismatch` diagnostic reliably reaches
-- Lake's captured output.
#eval show IO Unit from do
  IO.sleep 500
  IO.Process.exit 0
