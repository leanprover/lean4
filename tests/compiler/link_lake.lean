-- this should be sufficient to trigger linking against Lake's initializer symbols
-- TODO: uncomment the following line. We commented it to avoid a test failure on Windows.
-- Windows does not allow shared objects with more 2^16 exported symbols :(

-- import Lake
--
def main : IO Unit :=
  return
