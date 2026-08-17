-- This module takes ~3 seconds to elaborate.
-- It is used to test that importing modules are not compiled after cancellation.
#eval IO.sleep 3000
