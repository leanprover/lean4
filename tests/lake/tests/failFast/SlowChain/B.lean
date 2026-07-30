-- This module imports SlowChain.A.
-- After cancellation (triggered by Fail1/Fail2), SlowChain.A still compiles
-- successfully (it's already in-flight). Once A finishes, the mapM task chain
-- checks the cancellation token and short-circuits, so B is never compiled.
import SlowChain.A
