import UserEnvPlugin
import Lean.Elab.Command

run_cmd IO.println <| valExt.getState (← Lean.getEnv)
