#lang lean4
import Lean.Server
#eval Lean.Server.Test.runWithInputFile "./edits_client.log" none -- The builtin search path seems to be fine
