namespace SlimCheck

inductive TestResult (p : Prop) where
  | success : PSum Unit p → TestResult p
  | gaveUp : Nat → TestResult p
  | failure : ¬ p → List String → Nat → TestResult p
  deriving Inhabited

/-- Configuration for testing a property. -/
structure Configuration where
  numInst : Nat := 100
  maxSize : Nat := 100
  numRetries : Nat := 10
  traceDiscarded : Bool := false
  traceSuccesses : Bool := false
  traceShrink : Bool := false
  traceShrinkCandidates : Bool := false
  randomSeed : Option Nat := none
  quiet : Bool := false
  deriving Inhabited

abbrev Rand := Id

abbrev Gen (α : Type u) := ReaderT (ULift Nat) Rand α

/-- `Testable p` uses random examples to try to disprove `p`. -/
class Testable (p : Prop) where
  run (cfg : Configuration) (minimize : Bool) : Gen (TestResult p)

def NamedBinder (_n : String) (p : Prop) : Prop := p

namespace TestResult

def isFailure : TestResult p → Bool
  | failure _ _ _ => true
  | _ => false

end TestResult

namespace Testable

open TestResult

def runProp (p : Prop) [Testable p] : Configuration → Bool → Gen (TestResult p) := Testable.run

variable {var : String}

def addShrinks (n : Nat) : TestResult p → TestResult p
  | TestResult.failure p xs m => TestResult.failure p xs (m + n)
  | p => p

instance [Pure m] : Inhabited (OptionT m α) := ⟨(pure none : m (Option α))⟩

class Shrinkable (α : Type u) where
  shrink : (x : α) → List α := fun _ ↦ []

class SampleableExt (α : Sort u) where
  proxy : Type v
  [proxyRepr : Repr proxy]
  [shrink : Shrinkable proxy]
  sample : Gen proxy
  interp : proxy → α

partial def minimizeAux [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] (cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (n : Nat) :
    OptionT Gen (Σ x, TestResult (β (SampleableExt.interp x))) := do
  let candidates := SampleableExt.shrink.shrink x
  for candidate in candidates do
    let res ← OptionT.lift <| Testable.runProp (β (SampleableExt.interp candidate)) cfg true
    if res.isFailure then
      if cfg.traceShrink then
        pure () -- slimTrace s!"{var} shrunk to {repr candidate} from {repr x}"
      let currentStep := OptionT.lift <| pure <| Sigma.mk candidate (addShrinks (n + 1) res)
      let nextStep := minimizeAux cfg var candidate (n + 1)
      return ← (nextStep <|> currentStep)
  failure
