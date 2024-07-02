def ackermann (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann n 1
  | .succ n, .succ m => ackermann n (ackermann (n + 1) m)
termination_by?
   --^ codeAction

-- Check hat we print this even if there is only one plausible measure
def onlyOneMeasure (n : Nat) := match n with
  | 0 => 0
  | .succ n => onlyOneMeasure n
termination_by?
   --^ codeAction

def anonymousMeasure : Nat → Nat
  | 0 => 0
  | .succ n => anonymousMeasure n
termination_by?
   --^ codeAction

-- Check hat we print this even if there is only one plausible measure
def onlyOneMeasureWF (n : Nat) := match n with
  | 0 => 0
  | .succ n => onlyOneMeasureWF n
termination_by?
   --^ codeAction
decreasing_by decreasing_tactic

def anonymousMeasureWF : Nat → Nat
  | 0 => 0
  | .succ n => anonymousMeasureWF n
termination_by?
   --^ codeAction
decreasing_by decreasing_tactic
