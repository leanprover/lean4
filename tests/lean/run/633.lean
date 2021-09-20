abbrev semantics (α:Type) := StateM (List Nat) α

inductive expression : Nat → Type
| const : (n : Nat) → expression n

def uext {w:Nat} (x: expression w) (o:Nat) : expression w := expression.const w
def eval {n : Nat} (v:expression n) : semantics (expression n) := pure (expression.const n)
def set_overflow {w : Nat} (e : expression w) : semantics Unit := pure ()

structure instruction :=
  (mnemonic:String)
  (patterns:List Nat)

def definst (mnem:String) (body: expression 8 -> semantics Unit) : instruction :=
{ mnemonic := mnem
, patterns := ((body (expression.const 8)).run []).snd.reverse
}

def mul : instruction := do -- this is a "pure" do block (as in it is the Id monad)
 definst "mul" $ fun (src : expression 8) =>
    let action : semantics Unit := do -- this is not "pure" do block
      let tmp <- eval $ uext src 16
      set_overflow $ tmp
    action

def mul' : instruction := do -- this is a "pure" do block (as in it is the Id monad)
 definst "mul" $ fun (src : expression 8) =>
    let rec action : semantics Unit := do -- this is not "pure" do block
      let tmp <- eval $ uext src 16
      set_overflow $ tmp
    action

def mul'' : instruction := do -- this is a "pure" do block (as in it is the Id monad)
 definst "mul" $ fun (src : expression 8) =>
    let action : semantics (expression 8) :=
      return (<- eval $ uext src 16)
    pure ()
