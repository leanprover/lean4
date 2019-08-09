import init.lean.parser
import init.lean.parser.transform
open Lean
open Lean.Parser

def getAtomTrailingSpace : Syntax → Nat
| Syntax.atom (some info) _ => info.trailing.stopPos - info.trailing.startPos
| _ => 0

def getMinTrailingSpace (ps : Array Syntax) (i : Nat) : Nat :=
ps.foldl (fun acc (p : Syntax) =>
  let space : Nat :=
    match p.getTailInfo with
    | some info => info.trailing.stopPos - info.trailing.startPos
    | none => 0;
  if space < acc then space else acc)
  100000

def reduceTrailingSpace : Syntax → Nat → Syntax
| Syntax.atom (some info) val, delta => Syntax.atom (some { trailing := { stopPos := info.trailing.stopPos - delta, .. info.trailing }, .. info }) val

| stx, _ => stx

partial def fixPats : Array Syntax → Nat → Array Syntax
| ps, i =>
  let minSpace := getMinTrailingSpace ps i;
  if minSpace <= 1 then
    ps
  else
    let delta := minSpace - 1;
    ps.map $ fun p => p.modifyArg i $ fun pat =>
      match pat.getTailInfo with
      | some info => pat.setTailInfo (some { trailing := { stopPos := info.trailing.stopPos - delta, .. info.trailing } , .. info })
      | none => pat

def fixEqnSyntax (stx : Syntax) : Syntax :=
stx.rewriteBottomUp $ fun stx =>
  stx.ifNodeKind `Lean.Parser.Command.declValEqns
    (fun stx =>
      stx.val.modifyArg 0 $ fun altsStx =>
      altsStx.modifyArgs $ fun alts =>
        let pats    := alts.map $ fun alt => alt.getArg 1;
        let patSize := (pats.get 0).getArgs.size;
        let pats    := fixPats pats (patSize - 1);
        alts.mapIdx $ fun i alt => alt.setArg 1 (pats.get i))
    (fun _ => stx)

def main (xs : List String) : IO Unit :=
do
[fname] ← pure xs | throw (IO.userError "usage `patch <file-name>`");
env ← mkEmptyEnvironment;
stx ← parseFile env fname;
let stx := fixEqnSyntax stx;
match stx.reprint with
| some out => IO.print out
| none     => throw (IO.userError "failed to reprint")
