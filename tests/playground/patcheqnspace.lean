import init.lean.parser
import init.lean.parser.transform
open Lean
open Lean.Parser

def getAtomTrailingSpace : Syntax → Nat
| Syntax.atom (some info) _ => info.trailing.stopPos - info.trailing.startPos
| _ => 0

def getMinTrailingSpace (ps : Array Syntax) (i : Nat) : Nat :=
ps.foldl (fun acc (p : Syntax) =>
  let space := getAtomTrailingSpace (p.getArg i);
  if space < acc then space else acc)
  100000

def reduceTrailingSpace : Syntax → Nat → Syntax
| Syntax.atom (some info) val, delta => Syntax.atom (some { trailing := { stopPos := info.trailing.stopPos - delta, .. info.trailing }, .. info }) val

| stx, _ => stx

partial def fixPats : Array Syntax → Nat → Nat → Array Syntax
| ps, i, sz =>
  if i < sz then
    let minSpace := getMinTrailingSpace ps i;
    if minSpace <= 1 then
      fixPats ps (i+2) sz
    else
      let ps := ps.map $ fun p => p.modifyArg i $ fun comma => reduceTrailingSpace comma (minSpace - 1);
      fixPats ps (i+2) sz
  else
    ps

def fixEqnSyntax (stx : Syntax) : Syntax :=
stx.rewriteBottomUp $ fun stx =>
  stx.ifNodeKind `Lean.Parser.Command.declValEqns
    (fun stx =>
      stx.val.modifyArg 0 $ fun altsStx =>
      altsStx.modifyArgs $ fun alts =>
        let pats    := alts.map $ fun alt => alt.getArg 1;
        let patSize := (pats.get 0).getArgs.size;
        let pats    := fixPats pats 1 patSize;
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
