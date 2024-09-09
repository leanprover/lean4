import Lean

/-!
# Testing performance of wide and deeply nested structures instantiated with `with`

This test uses a macro to generate a structure with `depth` nested structures and `width` fields
   at each level. The structure is initialized with `val : α` at every field using the `with` construction pattern.
```
  structure A0 extends A1 where
  ...
  def a0 : A0 := { a1 with xm_1 := val, ..., xm_(width) := val}
  def a'0: A0 := { a'1 with ...}
  ...
  structure A(depth) extends Base where
  ...
  structure Base where
    base_1 : α
    ...
  ---
  def base : Base := ⟨val, ..., val⟩
```
  The test is then
```
  set_option maxHeartbeats 200 in
  example : a0 = a'0 := rfl
```
  As this type of unification occurs over and over and over when type checking declarations, it needs
  to be and stay fast. Before #2478, this test took over 700 heartbeats.
-/

open Lean Parser Command

def mkIdent' (s : String) (i : Nat) := mkIdent <| Name.mkSimple <| s++s!"{i}"

def mkFieldsStx (type : TSyntax `ident) (s : String) (width : Nat) : MacroM (TSyntax ``structFields) :=
  go type s width []
where go (type : TSyntax `ident) (s : String) (width : Nat)
    (binds : List <| TSyntax ``structExplicitBinder) : MacroM (TSyntax ``structFields) := do
  match width with
  | 0 => `(structFields| $binds.reverse.toArray*)
  | m+1 =>
    let new ← `(structExplicitBinder| ($(mkIdent' s m) : $type))
    go type s m (new::binds)

def baseIdent := mkIdent (Name.mkSimple "base")

def baseTypeIdent := mkIdent (Name.mkSimple "Base")

def init (type val : TSyntax `ident) (width : Nat) : MacroM (TSyntax `command) := do
  let fieldsStx ← mkFieldsStx type "base_" width
  let vals := Array.mkArray width val
  `(structure $baseTypeIdent where
    $fieldsStx:structFields
    def $baseIdent : $baseTypeIdent := ⟨$vals,*⟩)

def mkStructAndInstStx (type val : TSyntax `ident) (width depth: Nat) : MacroM <| TSyntax `command := do
  let init ← init type val width
  go val width depth #[init]
where go (val : TSyntax `ident) (width depth : Nat) (cmds : Array <| TSyntax `command) :
    MacroM <| TSyntax `command := do
  match depth with
  | 0 =>
    let cmd : TSyntax `command := ⟨mkNullNode cmds⟩
    `($cmd:command)
  | m+1 =>
    let len := cmds.toList.length
    let newTerm (s : String) := if len = 1 then baseTypeIdent else mkIdent' s (m+1)
    let newTerm' (s : String) := if len = 1 then baseIdent else mkIdent' s (m+1)
    let fieldsStx ← mkFieldsStx type (s!"x{m}_") width
    let nextStruct ←
      `(structure $(mkIdent' "A" m) extends $(newTerm "A") where
        $fieldsStx:structFields)
    let structVals ← (List.range width).mapM fun j =>
      `(Term.structInstField| $(mkIdent' s!"x{m}_" j):ident := $val)
    -- Note here we index backwards to `A0` is the deepest structure with terms `a0` and `a'0`
    let nextStructInst ←
      `(def $(mkIdent' "a" m) : $(mkIdent' "A" m) := { $(newTerm' "a"):ident with $structVals.toArray,* })
    let nextStructInst' ←
      `(def $(mkIdent' "a'" m) : $(mkIdent' "A" m) := { $(newTerm' "a'"):ident with $structVals.toArray,* })
    let newCmd : TSyntax `command ←
      `($nextStruct:command
        $nextStructInst
        $nextStructInst')
    go val width m (cmds.push newCmd)

/-- We build a structure with `depth` nested structures and `width` fields at each level.
    The structure is initialized with `val` at every field using the `with` construction pattern. -/
macro "deep_wide_struct_inst_with" type:ident val:ident depth:num width:num : command =>
  mkStructAndInstStx type val width.getNat depth.getNat

def foo : String := "foo"

deep_wide_struct_inst_with String foo 50 20

/-
Structure instances using the `with` pattern should be fast.
Without #2478, this takes over 700 heartbeats in the elaborator.

Remark: we are now propagating heartbeats to the kernel, and
had to increase it value to 1000
 -/
set_option maxHeartbeats 1000 in
example : a0 = a'0 := rfl
