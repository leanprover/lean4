inductive Exp
  | hole
  | var (i : UInt32)
  | app (a b : Exp)
with
  /-- Computes the hash -/ @[simp, computed_field] protected hash : Exp → UInt64
    | .var i => Hashable.hash i
    | .app a b => mixHash a.hash b.hash
    | .hole => 32

def dagLikeTerm : Nat → Exp
  | 0 => .app (.var 42) .hole
  | n+1 => .app (dagLikeTerm n) (dagLikeTerm n)

#eval (dagLikeTerm 1000).hash -- memoized

def varNum? : Exp → Option UInt32
  | .var i => i
  | _ => none

example : varNum? (.var 32) = some 32 := by native_decide





namespace WithIndices

inductive B.C (α : Type u) : Nat → Type u
  | a : C α 0
  | b (c : C α n) {d : C α (n-1)} : C α (n+1)
with
  @[computed_field] hash : ∀ α i, C α i → UInt64
    | _, _, .a => 1
    | _, _, .b c => 42 + c.hash

#eval (B.C.b (α := Nat) (.a) (d := .a)).hash

end WithIndices






namespace Mutual

mutual
  inductive A
    | a (b : B)
    | b (b : B)
  with
    @[computed_field] f : A → Nat
      | .a c => 32 + c.f
      | .b c => 42 + 2*c.f

  inductive B
    | c (a : A)
    | d
  with
    @[computed_field] f : B → Nat
      | .c a => a.f
      | .d => 0
end

#eval (B.c (.a .d)).f

end Mutual

