-- Some of these tests made more sense when we had a
-- derive_functional_induction command.

#check doesNotExist.induct

def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  foo 0 #[]
where
  foo (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get i h
      if p a then
        foo (i+1) (r.push a)
      else
        r
    else
      r
  termination_by as.size - i

-- Checks the error message when the users tries to access the induct rule for the wrong function
-- (before we used reserved names for this feature we did give a more helpful error message here)
#check takeWhile.induct

#check takeWhile.foo.induct


-- this tests the error we get when trying to access the induct rules for
-- a function that recurses over an inductive *predicate* (not yet supported)

inductive Even : Nat → Prop where
| zero : Even 0
| plus2 : Even n → Even (n + 2)

def idEven : Even n → Even n
| .zero => .zero
| .plus2 p => .plus2 (idEven p)

#check idEven.induct

-- this tests the error we get when trying to access the induct rules for
-- a function that recurses over `Acc`

def idAcc : Acc p x → Acc p x
  | Acc.intro x f => Acc.intro x (fun y h => idAcc (f y h))
#check idAcc.induct
