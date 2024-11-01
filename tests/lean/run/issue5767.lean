axiom Std.HashMap : Type
axiom Std.HashMap.insert : Std.HashMap → Std.HashMap
axiom Std.HashMap.get? : Std.HashMap → Int → Option Unit

structure St where
  m : Unit
  map : Std.HashMap

opaque P : St → Prop

noncomputable
def go1 (ss : Int) (st0 : St) : Bool :=
        let st1 := { st0 with map := st0.map.insert }
        match st1.map.get? ss with
        | some _ =>
          have : P st1 := sorry
          have : P st1 := sorry
          go1 ss st1
        | none => true
      termination_by st0
      decreasing_by sorry

/--
info: go1.induct (ss : Int) (motive : St → Prop)
  (case1 :
    ∀ (x : St),
      let st1 := { m := x.m, map := x.map.insert };
      ∀ (val : Unit), st1.map.get? ss = some val → P st1 → P st1 → motive st1 → motive x)
  (case2 :
    ∀ (x : St),
      let st1 := { m := x.m, map := x.map.insert };
      st1.map.get? ss = none → motive x)
  (st0 : St) : motive st0
-/
#guard_msgs in
#check go1.induct


-- the above was the original bugreport, and a (spurious) mdata around the match
-- triggered a bug and looking through it solved it. But that would just hide it, and it
-- can be triggered like this:

noncomputable
def go2 (ss : Int) (st0 : St) : Bool :=
        let st1 := { st0 with map := st0.map.insert }
        id <| match st1.map.get? ss with -- the ss argument is needed
          | some _ =>
            have : P st1 := sorry -- both needed
            have : P st1 := sorry -- both needed
            go2 ss st1
          | none => true
      termination_by st0
      decreasing_by sorry

/--
info: go2.induct : Int →
  ∀ (motive : St → Prop),
    (∀ (x : St),
        let st1 := { m := x.m, map := x.map.insert };
        motive st1 → motive x) →
      ∀ (st0 : St), motive st0
-/
#guard_msgs in
#check @go2.induct
