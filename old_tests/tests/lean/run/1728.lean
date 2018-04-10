structure Bijection ( U V : Type ) :=
  ( morphism : U → V )
  ( inverse  : V → U )
  ( witness_1 : ∀ u : U, inverse (morphism u) = u )
  ( witness_2 : ∀ v : V, morphism (inverse v) = v )

class Finite ( α : Type ) :=
  ( cardinality : nat )
  ( bijection : Bijection α (fin cardinality) )

lemma empty_exfalso (x : false) : empty := begin exfalso, trivial end

instance empty_is_Finite : Finite empty := {
  cardinality := 0,
  bijection := begin
                 split,
                 intros,
                 induction u,
                 intros,
                 induction v,
                 trace_state,
                 cases v_is_lt,
                 repeat {admit}
              end
}
