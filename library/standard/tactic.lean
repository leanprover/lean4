import logic

-- This is just a trick to embed the 'tactic language' as a
-- Lean expression. We should view (tactic A) as automation
-- that when execute produces a term of type A.
-- tactic_value is just a "dummy" for creating the "fake"
inductive tactic (A : Type) : Type :=
| tactic_value {} : tactic A
-- Remark the following names are not arbitrary, the tactic module
-- uses them when converting Lean expressions into actual tactic objects.
-- The bultin 'by' construct triggers the process of converting a
-- a term of type (tactic A) into a tactic that sythesizes a term
-- of type A
definition then_tac   {A : Type} (t1 t2 : tactic A) : tactic A := tactic_value
definition orelse_tac {A : Type} (t1 t2 : tactic A) : tactic A := tactic_value
definition repeat_tac {A : Type} (t : tactic A) : tactic A := tactic_value
definition now_tac    {A : Type} : tactic A := tactic_value
definition exact_tac  {A : Type} : tactic A := tactic_value
definition state_tac  {A : Type} : tactic A := tactic_value
definition fail_tac   {A : Type} : tactic A := tactic_value
definition id_tac     {A : Type} : tactic A := tactic_value
definition beta_tac   {A : Type} : tactic A := tactic_value
definition apply      {A : Type} {B : Type} (b : B) : tactic A := tactic_value
definition unfold_tac {A : Type} {B : Type} (b : B) : tactic A := tactic_value

infixl `;`:200         := then_tac
infixl `|`:100         := orelse_tac
notation `!`:max t:max := repeat_tac t


