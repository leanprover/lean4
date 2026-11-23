import Std.Tactic.BVDecide

set_option trustCompiler true
/-
source: Examples/Ivy/SuzukiKasami.lean
vc: rcv_privilege_unique_tokens
epr: false
epr_info: not EPR: sort dependency graph has a cycle (edges: node → seq_t, seq_t → seq_t)
non_core_constants: none
standalone_check: ok
-/

open Classical in
theorem rcv_privilege_unique_tokens
    : ∀ (node seq_t : Type) (n : node) (t : seq_t)
        (st_n_have_privilege st_n_requesting : node → Bool) (st_n_token_seq : node → seq_t)
        (st_reqs : node → node → seq_t → Bool) (st_t_for : seq_t → node → Bool)
        (st_crit : node → Bool) (seq_le : seq_t → seq_t → Prop),
      (∀ (x_1 : seq_t), seq_le x_1 x_1)
        → (∀ (x_2 y_1 z : seq_t), seq_le x_2 y_1 → seq_le y_1 z → seq_le x_2 z)
        → (∀ (x_3 y_2 : seq_t), seq_le x_3 y_2 → seq_le y_2 x_3 → x_3 = y_2)
        → (∀ (x_4 y_3 : seq_t), seq_le x_4 y_3 ∨ seq_le y_3 x_4)
        → ∀ (seq_lt : seq_t → seq_t → Prop),
          (∀ (x_6 y_5 : seq_t), seq_lt x_6 y_5 ↔ seq_le x_6 y_5 ∧ x_6 ≠ y_5)
            → ∀ (seq_next : seq_t → seq_t → Prop),
              (∀ (x_8 y_7 : seq_t),
                  seq_next x_8 y_7
                    ↔ seq_lt x_8 y_7 ∧ ∀ (z_1 : seq_t), seq_lt x_8 z_1 → seq_le y_7 z_1)
                → ∀ (seq_zero : seq_t),
                  (∀ (x_9 : seq_t), seq_le seq_zero x_9)
                    → (∀ (N M : node), st_crit N = Bool.true ∧ st_crit M = Bool.true → N = M)
                    → (∀ (N_1 M_1 : node),
                      st_n_have_privilege N_1 = Bool.true ∧ st_n_have_privilege M_1 = Bool.true
                        → N_1 = M_1)
                    → (∀ (N_2 : node),
                      st_crit N_2 = Bool.true
                        → st_n_have_privilege N_2 = Bool.true ∧ st_n_requesting N_2 = Bool.true)
                    → (∀ (I : seq_t) (N_3 M_2 : node),
                      st_t_for I N_3 = Bool.true ∧ st_t_for I M_2 = Bool.true → N_3 = M_2)
                    → (∀ (N_4 : node),
                      st_n_token_seq N_4 ≠ seq_zero → st_t_for (st_n_token_seq N_4) N_4 = Bool.true)
                    → (∀ (N_5 M_3 : node),
                      st_n_have_privilege N_5 = Bool.true ∧ N_5 ≠ M_3
                        → seq_lt (st_n_token_seq M_3) (st_n_token_seq N_5))
                    → (∀ (N_6 : node) (I_1 : seq_t) (M_4 : node),
                      st_n_have_privilege N_6 = Bool.true ∧ st_t_for I_1 M_4 = Bool.true
                        → seq_le I_1 (st_n_token_seq N_6))
                    → (∀ (N_7 M_5 : node) (I_2 : seq_t),
                      st_reqs N_7 M_5 I_2 = Bool.true → N_7 ≠ M_5)
                    → (∀ (I_3 : seq_t) (N_8 : node) (J : seq_t) (M_6 : node),
                      st_t_for I_3 N_8 = Bool.true ∧ seq_next J I_3 ∧ st_t_for J M_6 = Bool.true
                        → N_8 ≠ M_6)
                    → (∀ (I_4 : seq_t) (N_9 : node) (J_1 : seq_t) (M_7 : node),
                      st_t_for I_4 N_9 = Bool.true ∧ st_t_for J_1 M_7 = Bool.true ∧ seq_lt I_4 J_1
                        → seq_le I_4 (st_n_token_seq N_9))
                    → st_t_for t n = Bool.true → seq_lt (st_n_token_seq n) t
                    → ∀ (I_5 : seq_t) (N_10 M_8 : node),
                      st_t_for I_5 N_10 = Bool.true → st_t_for I_5 M_8 = Bool.true
                        → N_10 = M_8 := by
  epr (cegarRounds := 1000)
