instance nat.decidable_ball (p : ℕ → Prop) [∀ i, decidable (p i)] : ∀ n, decidable (∀ x < n, p x)
| 0 := decidable.is_true begin intros n h, cases h end
| (n+1) :=
    match nat.decidable_ball n with
    | (decidable.is_false h) :=
        decidable.is_false begin
            intro h2, apply h,
            intros x hx, apply h2,
            apply nat.le_succ_of_le,
            assumption,
        end
    | (decidable.is_true h) :=
        if h' : p n then
            decidable.is_true begin
                intros x hx, cases hx,
                {assumption},
                {apply h, assumption},
            end
        else
            decidable.is_false begin
               intro hpx,
               apply h', apply hpx,
               constructor,
            end
    end

open expr tactic

instance decidable_dec_eq (p) : decidable_eq (decidable p) :=
by mk_dec_eq_instance

@[irreducible]
def is_ok {α : Type} [decidable_eq α] (a : α) : Prop := a = a

meta def get_const_def : expr → tactic expr
| (const c ls) := do
    d ← get_decl c,
    some v ← return $ d.instantiate_value_univ_params ls
        | fail $ "unknown declaration " ++ to_string c,
    return v
| _ := fail "get_const_def applied to non-constant"

@[reducible]
def {u} is_ok_handler (msg : thunk string) {α : Sort u} [decidable_eq α] (a b : α) : Prop :=
(if a = b then tt else trace (msg ()) ff : bool)

meta def mk_msg : list expr → tactic expr
| [] := return `("")
| (e::es) := (do
    let label := if e.is_local_constant then e.local_pp_name else `_,
    let label := label.to_string ++ "=",
    e' ← to_expr ``(to_string %%e),
    es' ← mk_msg es,
    return `(%%(reflect label) ++ %%e' ++ " " ++ %%es'))
<|> mk_msg es

meta def mk_checker_core : list expr → expr → tactic expr
| hs `(@is_ok %%α %%h %%a) := do
    v ← get_const_def (get_app_fn a),
    let lhs := a,
    let rhs := app_of_list v (get_app_args a),
    msg ← mk_msg (hs ++ [lhs,rhs]),
    to_expr ``(@is_ok_handler (λ _, %%msg) %%α %%h %%lhs %%rhs)
| hs (pi ppn bi dom b) := do
    x ← mk_local' ppn bi dom,
    b' ← mk_checker_core (hs ++ [x]) (b.instantiate_var x),
    return (pis [x] b')
| hs e := do e' ← pp e, fail $ to_fmt "mk_checker: unknown expression" ++ e'

meta def mk_checker := mk_checker_core []

meta def verify (p : Prop) [rp : reflected p] : tactic unit := do
prove_goal_async $ do
checker ← mk_checker rp,
program ← to_expr ``(%%checker : bool),
all_true ← eval_expr bool program,
triv,
when (¬ all_true) (do
    p' ← pp rp,
    fail $ to_fmt "verify failed on: " ++ p'),
trace "verified"

run_cmd verify $ ∀ x < 50, ∀ y < 50, is_ok $ nat.add x y
run_cmd verify $ ∀ x < 10, ∀ y < 10, is_ok $ nat.mul x y
run_cmd verify $ ∀ x < 50, ∀ y < 50, is_ok $ nat.sub x y
run_cmd verify $ ∀ x < 50, ∀ y < 50, is_ok $ nat.div x y
run_cmd verify $ ∀ x < 100, ∀ y < 100, is_ok $ nat.mod x y
run_cmd verify $ ∀ x < 100, ∀ y < 100, is_ok $ nat.gcd x y
run_cmd verify $ ∀ x < 50, ∀ y < 50, is_ok $ nat.decidable_eq x y
run_cmd verify $ ∀ x < 50, ∀ y < 50, is_ok $ nat.decidable_le x y
run_cmd verify $ ∀ x < 50, ∀ y < 50, is_ok $ nat.decidable_lt x y
run_cmd verify $ ∀ x < 200, is_ok $ nat.repr x
run_cmd verify $ ∀ x < 200, is_ok $ nat.bodd x
run_cmd verify $ ∀ x < 200, is_ok $ nat.div2 x
run_cmd verify $ ∀ x < 200, is_ok $ nat.bodd_div2 x
run_cmd verify $ ∀ x < 100, ∀ y < 40, is_ok $ nat.shiftl x y
run_cmd verify $ ∀ x < 100, ∀ y < 100, is_ok $ nat.shiftr x y
run_cmd verify $ ∀ x < 30, ∀ y < 30, is_ok $ nat.lor x y
run_cmd verify $ ∀ x < 30, ∀ y < 30, is_ok $ nat.land x y
run_cmd verify $ ∀ x < 30, ∀ y < 30, is_ok $ nat.ldiff x y
run_cmd verify $ ∀ x < 30, ∀ y < 30, is_ok $ nat.lxor x y
run_cmd verify $ ∀ x < 100, ∀ y < 10, is_ok $ nat.test_bit x y

def ints : list ℤ :=
(do i ← list.range 40, [-i, i]) ++
(do s ← [-1,1], j ← list.range 20, [s*(2^31:nat) + j-10])

def small_ints : list ℤ :=
(do i ← list.range 40, [-i, i])

run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.add x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.mul x y
run_cmd verify $ ∀ x ∈ ints, is_ok $ int.neg x
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.quot x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.rem x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.gcd x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.decidable_eq x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.decidable_le x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.decidable_lt x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ small_ints, is_ok $ int.shiftl x y

run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.lor x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.land x y
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.ldiff x y
run_cmd verify $ ∀ x ∈ ints, is_ok $ int.lnot x
run_cmd verify $ ∀ x ∈ ints, ∀ y ∈ ints, is_ok $ int.lxor x y
run_cmd verify $ ∀ x ∈ ints, ∀ y < 10, is_ok $ int.test_bit x y
