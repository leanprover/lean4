/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.format
import init.meta.expr
import init.category.state
import init.data.string
import init.data.list.instances

import init.native.ir
import init.native.format
import init.native.internal
import init.native.anf
import init.native.cf
import init.native.pass
import init.native.util
import init.native.config
import init.native.result

namespace native
inductive error : Type
| string : string → error
| many   : list error → error

meta def error.to_string : error → string
| (error.string s) := s
| (error.many es) := to_string $ list.map error.to_string es

meta def arity_map : Type :=
  rb_map name nat

meta def get_arity : expr → nat
| (expr.lam _ _ _ body) := 1 + get_arity body
| _ := 0

@[reducible] def ir_result (A : Type*) :=
native.result error A

meta def mk_arity_map : list (name × expr) → arity_map
| [] := rb_map.mk name nat
| ((n, body) :: rest) := rb_map.insert (mk_arity_map rest) n (get_arity body)

@[reducible] meta def ir_compiler_state :=
  (config × arity_map × nat)

@[reducible] meta def ir_compiler (A : Type) :=
  native.resultT (state ir_compiler_state) error A

meta def lift {A} (action : state ir_compiler_state A) : ir_compiler A :=
⟨fmap (fun (a : A), native.result.ok a) action⟩

meta def trace_ir (s : string) : ir_compiler unit := do
  (conf, map, counter) ← lift $ state.read,
  if config.debug conf
  then trace s (fun u, return ())
  else return ()

-- An `exotic` monad combinator that accumulates errors.
meta def run {M E A} (res : native.resultT M E A) : M (native.result E A) :=
  match res with
  | ⟨action⟩ := action
  end

meta def sequence_err : list (ir_compiler format) → ir_compiler (list format × list error)
| [] := return ([], [])
| (action :: remaining) :=
    ⟨ fun s,
       match (run (sequence_err remaining)) s with
       | (native.result.err e, s') := (native.result.err e, s)
       | (native.result.ok (res, errs), s') :=
         match (run action) s' with
         | (native.result.err e, s'') := (native.result.ok (res, e :: errs), s'')
         | (native.result.ok v, s'') := (native.result.ok (v :: res, errs), s'')
         end
         end
     ⟩

-- meta lemma sequence_err_always_ok :
--   forall xs v s s', sequence_err xs s = native.result.ok (v, s') := sorry

meta def lift_result {A} (action : ir_result A) : ir_compiler A :=
  ⟨fun s, (action, s)⟩

-- TODO: fix naming here
private meta def take_arguments' : expr → list name → (list name × expr)
| (expr.lam n _ _ body) ns := take_arguments' body (n :: ns)
| e' ns := (ns, e')

meta def fresh_name : ir_compiler name := do
  (conf, map, counter) ← lift state.read,
  let fresh := name.mk_numeral (unsigned.of_nat counter) `native._ir_compiler_
  in do
    lift $ state.write (conf, map, counter + 1),
    return fresh

meta def take_arguments (e : expr) : ir_compiler (list name × expr) :=
let (arg_names, body) := take_arguments' e [] in do
  fresh_names ← monad.mapm (fun x, fresh_name) arg_names,
  let locals := list.map mk_local fresh_names in
  return $ (fresh_names, expr.instantiate_vars body (list.reverse locals))

-- meta def lift_state {A} (action : state arity_map A) : ir_compiler A :=
--   fun (s : arity_map), match action s with
--   | (a, s) := (return a, s)
--   end

meta def mk_error {T} : string → ir_compiler T :=
  fun s, do
  trace_ir "CREATEDERROR",
  lift_result (native.result.err $ error.string s)

meta def lookup_arity (n : name) : ir_compiler nat := do
  (_, map, counter) ← lift state.read,
  if n = `nat.cases_on
  then pure 2
  else
  match rb_map.find map n with
  | option.none := mk_error $ "could not find arity for: " ++ to_string n
  | option.some n := return n
  end

meta def mk_nat_literal (n : nat) : ir_compiler ir.expr :=
  return (ir.expr.lit $ ir.literal.nat n)

def repeat {A : Type} : nat → A → list A
| 0 _ := []
| (n + 1) a := a :: repeat n a

def zip {A B : Type} : list A → list B → list (A × B)
| [] [] := []
| [] (y :: ys) := []
| (x :: xs) [] := []
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys

private def upto' : ℕ → list ℕ
| 0 := []
| (n + 1) := n :: upto' n

def upto (n : ℕ) : list ℕ :=
  list.reverse $ upto' n

def label {A : Type} (xs : list A) : list (nat × A) :=
  zip (upto (list.length xs)) xs

-- lemma label_size_eq :
--   forall A (xs : list A),
--   list.length (label xs) = list.length xs :=
-- begin
--   intros,
--   induction xs,
--   apply sorry
--   apply sorry
-- end

-- HELPERS --
meta def assert_name : ir.expr → ir_compiler name
| (ir.expr.locl n) := lift_result $ native.result.ok n
| e := mk_error $ "expected name found: " ++ to_string (format_cpp.expr e)

meta def assert_expr : ir.stmt → ir_compiler ir.expr
| (ir.stmt.e exp) := return exp
| s := mk_error ("internal invariant violated, found: " ++ (to_string (format_cpp.stmt s)))

meta def mk_call (head : name) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do
    args' ← monad.sequence args'',
    return (ir.expr.call head args')

meta def mk_under_sat_call (head : name) (args : list ir.expr) : ir_compiler ir.expr :=
let args'' := list.map assert_name args in do
    args' ← monad.sequence args'',
    return $ ir.expr.mk_native_closure head args'

meta def bind_value_with_ty (val : ir.expr) (ty : ir.ty) (body : name → ir_compiler ir.stmt) : ir_compiler ir.stmt := do
  fresh ← fresh_name,
  ir.stmt.letb fresh ty val <$> (body fresh)

meta def bind_value (val : ir.expr) (body : name → ir_compiler ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty val ir.ty.object body

-- not in love with this --solution-- hack, revisit
meta def compile_local (n : name) : ir_compiler name :=
return $ (mk_str_name "_$local$_" (name.to_string_with_sep "_" n))

meta def mk_invoke (loc : name) (args : list ir.expr) : ir_compiler ir.expr :=
let args'' := list.map assert_name args
in do
  args' ← monad.sequence args'',
  loc' ← compile_local loc,
  lift_result (native.result.ok $ ir.expr.invoke loc' args')

meta def mk_over_sat_call (head : name) (fst snd : list ir.expr) : ir_compiler ir.expr :=
let fst' := list.map assert_name fst,
    snd' := list.map assert_name snd in do
  args' ← monad.sequence fst',
  args'' ← monad.sequence snd',
  fresh ← fresh_name,
  locl ← compile_local fresh,
  invoke ← ir.stmt.e <$> (mk_invoke fresh (fmap ir.expr.locl args'')),
  return $ ir.expr.block (ir.stmt.seq [
    ir.stmt.letb locl ir.ty.object (ir.expr.call head args') ir.stmt.nop,
    invoke
  ])

meta def is_return (n : name) : bool :=
decidable.to_bool $ `native_compiler.return = n

meta def compile_call (head : name) (arity : nat) (args : list ir.expr) : ir_compiler ir.expr := do
  trace_ir $ "compile_call: " ++ (to_string head),
  if list.length args = arity
  then mk_call head args
  else if list.length args < arity
  then mk_under_sat_call head args
  else mk_over_sat_call head (list.taken arity args) (list.dropn arity args)

meta def mk_object (arity : unsigned) (args : list ir.expr) : ir_compiler ir.expr :=
  let args'' := list.map assert_name args
  in do args' ← monad.sequence args'',
        lift_result (native.result.ok $ ir.expr.mk_object (unsigned.to_nat arity) args')

meta def one_or_error (args : list expr) : ir_compiler expr :=
match args with
| ((h : expr) :: []) := lift_result $ native.result.ok h
| _ := mk_error "internal invariant violated, should only have one argument"
end

meta def panic (msg : string) : ir_compiler ir.expr :=
  return $ ir.expr.panic msg

-- END HELPERS --

meta def bind_case_fields' (scrut : name) : list (nat × name) → ir.stmt → ir_compiler ir.stmt
| [] body := return body
| ((n, f) :: fs) body := do
  loc ← compile_local f,
  ir.stmt.letb f ir.ty.object (ir.expr.project scrut n) <$> (bind_case_fields' fs body)

meta def bind_case_fields (scrut : name) (fs : list name) (body : ir.stmt) : ir_compiler ir.stmt :=
  bind_case_fields' scrut (label fs) body

meta def mk_cases_on (case_name scrut : name) (cases : list (nat × ir.stmt)) (default : ir.stmt) : ir.stmt :=
ir.stmt.seq [
  ir.stmt.letb `ctor_index ir.ty.int (ir.expr.call `cidx [scrut]) ir.stmt.nop,
  ir.stmt.switch `ctor_index cases default
]

meta def compile_cases (action : expr → ir_compiler ir.stmt) (scrut : name)
: list (nat × expr) → ir_compiler (list (nat × ir.stmt))
| [] := return []
| ((n, body) :: cs) := do
  (fs, body') ← take_arguments body,
  body'' ← action body',
  cs' ← compile_cases cs,
  case ← bind_case_fields scrut fs body'',
  return $ (n, case) :: cs'

meta def compile_cases_on_to_ir_expr
    (case_name : name)
    (cases : list expr)
    (action : expr → ir_compiler ir.stmt) : ir_compiler ir.expr := do
    default ← panic "default case should never be reached",
    match cases with
    | [] := mk_error $ "found " ++ to_string case_name ++ "applied to zero arguments"
    | (h :: cs) := do
      ir_scrut ← action h >>= assert_expr,
      ir.expr.block <$> bind_value ir_scrut (fun scrut, do
        cs' ← compile_cases action scrut (label cs),
        return (mk_cases_on case_name scrut cs' (ir.stmt.e default)))
    end

meta def bind_builtin_case_fields' (scrut : name) : list (nat × name) → ir.stmt → ir_compiler ir.stmt
| [] body := return body
| ((n, f) :: fs) body := do
  loc ← compile_local f,
  ir.stmt.letb loc ir.ty.object (ir.expr.project scrut n) <$> (bind_builtin_case_fields' fs body)

meta def bind_builtin_case_fields (scrut : name) (fs : list name) (body : ir.stmt) : ir_compiler ir.stmt :=
bind_builtin_case_fields' scrut (label fs) body

meta def compile_builtin_cases (action : expr → ir_compiler ir.stmt) (scrut : name)
  : list (nat × expr) → ir_compiler (list (nat × ir.stmt))
| [] := return []
| ((n, body) :: cs) := do
  (fs, body') ← take_arguments body,
  body'' ← action body',
  cs' ← compile_builtin_cases cs,
  case ← bind_builtin_case_fields scrut fs body'',
  return $ (n, case) :: cs'

meta def in_lean_ns (n : name) : name :=
  mk_simple_name ("lean::" ++ name.to_string_with_sep "_" n)

meta def mk_builtin_cases_on (case_name scrut : name) (cases : list (nat × ir.stmt)) (default : ir.stmt) : ir.stmt :=
-- replace `ctor_index with a generated name
ir.stmt.seq [
  ir.stmt.letb `buffer ir.ty.object_buffer ir.expr.uninitialized ir.stmt.nop,
  ir.stmt.letb `ctor_index ir.ty.int (ir.expr.call (in_lean_ns case_name) [scrut, `buffer]) ir.stmt.nop,
  ir.stmt.switch `ctor_index cases default
]

meta def compile_builtin_cases_on_to_ir_expr
(case_name : name)
(cases : list expr)
(action : expr → ir_compiler ir.stmt) : ir_compiler ir.expr := do
default ← panic "default case should never be reached",
match cases with
| [] := mk_error $ "found " ++ to_string case_name ++ "applied to zero arguments"
| (h :: cs) := do
  ir_scrut ← action h >>= assert_expr,
  ir.expr.block <$> bind_value ir_scrut (fun scrut, do
    cs' ← compile_builtin_cases action scrut (label cs),
    return (mk_builtin_cases_on case_name scrut cs' (ir.stmt.e default)))
end

meta def mk_is_simple (scrut : name) : ir.expr :=
  ir.expr.call `is_simple [scrut]

meta def mk_is_zero (n : name) : ir.expr :=
  ir.expr.equals (ir.expr.raw_int 0) (ir.expr.locl n)

meta def mk_cidx (obj : name) : ir.expr :=
  ir.expr.call `cidx [obj]

-- we should add applicative brackets
meta def mk_simple_nat_cases_on (scrut : name) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty (mk_cidx scrut) (ir.ty.name `int) (fun cidx,
    bind_value_with_ty (mk_is_zero cidx) (ir.ty.name `bool) (fun is_zero,
    pure $ ir.stmt.ite is_zero zero_case succ_case))

meta def mk_mpz_nat_cases_on (scrut : name) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
  ir.stmt.e <$> panic "mpz"

meta def mk_nat_cases_on (scrut : name) (zero_case succ_case : ir.stmt) : ir_compiler ir.stmt :=
  bind_value_with_ty (mk_is_simple scrut) (ir.ty.name `bool) (fun is_simple,
    ir.stmt.ite is_simple <$>
      mk_simple_nat_cases_on scrut zero_case succ_case <*>
      mk_mpz_nat_cases_on scrut zero_case succ_case)

meta def assert_two_cases (cases : list expr) : ir_compiler (expr × expr) :=
  match cases with
  | c1 :: c2 :: _ := return (c1, c2)
  | _ := mk_error "nat.cases_on should have exactly two cases"
  end

meta def mk_vm_nat (n : name) : ir.expr :=
  ir.expr.call (in_lean_ns `mk_vm_simple) [n]

meta def compile_succ_case (action : expr → ir_compiler ir.stmt) (scrut : name) (succ_case : expr) : ir_compiler ir.stmt := do
  (fs, body') ← take_arguments succ_case,
  body'' ← action body',
  match fs with
  | pred :: _ := do
    loc ← compile_local pred,
    fresh ← fresh_name,
    bind_value_with_ty (mk_cidx scrut) (ir.ty.name `int) (fun cidx,
      bind_value_with_ty (ir.expr.sub (ir.expr.locl cidx) (ir.expr.raw_int 1)) (ir.ty.name `int) (fun sub,
      pure $ ir.stmt.letb loc ir.ty.object (mk_vm_nat sub) body''
    ))
  | _ := mk_error "compile_succ_case too many fields"
  end

meta def compile_nat_cases_on_to_ir_expr
(case_name : name)
(cases : list expr)
(action : expr → ir_compiler ir.stmt) : ir_compiler ir.expr :=
  match cases with
  | [] := mk_error $ "found " ++ to_string case_name ++ "applied to zero arguments"
  | (h :: cs) := do
    ir_scrut ← action h >>= assert_expr,
    (zero_case, succ_case) ← assert_two_cases cs,
    trace_ir (to_string zero_case),
    trace_ir (to_string succ_case),
    ir.expr.block <$> bind_value ir_scrut (fun scrut, do
      zc ← action zero_case,
      sc ← compile_succ_case action scrut succ_case,
      mk_nat_cases_on scrut zc sc
    )
  end

            -- this→emit_indented("if (is_simple(");
            -- action(scrutinee);
            -- this→emit_string("))");
            -- this→emit_block([&] () {
            --     this→emit_indented("if (cidx(");
            --     action(scrutinee);
            --     this→emit_string(") == 0) ");
            --     this→emit_block([&] () {
            --         action(zero_case);
            --         *this→m_output_stream << ";\n";
            --     });
            --     this→emit_string("else ");
            --     this→emit_block([&] () {
            --         action(succ_case);
            --         *this→m_output_stream << ";\n";
            --     });
            -- });
            -- this→emit_string("else ");
            -- this→emit_block([&] () {
            --     this→emit_indented("if (to_mpz(");
            --     action(scrutinee);
            --     this→emit_string(") == 0) ");
            --     this→emit_block([&] () {
            --         action(zero_case);
            --         *this→m_output_stream << ";\n";
            --     });
            --     this→emit_string("else ");
            --     this→emit_block([&] () {
            --         action(succ_case);
            --     });
            -- });

-- this code isnt' great working around the semi-functional frontend
meta def compile_expr_app_to_ir_expr
  (head : expr)
  (args : list expr)
  (action : expr → ir_compiler ir.stmt) : ir_compiler ir.expr := do
    trace_ir (to_string head  ++ to_string args),
    if expr.is_constant head = bool.tt
    then (if is_return (expr.const_name head)
    then do
      rexp ← one_or_error args,
      (ir.expr.block ∘ ir.stmt.return) <$> ((action rexp) >>= assert_expr)
    else if is_nat_cases_on (expr.const_name head)
    then compile_nat_cases_on_to_ir_expr (expr.const_name head) args action
    else match is_internal_cnstr head with
    | option.some n := do
      args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
      mk_object n args'
    | option.none := match is_internal_cases head with
    | option.some n := compile_cases_on_to_ir_expr (expr.const_name head) args action
    | option.none := match get_builtin (expr.const_name head) with
      | option.some builtin :=
        match builtin with
        | builtin.vm n := mk_error "vm"
        | builtin.cfun n arity := do
          args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
          compile_call n arity args'
        | builtin.cases n arity :=
          compile_builtin_cases_on_to_ir_expr (expr.const_name head) args action
        end
      | option.none := do
        args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
        arity ← lookup_arity (expr.const_name head),
        compile_call (expr.const_name head) arity args'
      end
    end end)
    else if expr.is_local_constant head
    then do
      args' ← monad.sequence $ list.map (fun x, action x >>= assert_expr) args,
      mk_invoke (expr.local_uniq_name head) args'
    else (mk_error ("unsupported call position" ++ (to_string head)))

meta def compile_expr_macro_to_ir_expr (e : expr) : ir_compiler ir.expr :=
  match native.get_nat_value e with
  | option.none := mk_error "unsupported macro"
  | option.some n := mk_nat_literal n
  end

meta def compile_expr_to_ir_expr (action : expr → ir_compiler ir.stmt): expr → ir_compiler ir.expr
| (expr.const n ls) :=
  match native.is_internal_cnstr (expr.const n ls) with
  | option.none :=
    -- TODO, do I need to case on arity here? I should probably always emit a call
    match get_builtin n with
    | option.some (builtin.cfun n' arity) :=
      compile_call n arity []
    | _ :=
      if n = "_neutral_"
      then (pure $ ir.expr.mk_object 0 [])
      else do
        arity ← lookup_arity n,
        compile_call n arity []
    end
  | option.some arity := pure $ ir.expr.mk_object (unsigned.to_nat arity) []
  end
| (expr.var i) := mk_error "there should be no bound variables in compiled terms"
| (expr.sort _) := mk_error "found sort"
| (expr.mvar _ _) := mk_error "unexpected meta-variable in expr"
| (expr.local_const n _ _ _) := ir.expr.locl <$> compile_local n
| (expr.app f x) :=
  let head := expr.get_app_fn (expr.app f x),
      args := expr.get_app_args (expr.app f x)
  in compile_expr_app_to_ir_expr head args action
| (expr.lam _ _ _ _) := mk_error "found lam"
| (expr.pi _ _ _ _) := mk_error "found pi"
| (expr.elet n _ v body) := mk_error "internal error: can not translate let binding into a ir_expr"
| (expr.macro d sz args) := compile_expr_macro_to_ir_expr (expr.macro d sz args)

meta def compile_expr_to_ir_stmt : expr → ir_compiler ir.stmt
| (expr.pi _ _ _ _) := mk_error "found pi, should not be translating a Pi for any reason (yet ...)"
| (expr.elet n _ v body) := do
  n' ← compile_local n,
  v' ← compile_expr_to_ir_expr compile_expr_to_ir_stmt v,
  -- this is a scoping fail, we need to fix how we compile locals
  body' ← compile_expr_to_ir_stmt (expr.instantiate_vars body [mk_local n]),
  -- not the best solution, here need to think hard about how to prevent thing, more aggressive anf?
  match v' with
  | ir.expr.block stmt := return (ir.stmt.seq [ir.stmt.letb n' ir.ty.object ir.expr.uninitialized ir.stmt.nop, body'])
  | _ := return (ir.stmt.letb n' ir.ty.object v' body')
  end
| e' := ir.stmt.e <$> compile_expr_to_ir_expr compile_expr_to_ir_stmt e'

meta def compile_defn_to_ir (decl_name : name) (args : list name) (body : expr) : ir_compiler ir.defn := do
  body' ← compile_expr_to_ir_stmt body,
  let params := (zip args (repeat (list.length args) (ir.ty.ref ir.ty.object))) in
  pure (ir.defn.mk decl_name params ir.ty.object body')

def unwrap_or_else {T R : Type} : ir_result T → (T → R) → (error → R) → R
| (native.result.err e) f err := err e
| (native.result.ok t) f err := f t

meta def replace_main (n : name) : name :=
     if n = `main
     then "___lean__main"
     else n

meta def trace_expr (e : expr) : ir_compiler unit :=
  trace ("trace_expr: " ++ to_string e) (fun u, return ())

meta def compile_defn (decl_name : name) (e : expr) : ir_compiler format :=
  let arity := get_arity e in do
    (args, body) ← take_arguments e,
    ir ← compile_defn_to_ir (replace_main decl_name) args body,
    return $ format_cpp.defn ir

meta def compile' : list (name × expr) → list (ir_compiler format)
| [] := []
| ((n, e) :: rest) := do
  let decl := (fun d, d ++ format.line ++ format.line) <$> compile_defn n e
  in decl :: (compile' rest)

meta def format_error : error → format
| (error.string s) := to_fmt s
| (error.many es) := format_concat (list.map format_error es)

meta def mk_lean_name (n : name) : ir.expr :=
  ir.expr.constructor (in_lean_ns `name) (name.components n)

meta def emit_declare_vm_builtins : list (name × expr) → ir_compiler (list ir.stmt)
| [] := return []
| ((n, body) :: es) := do
  vm_name ← pure $ (mk_lean_name n),
  tail ← emit_declare_vm_builtins es,
  fresh ← fresh_name,
  let cpp_name := in_lean_ns `name,
    single_binding := ir.stmt.seq [
    ir.stmt.letb fresh (ir.ty.name cpp_name) vm_name ir.stmt.nop,
    ir.stmt.e $ ir.expr.assign `env (ir.expr.call `add_native [`env, fresh, replace_main n])
 ] in return $ single_binding :: tail

meta def emit_main (procs : list (name × expr)) : ir_compiler ir.defn := do
  builtins ← emit_declare_vm_builtins procs,
  arity ← lookup_arity `main,
  vm_simple_obj ← fresh_name,
  call_main ← compile_call "___lean__main" arity [ir.expr.locl vm_simple_obj],
  return (ir.defn.mk `main [] ir.ty.int $ ir.stmt.seq ([
    ir.stmt.e $ ir.expr.call (in_lean_ns `initialize) [],
    ir.stmt.letb `env (ir.ty.name (in_lean_ns `environment)) ir.expr.uninitialized ir.stmt.nop
  ] ++ builtins ++ [
    ir.stmt.letb `ios (ir.ty.name (in_lean_ns `io_state)) (ir.expr.call (in_lean_ns `get_global_ios) []) ir.stmt.nop,
    ir.stmt.letb `opts (ir.ty.name (in_lean_ns `options)) (ir.expr.call (in_lean_ns `get_options_from_ios) [`ios]) ir.stmt.nop,
    ir.stmt.letb `S (ir.ty.name (in_lean_ns `vm_state)) (ir.expr.constructor (in_lean_ns `vm_state) [`env, `opts]) ir.stmt.nop,
    ir.stmt.letb `scoped (ir.ty.name (in_lean_ns `scope_vm_state)) (ir.expr.constructor (in_lean_ns `scope_vm_state) [`S]) ir.stmt.nop,
    ir.stmt.e $ ir.expr.assign `g_env (ir.expr.address_of `env),
    ir.stmt.letb vm_simple_obj ir.ty.object (ir.expr.mk_object 0 []) ir.stmt.nop,
    ir.stmt.e call_main
]))

  --   -- call_mains
  --   -- buffer<expr> args;
  --   -- auto unit = mk_neutral_expr();
  --   -- args.push_back(unit);
  --   -- // Make sure to invoke the C call machinery since it is non-deterministic
  --   -- // which case we enter here.
  --   -- compile_to_c_call(main_fn, args, 0, name_map<unsigned>());
  --   -- *this→m_output_stream << ";\n return 0;\n}" << std::endl;
  -- ]

meta def unzip {A B} : list (A × B) → (list A × list B)
| [] := ([], [])
| ((x, y) :: rest) :=
  let (xs, ys) := unzip rest
  in (x :: xs, y :: ys)

meta def configuration : ir_compiler config := do
  (conf, _, _) ← lift $ state.read,
  pure conf

meta def apply_pre_ir_passes (procs : list procedure) (conf : config) : list procedure :=
  run_passes conf [anf, cf] procs

meta def driver (procs : list (name × expr)) : ir_compiler (list format × list error) := do
  procs' ← apply_pre_ir_passes procs <$> configuration,
  (fmt_decls, errs) ← sequence_err (compile' procs'),
  main ← emit_main procs',
  return (format_cpp.defn main :: fmt_decls, errs)

meta def compile (conf : config) (procs : list (name × expr)) : format :=
  let arities := mk_arity_map procs in
  -- Put this in a combinator or something ...
  match run (driver procs) (conf, arities, 0) with
  | (native.result.err e, s) := error.to_string e
  | (native.result.ok (decls, errs), s) :=
    if list.length errs = 0
    then format_concat decls
    else format_error (error.many errs)
  end

-- meta def compile (procs : list (name))
end native
