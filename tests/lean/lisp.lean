import init.lean.parser.macro init.lean.parser.identifier system.io
import .macro1

attribute [instance] lean.name.has_lt_quick
open lean.parser
open lean.parser.parser_t

def test {α} [decidable_eq α] (p : parser α) (s : string) (e : α) : io unit :=
match parse p s with
| except.ok a    := if a = e then return () else io.print_ln "unexpected result"
| except.error e := io.print_ln (e.to_string s)

def test_failure {α} (p : parser α) (s : string) : io unit :=
match parse p s with
| except.ok a    := io.print_ln "unexpected success"
| except.error e := return ()

def show_result {α} [has_to_string α] (s : string) (p : except message α) : io unit :=
match p with
| except.ok a    := io.print_ln "result: " >> io.print_ln (to_string a)
| except.error e := io.print_ln (e.to_string s)

namespace lean.parser.syntax.combinators
variables {m : Type → Type} [monad m]

def ident : parser_t m syntax :=
do start ← pos,
   n ← identifier,
   stop ← pos,
   whitespace,
   pure $ syntax.ident ⟨some ⟨start, stop⟩, n, none, none⟩

def sym (sym : string) : parser_t m syntax :=
do start ← pos,
   str sym,
   stop ← pos,
   whitespace,
   pure $ syntax.atom ⟨some ⟨start, stop⟩, atomic_val.string sym⟩

def num : parser_t m syntax :=
do start ← pos,
   n ← parser_t.num,
   stop ← pos,
   whitespace,
   pure $ syntax.atom ⟨some ⟨start, stop⟩, atomic_val.number n⟩

def node (n : name) (ps : list (parser_t m syntax)) : parser_t m syntax :=
do args ← ps.mmap id,
   pure $ syntax.node ⟨n, args⟩

def many (p : parser_t m syntax) : parser_t m syntax :=
do args ← many p,
   pure $ syntax.node ⟨name.anonymous, args⟩

def wrap_with_node (n : name) (stx : syntax) : syntax :=
syntax.node ⟨n, [stx]⟩

end lean.parser.syntax.combinators

namespace lisp
open lean.parser
open lean.parser.syntax.combinators

abbreviation read_m := parser syntax
abbreviation ws {m} [monad m] : parser_t m unit := whitespace

def parse_list (parse : read_m) : read_m :=
(node `list [sym "(", many parse, sym ")"] <|>
 node `list [sym "[", many parse, sym "]"]) <?> "list"

def parse : ℕ → read_m
| 0 := unexpected "nesting limit exceeded"
| (n+1) := ident <|> num <|> parse_list (parse n)

def let_macro := {macro .
  name := `let,
  expand := some $ λ node,
  match node.args with
  | [syntax.node ⟨name.anonymous, clauses⟩, body] :=
    do clauses ← clauses.mmap (λ cl, match cl with
         | syntax.node ⟨name.anonymous, [v, e]⟩ := some (v, e)
         | stx                                  := none),
       let ⟨vars, exprs⟩ := clauses.unzip,
       syntax.node {macro := `let_core, args := [
         syntax.node ⟨name.anonymous, exprs⟩,
         syntax.node {macro := `bind, args := [
           syntax.node {macro := name.anonymous, args := vars},
           body
         ]}
       ]}
  | _ := none}

def mk_list_stx (args : list syntax) : syntax :=
syntax.node ⟨`list, [
  syntax.atom ⟨none, atomic_val.string "("⟩,
  syntax.node ⟨name.anonymous, args⟩,
  syntax.atom ⟨none, atomic_val.string ")"⟩]⟩

def mk_ident (n : name) : syntax :=
syntax.ident ⟨none, n, none, none⟩

def match_list_stx : syntax → option (list syntax)
| (syntax.node ⟨`list, [lp, syntax.node ⟨name.anonymous, args⟩, rp]⟩) := some args
| _ := none

/- From "Macros that Work Together" -/
def or_macro := {macro .
  name := `or,
  expand := some $ λ n,
  -- '(or e1 e2)'
  do [e1, e2] ← pure n.args | none,
     -- '(let ([tmp e1]) (if tmp tmp e2))'
     mk_list_stx [
       mk_ident `let,
       mk_list_stx [mk_list_stx [mk_ident `tmp, e1]],
       mk_list_stx [mk_ident `if, mk_ident `tmp, mk_ident `tmp, e2]]}

/-- Recognizes and translates calls to built-in macros -/
def list_macro := {macro .
  name := `list,
  expand := some $ λ n,
  match match_list_stx (syntax.node n) with
  | some [syntax.ident {name := `lambda, ..}, vars, body] :=
    do vars ← match_list_stx vars,
       syntax.node ⟨`lambda, [syntax.node ⟨name.anonymous, vars⟩, body]⟩
  | some (syntax.ident {name := `or, ..}::args) :=
    syntax.node ⟨`or, args⟩
  | some (syntax.ident {name := `if, ..}::args) :=
    syntax.node ⟨`if, args⟩
  | some [syntax.ident {name := `let, ..}, clauses, body] :=
    do clauses ← match_list_stx clauses,
       clauses ← clauses.mmap (λ cl, match match_list_stx cl with
         | some cl := some $ syntax.node ⟨name.anonymous, cl⟩
         | none := none),
       syntax.node ⟨`let, [syntax.node ⟨name.anonymous, clauses⟩, body]⟩
  | _ := none}

inductive value
| number (n : nat)
| list (l : list value)
| closure (env : list value) (code : syntax)

-- TODO(Sebastian): shouldn't be meta
meta def value.to_string : value → string
| (value.number n) := to_string n
| (value.list l)   := (l.map (λ v, value.to_string v)).to_string
| (value.closure _ _) := "#<function>"

meta def eval : nat → syntax → list value → except string value
| _        (syntax.atom ⟨_, atomic_val.number n⟩) env := except.ok $ value.number n
| _        (syntax.ident {res := some {decl := sum.inl idx, ..}, ..}) env :=
(match env.nth idx with
| some v := except.ok v
| none   := throw "aaah")
| _        (syntax.node ⟨`lambda_core, [syntax.node ⟨`bind, [_, body]⟩]⟩) env :=
  except.ok $ value.closure env body
| (fuel+1) (syntax.node ⟨`let_core, [syntax.node ⟨_, [expr]⟩, syntax.node ⟨`bind, [_, body]⟩]⟩) env :=
do v ← eval fuel expr env,
   eval fuel body (v::env)
| (fuel+1) (syntax.node ⟨`if, [cond, t, e]⟩) env :=
do cond ← eval fuel cond env,
   eval fuel (match cond with
     | value.number 0 := e
     | value.list []  := e
     | _              := t) env
| (fuel+1) (syntax.node ⟨`list, [lp, syntax.node ⟨_, f::args⟩, rp]⟩) env :=
do f ← eval fuel f env,
   args.mfoldl (λ f arg,
   do value.closure cenv code ← pure f |
        throw $ "not a function: " ++ f.to_string,
      arg ← eval fuel arg env,
      eval fuel code (arg::cenv)) f
| _        stx env := throw $ "cannot evaluate " ++ to_string stx

def cfg := {macro1.cfg with macros :=
  ((macro1.cfg.macros.insert `list list_macro)
   .insert `let let_macro)
  .insert `or or_macro}
meta def go (s) : tactic unit :=
match ((parse 1000).parse_with_eoi s).run with
| except.error e := tactic.trace (e.to_string s)
| except.ok stx  :=
tactic.trace (to_fmt "reader:   " ++ to_fmt stx) >>
match (expand' stx).run' cfg () with
| except.error e := tactic.fail e
| except.ok stx  :=
tactic.trace (to_fmt "expander: " ++ to_fmt stx) >>
match (resolve' stx).run' cfg () with
| except.error e := tactic.fail e
| except.ok stx  :=
tactic.trace (to_fmt "resolver: " ++ to_fmt stx) >>
match eval 1000 stx [] with
| except.error e := tactic.fail e
| except.ok val  :=
tactic.trace (to_fmt "evaluator: " ++ val.to_string)


#eval go "()"
#eval go "((lambda [x] x) 1)"
#eval go "((lambda [x y] x) 1 2)"
#eval go "(let ([x 1]) x)"

#eval go "(let ([tmp 5]) (or 0 tmp))"

end lisp
