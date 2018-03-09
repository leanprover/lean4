/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import data.buffer data.dlist

inductive parse_result (α : Type)
| done (pos : ℕ) (result : α) : parse_result
| fail (pos : ℕ) (expected : dlist string) : parse_result

def parser (α : Type) :=
∀ (input : char_buffer) (start : ℕ), parse_result α

namespace parser
variables {α β γ : Type}

protected def bind (p : parser α) (f : α → parser β) : parser β :=
λ input pos, match p input pos with
| parse_result.done pos a           := f a input pos
| parse_result.fail ._ pos expected := parse_result.fail β pos expected
end

protected def pure (a : α) : parser α :=
λ input pos, parse_result.done pos a

private lemma parser.id_map (p : parser α) : parser.bind p parser.pure = p :=
begin
apply funext, intro input,
apply funext, intro pos,
dunfold parser.bind,
cases (p input pos); exact rfl
end

private lemma parser.bind_assoc (p : parser α) (q : α → parser β) (r : β → parser γ) :
  parser.bind (parser.bind p q) r = parser.bind p (λ a, parser.bind (q a) r) :=
begin
apply funext, intro input,
apply funext, intro pos,
dunfold parser.bind,
cases (p input pos); try {dunfold bind},
cases (q result input pos_1); try {dunfold bind},
all_goals {refl}
end

protected def fail (msg : string) : parser α :=
λ _ pos, parse_result.fail α pos (dlist.singleton msg)

instance : monad parser :=
{ pure := @parser.pure, bind := @parser.bind }

instance : is_lawful_monad parser :=
{ id_map := @parser.id_map,
  pure_bind := λ _ _ _ _, rfl,
  bind_assoc := @parser.bind_assoc }

instance : monad_fail parser :=
{ fail := @parser.fail, ..parser.monad }

protected def failure : parser α :=
λ _ pos, parse_result.fail α pos dlist.empty

protected def orelse (p q : parser α) : parser α :=
λ input pos, match p input pos with
| parse_result.fail ._ pos₁ expected₁ :=
  if pos₁ ≠ pos then parse_result.fail _ pos₁ expected₁ else
  match q input pos with
  | parse_result.fail ._ pos₂ expected₂ :=
    if pos₁ < pos₂ then
      parse_result.fail _ pos₁ expected₁
    else if pos₂ < pos₁ then
      parse_result.fail _ pos₂ expected₂
    else -- pos₁ = pos₂
      parse_result.fail _ pos₁ (expected₁ ++ expected₂)
  | ok := ok
  end
  | ok := ok
end

instance : alternative parser :=
{ failure := @parser.failure,
  orelse := @parser.orelse }

instance : inhabited (parser α) :=
⟨parser.failure⟩

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorate_errors (msgs : thunk (list string)) (p : parser α) : parser α :=
λ input pos, match p input pos with
| parse_result.fail ._ _ expected :=
  parse_result.fail _  pos (dlist.lazy_of_list (msgs ()))
| ok := ok
end

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorate_error (msg : thunk string) (p : parser α) : parser α :=
decorate_errors [msg ()] p

/-- Matches a single character satisfying the given predicate. -/
def sat (p : char → Prop) [decidable_pred p] : parser char :=
λ input pos,
if h : pos < input.size then
  let c := input.read ⟨pos, h⟩ in
  if p c then
    parse_result.done (pos+1) $ input.read ⟨pos, h⟩
  else
    parse_result.fail _ pos dlist.empty
else
  parse_result.fail _ pos dlist.empty

/-- Matches the empty word. -/
def eps : parser unit := return ()

/-- Matches the given character. -/
def ch (c : char) : parser unit :=
decorate_error c.to_string $ sat (= c) >> eps

/-- Matches a whole char_buffer.  Does not consume input in case of failure. -/
def char_buf (s : char_buffer) : parser unit :=
decorate_error s.to_string $ s.to_list.mmap' ch

/-- Matches one out of a list of characters. -/
def one_of (cs : list char) : parser char :=
decorate_errors (do c ← cs, return c.to_string) $
sat (∈ cs)

def one_of' (cs : list char) : parser unit :=
one_of cs >> eps

/-- Matches a string.  Does not consume input in case of failure. -/
def str (s : string) : parser unit :=
decorate_error s $ s.to_list.mmap' ch

/-- Number of remaining input characters. -/
def remaining : parser ℕ :=
λ input pos, parse_result.done pos (input.size - pos)

/-- Matches the end of the input. -/
def eof : parser unit :=
decorate_error "<end-of-file>" $
do rem ← remaining, guard $ rem = 0

def foldr_core (f : α → β → β) (p : parser α) (b : β) : ∀ (reps : ℕ), parser β
| 0 := failure
| (reps+1) := (do x ← p, xs ← foldr_core reps, return (f x xs)) <|> return b

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldr (f : α → β → β) (p : parser α) (b : β) : parser β :=
λ input pos, foldr_core f p b (input.size - pos + 1) input pos

def foldl_core (f : α → β → α) : ∀ (a : α) (p : parser β) (reps : ℕ), parser α
| a p 0 := failure
| a p (reps+1) := (do x ← p, foldl_core (f a x) p reps) <|> return a

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldl (f : α → β → α) (a : α) (p : parser β) : parser α :=
λ input pos, foldl_core f a p (input.size - pos + 1) input pos

/-- Matches zero or more occurrences of `p`. -/
def many (p : parser α) : parser (list α) :=
foldr list.cons p []

def many_char (p : parser char) : parser string :=
list.as_string <$> many p

/-- Matches zero or more occurrences of `p`. -/
def many' (p : parser α) : parser unit :=
many p >> eps

/-- Matches one or more occurrences of `p`. -/
def many1 (p : parser α) : parser (list α) :=
list.cons <$> p <*> many p

def many_char1 (p : parser char) : parser string :=
list.as_string <$> many1 p

/-- Matches one or more occurrences of `p`, separated by `sep`. -/
def sep_by1 (sep : parser unit) (p : parser α) : parser (list α) :=
list.cons <$> p <*> many (sep >> p)

/-- Matches zero or more occurrences of `p`, separated by `sep`. -/
def sep_by (sep : parser unit) (p : parser α) : parser (list α) :=
sep_by1 sep p <|> return []

def fix_core (F : parser α → parser α) : ∀ (max_depth : ℕ), parser α
| 0             := failure
| (max_depth+1) := F (fix_core max_depth)

/-- Fixpoint combinator satisfying `fix F = F (fix F)`. -/
def fix (F : parser α → parser α) : parser α :=
λ input pos, fix_core F (input.size - pos + 1) input pos

private def make_monospaced : char → char
| '\n' := ' '
| '\t' := ' '
| '\x0d' := ' '
| c := c

def mk_error_msg (input : char_buffer) (pos : ℕ) (expected : dlist string) : char_buffer :=
let left_ctx := (input.take pos).take_right 10,
    right_ctx := (input.drop pos).take 10 in
left_ctx.map make_monospaced ++ right_ctx.map make_monospaced ++ "\n".to_char_buffer ++
left_ctx.map (λ _, ' ') ++ "^\n".to_char_buffer ++
"\n".to_char_buffer ++
"expected: ".to_char_buffer
  ++ string.to_char_buffer (" | ".intercalate expected.to_list)
  ++ "\n".to_char_buffer

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run (p : parser α) (input : char_buffer) : sum string α :=
match (p <* eof) input 0 with
| parse_result.done pos res := sum.inr res
| parse_result.fail ._ pos expected :=
  sum.inl $ buffer.to_string $ mk_error_msg input pos expected
end

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run_string (p : parser α) (input : string) : sum string α :=
run p input.to_char_buffer

end parser
