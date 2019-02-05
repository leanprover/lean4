/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.coe init.data.uint init.data.to_string
import init.lean.format init.data.hashable
namespace lean

inductive name
| anonymous  : name
| mk_string  : name → string → name
| mk_numeral : name → nat → name

instance : inhabited name :=
⟨name.anonymous⟩

def mk_str_name (p : name) (s : string) : name :=
name.mk_string p s

def mk_num_name (p : name) (v : nat) : name :=
name.mk_numeral p v

def mk_simple_name (s : string) : name :=
mk_str_name name.anonymous s

instance string_to_name : has_coe string name :=
⟨mk_simple_name⟩

namespace name
private def hash_aux : name → usize → usize
| anonymous        r := r
| (mk_string n s)  r := hash_aux n (mix_hash r (hash s))
| (mk_numeral n k) r := hash_aux n (mix_hash r (hash k))

-- TODO: mark as opaque and builtin, and add as builtin
protected def hash (n : name) : usize :=
hash_aux n 11

instance : hashable name :=
⟨name.hash⟩

def get_prefix : name → name
| anonymous        := anonymous
| (mk_string p s)  := p
| (mk_numeral p s) := p

def update_prefix : name → name → name
| anonymous        new_p := anonymous
| (mk_string p s)  new_p := mk_string new_p s
| (mk_numeral p s) new_p := mk_numeral new_p s


def components' : name -> list name
| anonymous                := []
| (mk_string n s)          := mk_string anonymous s :: components' n
| (mk_numeral n v)         := mk_numeral anonymous v :: components' n

def components (n : name) : list name :=
n.components'.reverse

protected def dec_eq : Π a b : name, decidable (a = b)
| anonymous          anonymous          := is_true rfl
| (mk_string p₁ s₁)  (mk_string p₂ s₂)  :=
  if h₁ : s₁ = s₂ then
    match dec_eq p₁ p₂ with
    | is_true h₂  := is_true $ h₁ ▸ h₂ ▸ rfl
    | is_false h₂ := is_false $ λ h, name.no_confusion h $ λ hp hs, absurd hp h₂
  else is_false $ λ h, name.no_confusion h $ λ hp hs, absurd hs h₁
| (mk_numeral p₁ n₁) (mk_numeral p₂ n₂) :=
  if h₁ : n₁ = n₂ then
    match dec_eq p₁ p₂ with
    | is_true h₂  := is_true $ h₁ ▸ h₂ ▸ rfl
    | is_false h₂ := is_false $ λ h, name.no_confusion h $ λ hp hs, absurd hp h₂
  else is_false $ λ h, name.no_confusion h $ λ hp hs, absurd hs h₁
| anonymous          (mk_string _ _)    := is_false $ λ h, name.no_confusion h
| anonymous          (mk_numeral _ _)   := is_false $ λ h, name.no_confusion h
| (mk_string _ _)    anonymous          := is_false $ λ h, name.no_confusion h
| (mk_string _ _)    (mk_numeral _ _)   := is_false $ λ h, name.no_confusion h
| (mk_numeral _ _)   anonymous          := is_false $ λ h, name.no_confusion h
| (mk_numeral _ _)   (mk_string _ _)    := is_false $ λ h, name.no_confusion h

instance : decidable_eq name :=
{dec_eq := name.dec_eq}

protected def append : name → name → name
| n anonymous := n
| n (mk_string p s) :=
  mk_string (append n p) s
| n (mk_numeral p d) :=
  mk_numeral (append n p) d

instance : has_append name :=
⟨name.append⟩

def replace_prefix : name → name → name → name
| anonymous anonymous new_p := new_p
| anonymous _         _     := anonymous
| n@(mk_string p s) query_p new_p :=
  if n = query_p then
    new_p
  else
    mk_string (p.replace_prefix query_p new_p) s
| n@(mk_numeral p s) query_p new_p :=
  if n = query_p then
    new_p
  else
    mk_numeral (p.replace_prefix query_p new_p) s

def quick_lt : name → name → bool
| anonymous        anonymous          := ff
| anonymous        _                  := tt
| (mk_numeral n v) (mk_numeral n' v') := v < v' || (v = v' && n.quick_lt n')
| (mk_numeral _ _) (mk_string _ _)    := tt
| (mk_string n s)  (mk_string n' s')  := s < s' || (s = s' && n.quick_lt n')
| _                _                  := ff

/- Alternative has_lt instance. -/
@[inline] protected def has_lt_quick : has_lt name :=
⟨λ a b, name.quick_lt a b = tt⟩

@[inline] instance : decidable_rel (@has_lt.lt name name.has_lt_quick) :=
infer_instance_as (decidable_rel (λ a b, name.quick_lt a b = tt))

def to_string_with_sep (sep : string) : name → string
| anonymous                := "[anonymous]"
| (mk_string anonymous s)  := s
| (mk_numeral anonymous v) := to_string v
| (mk_string n s)          := to_string_with_sep n ++ sep ++ s
| (mk_numeral n v)         := to_string_with_sep n ++ sep ++ repr v

protected def to_string : name → string :=
to_string_with_sep "."

instance : has_to_string name :=
⟨name.to_string⟩

instance : has_to_format name :=
⟨λ n, n.to_string⟩

theorem mk_string_ne_mk_string_of_ne_prefix {p₁ : name} (s₁ : string) {p₂ : name} (s₂ : string) : p₁ ≠ p₂ → mk_string p₁ s₁ ≠ mk_string p₂ s₂ :=
λ h₁ h₂, name.no_confusion h₂ (λ h _, absurd h h₁)

theorem mk_string_ne_mk_string_of_ne_string (p₁ : name) {s₁ : string} (p₂ : name) {s₂ : string} : s₁ ≠ s₂ → mk_string p₁ s₁ ≠ mk_string p₂ s₂ :=
λ h₁ h₂, name.no_confusion h₂ (λ _ h, absurd h h₁)

theorem mk_numeral_ne_mk_numeral_of_ne_prefix {p₁ : name} (n₁ : nat) {p₂ : name} (n₂ : nat) : p₁ ≠ p₂ → mk_numeral p₁ n₁ ≠ mk_numeral p₂ n₂ :=
λ h₁ h₂, name.no_confusion h₂ (λ h _, absurd h h₁)

theorem mk_numeral_ne_mk_numeral_of_ne_numeral (p₁ : name) {n₁ : nat} (p₂ : name) {n₂ : nat} : n₁ ≠ n₂ → mk_numeral p₁ n₁ ≠ mk_numeral p₂ n₂ :=
λ h₁ h₂, name.no_confusion h₂ (λ _ h, absurd h h₁)

end name
end lean
