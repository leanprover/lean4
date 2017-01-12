/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

-- Polytime version of lexicographic path order as described in:
-- Things to know when implementing LPO, Bernd Löchner, ESFOR 2004
import .utils
open expr decidable monad

def lex {T} [decidable_eq T] (gt : T → T → bool) : list T → list T → bool
| (s::ss) (t::ts) := if s = t then lex ss ts else gt s t
| _ _ := ff

def majo {T} (gt : T → T → bool) (s : T) : list T → bool
| [] := tt
| (t::ts) := gt s t && majo ts

meta def alpha (lpo : expr → expr → bool) : list expr → expr → bool
| [] _ := ff
| (s::ss) t := to_bool (s = t) || lpo s t || alpha ss t

meta def lex_ma (lpo : expr → expr → bool) (s t : expr) : list expr → list expr → bool
| (si::ss) (ti::ts) :=
  if si = ti then lex_ma ss ts
  else if lpo si ti then majo lpo s ts
  else alpha lpo (si::ss) t
| _ _ := ff

meta def lpo (prec_gt : expr → expr → bool) : expr → expr → bool | s t :=
if prec_gt (get_app_fn s) (get_app_fn t) then majo lpo s (get_app_args t)
else if get_app_fn s = get_app_fn t then lex_ma lpo s t (get_app_args s) (get_app_args t)
else alpha lpo (get_app_args s) t

meta def prec_gt_of_name_list (ns : list name) : expr → expr → bool :=
let nis := rb_map.of_list ns^.zip_with_index in
λs t, match (nis^.find (name_of_funsym s), nis^.find (name_of_funsym t)) with
| (some si, some ti) := to_bool (si > ti)
| _ := ff
end

meta def mk_lpo (ns : list name) : expr → expr → bool :=
let prec_gt := prec_gt_of_name_list ns in
lpo (prec_gt_of_name_list ns)
