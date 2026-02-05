/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura and Sebastian Ullrich

Additional goodies for writing macros
-/
module
prelude
public import Init.Meta.Defs
public meta import Init.Meta.Defs
public meta import Init.Syntax
public section
namespace Lean

macro_rules
  | `(prec| $a + $b) => do `(prec| $(quote <| (← evalPrec a) + (← evalPrec b)):num)

macro_rules
  | `(prec| $a - $b) => do `(prec| $(quote <| (← evalPrec a) - (← evalPrec b)):num)

macro "eval_prec " p:prec:max : term => return quote (k := `term) (← evalPrec p)

macro_rules
  | `(prio| $a + $b) => do `(prio| $(quote <| (← evalPrio a) + (← evalPrio b)):num)

macro_rules
  | `(prio| $a - $b) => do `(prio| $(quote <| (← evalPrio a) - (← evalPrio b)):num)

macro "eval_prio " p:prio:max : term => return quote (k := `term) (← evalPrio p)

namespace Parser.Tactic

/-- `erw [rules]` is a shorthand for `rw (transparency := .default) [rules]`.
This does rewriting up to unfolding of regular definitions (by comparison to regular `rw`
which only unfolds `@[reducible]` definitions). -/
macro "erw" c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| rw $[$(getConfigItems c)]* (transparency := .default) $s:rwRuleSeq $(loc)?)

syntax simpAllKind := atomic(" (" &"all") " := " &"true" ")"
syntax dsimpKind   := atomic(" (" &"dsimp") " := " &"true" ")"

macro (name := declareSimpLikeTactic) doc?:(docComment)?
    "declare_simp_like_tactic" opt:((simpAllKind <|> dsimpKind)?)
    ppSpace tacName:ident ppSpace tacToken:str ppSpace cfg:optConfig : command => do
  let (kind, tkn, stx) ←
    if opt.raw.isNone then
      pure (← `(``simp), ← `("simp"), ← `($[$doc?:docComment]? syntax (name := $tacName) $tacToken:str optConfig (discharger)? (&" only")? (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic))
    else if opt.raw[0].getKind == ``simpAllKind then
      pure (← `(``simpAll), ← `("simp_all"), ← `($[$doc?:docComment]? syntax (name := $tacName) $tacToken:str optConfig (discharger)? (&" only")? (" [" (simpErase <|> simpLemma),* "]")? : tactic))
    else
      pure (← `(``dsimp), ← `("dsimp"), ← `($[$doc?:docComment]? syntax (name := $tacName) $tacToken:str optConfig (discharger)? (&" only")? (" [" (simpErase <|> simpLemma),* "]")? (location)? : tactic))
  `($stx:command
    @[macro $tacName] meta def expandSimp : Macro := fun s => do
      let cfg ← `(optConfig| $cfg)
      let s := s.setKind $kind
      let s := s.setArg 0 (mkAtomFrom s[0] $tkn (canonical := true))
      let s := s.setArg 1 (appendConfig s[1] cfg)
      let s := s.mkSynthetic
      return s)

/-- `simp!` is shorthand for `simp` with `autoUnfold := true`.
This will unfold applications of functions defined by pattern matching, when one of the patterns applies.
This can be used to partially evaluate many definitions. -/
declare_simp_like_tactic simpAutoUnfold "simp! " (autoUnfold := true)

/--
`simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`.
Note that `+decide` is not needed for reducing arithmetic terms since simprocs have been added to Lean.
-/
syntax (name := simpArith) "simp_arith " optConfig (discharger)? (&" only")? (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

/--
`simp_arith!` has been deprecated. It was a shorthand for `simp! +arith +decide`.
Note that `+decide` is not needed for reducing arithmetic terms since simprocs have been added to Lean.
-/
syntax (name := simpArithBang) "simp_arith! " optConfig (discharger)? (&" only")? (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

/-- `simp_all!` is shorthand for `simp_all` with `autoUnfold := true`.
This will unfold applications of functions defined by pattern matching, when one of the patterns applies.
This can be used to partially evaluate many definitions. -/
declare_simp_like_tactic (all := true) simpAllAutoUnfold "simp_all! " (autoUnfold := true)

/--
`simp_all_arith` has been deprecated. It was a shorthand for `simp_all +arith +decide`.
Note that `+decide` is not needed for reducing arithmetic terms since simprocs have been added to Lean.
-/
syntax (name := simpAllArith) "simp_all_arith" optConfig (discharger)? (&" only")? (" [" (simpErase <|> simpLemma),* "]")? : tactic

/--
`simp_all_arith!` has been deprecated. It was a shorthand for `simp_all! +arith +decide`.
Note that `+decide` is not needed for reducing arithmetic terms since simprocs have been added to Lean.
-/
syntax (name := simpAllArithBang) "simp_all_arith!" optConfig (discharger)? (&" only")? (" [" (simpErase <|> simpLemma),* "]")? : tactic


/-- `dsimp!` is shorthand for `dsimp` with `autoUnfold := true`.
This will unfold applications of functions defined by pattern matching, when one of the patterns applies.
This can be used to partially evaluate many definitions. -/
declare_simp_like_tactic (dsimp := true) dsimpAutoUnfold "dsimp! " (autoUnfold := true)
