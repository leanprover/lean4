/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Paul Reichert
-/

/-
This benchmark evaluates the performance of fuzzy matching when using the new ranges.
Currently, the code is using the old ranges because of a significant performance regression
regarding the compilation of the new ones in some `for` loops.

We copy the fuzzy matching algorithm, but use the new ranges (`a...b`) instead of the old ones
(`[a:b]`). Then we match 1000 hard-coded symbols against a few test inputs using the compiled
algorithm.

Because interpretation of the fuzzy matching algorithm is prohibitively slow, we cannot
just use `TermElabM` to extract the list of symbols from the environment.
-/

module
public import Lean.Elab.Term
meta import Lean.Elab.Term.TermElabM

@[specialize] private def iterateLookaround (f : (Option Char × Char × Option Char) → α) (string : String) : Array α :=
  if string.isEmpty then
    #[]
  else if string.length == 1 then
    #[f (none, string.get 0, none)]
  else Id.run do
    let mut result := Array.mkEmpty string.length
    result := result.push <| f (none, string.get 0, string.get ⟨1⟩)
    -- TODO: the following code is assuming all characters are ASCII
    for i in 2...string.length do
      result := result.push <| f (string.get ⟨i - 2⟩, string.get ⟨i - 1⟩, string.get ⟨i⟩)
    result.push <| f (string.get ⟨string.length - 2⟩, string.get ⟨string.length - 1⟩, none)

private def containsInOrderLower (a b : String) : Bool := Id.run do
  if a.isEmpty then
    return true
  let mut aIt := a.mkIterator
    -- TODO: the following code is assuming all characters are ASCII
  for i in *...b.rawEndPos.byteIdx do
    if aIt.curr.toLower == (b.get ⟨i⟩).toLower then
      aIt := aIt.next
      if !aIt.hasNext then
        return true
  return false

/-- Represents the type of a single character. -/
inductive CharType where
  | lower | upper | separator

def charType (c : Char) : CharType :=
  if c.isAlphanum then
    if c.isUpper
      then CharType.upper
      else CharType.lower
  else
    CharType.separator


/-- Represents the role of a character inside a word. -/
inductive CharRole where
  | head | tail | separator
  deriving Inhabited

@[inline] def charRole (prev? : Option CharType) (curr : CharType) (next?: Option CharType) : CharRole :=
  if curr matches CharType.separator then
    CharRole.separator
  else if prev?.isNone || prev? matches some CharType.separator then
    CharRole.head
  else if curr matches CharType.lower then
    CharRole.tail
  else if prev? matches some CharType.upper && !(next? matches some CharType.lower) then
    CharRole.tail
  else
    CharRole.head

/-- Add additional information to each character in a string. -/
private def stringInfo (s : String) : Array CharRole :=
  iterateLookaround (string := s) fun (prev?, curr, next?) =>
    charRole (prev?.map charType) (charType curr) (next?.map charType)


private def selectBest (missScore? matchScore? : Option Int) : Option Int :=
  match (missScore?, matchScore?) with
  | (missScore, none)  => missScore
  | (none, matchScore) => matchScore
  | (some missScore, some matchScore) =>
    some <| max missScore matchScore

private def fuzzyMatchCore (pattern word : String) (patternRoles wordRoles : Array CharRole) : Option Int := Id.run do
  /- Flattened array where the value at index (i, j, k) represents the best possible score of a fuzzy match
  between the substrings pattern[*...=i] and word[*...j] assuming that pattern[i] misses at word[j] (k = 0, i.e.
  it was matched earlier), or matches at word[j] (k = 1). A value of `none` corresponds to a score of -∞, and is used
  where no such match/miss is possible or for unneeded parts of the table. -/
  let mut result : Array (Option Int) := Array.replicate (pattern.length * word.length * 2) none
  let mut runLengths : Array Int := Array.replicate (pattern.length * word.length) 0

  -- penalty for starting a consecutive run at each index
  let mut startPenalties : Array Int := Array.replicate word.length 0

  let mut lastSepIdx := 0
  let mut penaltyNs : Int := 0
  let mut penaltySkip : Int := 0
  for wordIdx in *...word.length do
    if (wordIdx != 0) && wordRoles[wordIdx]! matches .separator then
      -- reset skip penalty at namespace separator
      penaltySkip := 0
      -- add constant penalty for each namespace to prefer shorter namespace nestings
      penaltyNs := penaltyNs + 1
      lastSepIdx := wordIdx
    penaltySkip := penaltySkip + skipPenalty wordRoles[wordIdx]! (wordIdx == 0)
    startPenalties := startPenalties.set! wordIdx $ penaltySkip + penaltyNs

  -- TODO: the following code is assuming all characters are ASCII
  for patternIdx in *...pattern.length do
    /- For this dynamic program to be correct, it's only necessary to populate a range of length
   `word.length - pattern.length` at each index (because at the very end, we can only consider fuzzy matches
    of `pattern` with a longer substring of `word`). -/
    for wordIdx in patternIdx...(word.length-(pattern.length - patternIdx - 1)) do
      let missScore? :=
        if wordIdx >= 1 then
          selectBest
            (getMiss result patternIdx (wordIdx - 1))
            (getMatch result patternIdx (wordIdx - 1))
        else none

      let mut matchScore? := none

      if allowMatch (pattern.get ⟨patternIdx⟩) (word.get ⟨wordIdx⟩) patternRoles[patternIdx]! wordRoles[wordIdx]! then
        if patternIdx >= 1 then
          let runLength := runLengths[getIdx (patternIdx - 1) (wordIdx - 1)]! + 1
          runLengths := runLengths.set! (getIdx patternIdx wordIdx) runLength

          matchScore? := selectBest
            (getMiss result (patternIdx - 1) (wordIdx - 1) |>.map (· + matchResult
              patternIdx wordIdx
              patternRoles[patternIdx]! wordRoles[wordIdx]!
              none
            - startPenalties[wordIdx]!))
            (getMatch result (patternIdx - 1) (wordIdx - 1) |>.map (· + matchResult
              patternIdx wordIdx
              patternRoles[patternIdx]! wordRoles[wordIdx]!
              (.some runLength)
            )) |>.map fun score => if wordIdx >= lastSepIdx then score + 1 else score -- main identifier bonus
        else
          runLengths := runLengths.set! (getIdx patternIdx wordIdx) 1
          matchScore? := .some $ matchResult
              patternIdx wordIdx
              patternRoles[patternIdx]! wordRoles[wordIdx]!
              none
              - startPenalties[wordIdx]!

      result := set result patternIdx wordIdx missScore? matchScore?

  return selectBest (getMiss result (pattern.length - 1) (word.length - 1)) (getMatch result (pattern.length - 1) (word.length - 1))

  where
    getDoubleIdx (patternIdx wordIdx : Nat) := patternIdx * word.length * 2 + wordIdx * 2

    getIdx (patternIdx wordIdx : Nat) := patternIdx * word.length + wordIdx

    getMiss (result : Array (Option Int)) (patternIdx wordIdx : Nat) : Option Int :=
      result[getDoubleIdx patternIdx wordIdx]!

    getMatch (result : Array (Option Int)) (patternIdx wordIdx : Nat) : Option Int :=
      result[getDoubleIdx patternIdx wordIdx + 1]!

    set (result : Array (Option Int)) (patternIdx wordIdx : Nat) (missValue matchValue : Option Int) : Array (Option Int) :=
      let idx := getDoubleIdx patternIdx wordIdx
      result |>.set! idx missValue |>.set! (idx + 1) matchValue

    /-- Heuristic to penalize skipping characters in the word. -/
    skipPenalty (wordRole : CharRole) (wordStart : Bool) : Int := Id.run do
      /- Skipping the beginning of the word. -/
      if wordStart then
        return 3
      /- Skipping the beginning of a segment. -/
      if wordRole matches CharRole.head then
        return 1

      return 0

    /-- Whether characters from the pattern and the word match. -/
    allowMatch (patternChar wordChar : Char) (patternRole wordRole : CharRole) : Bool := Id.run do
      /- Different characters do not match. -/
      if patternChar.toLower != wordChar.toLower then
        return false
      /- The beginning of a segment in the pattern must align with the beginning of a segment in the word. -/
      if patternRole matches CharRole.head && !(wordRole matches CharRole.head) then
        return false

      return true

    /-- Heuristic to rate a match. -/
    matchResult (patternIdx wordIdx : Nat) (patternRole wordRole : CharRole) (consecutive : Option Int) : Int := Id.run do
      let mut score : Int := 1
      /- Case-sensitive equality or beginning of a segment in pattern and word. -/
      if (pattern.get ⟨patternIdx⟩) == (word.get ⟨wordIdx⟩) || (patternRole matches CharRole.head && wordRole matches CharRole.head) then
        score := score + 1
      /- Matched end of word with end of pattern -/
      if wordIdx == word.length - 1 && patternIdx == pattern.length - 1 then
        score := score + 2
      /- Matched beginning of the word. -/
      if (wordIdx == 0) then
        score := score + 3
      /- Consecutive character match. -/
      if let some bonus := consecutive then
        /- consecutive run bonus -/
        score := score + bonus
      return score

/-- Match the given pattern with the given word using a fuzzy matching
algorithm. The resulting scores are in the interval `[0, 1]` or `none` if no
match was found. -/
def fuzzyMatchScore? (pattern word : String) : Option Float := Id.run do
  /- Some fast and simple checks. -/
  if pattern.isEmpty then
    return some 1
  if pattern.length > word.length then
    return none
  if !(containsInOrderLower pattern word) then
    return none

  let some score := fuzzyMatchCore pattern word (stringInfo pattern) (stringInfo word)
    | none
  let mut score := score

  /- Bonus if every character is matched. -/
  if pattern.length == word.length then
    score := score * 2

  /- Perfect score per character. -/
  let perfect := 4
  /- Perfect score for full match given the heuristic in `matchResult`;
  the latter term represents the bonus of a perfect consecutive run. -/
  let perfectMatch := (perfect * pattern.length + ((pattern.length * (pattern.length + 1) / 2) - 1))
  let normScore := Float.ofInt score / Float.ofInt perfectMatch

  return some <| min 1 (max 0 normScore)

def fuzzyMatchScoreWithThreshold? (pattern word : String) (threshold := 0.1) : Option Float :=
  fuzzyMatchScore? pattern word |>.filter (· > threshold)

/-- Match the given pattern with the given word using a fuzzy matching
algorithm. Return `false` if no match was found or the found match received a
score below the given threshold. -/
def fuzzyMatch (pattern word : String) (threshold := 0.2) : Bool :=
  fuzzyMatchScoreWithThreshold? pattern word threshold |>.isSome

-- The constants have been generated using the following code.
open Lean Elab Term Meta

meta def getConsts : MetaM (List Name) := do
  let env ← getEnv
  return env.constants.toList.map (·.1)

elab "gen_consts" : term => do
  let consts : List Name ← getConsts
  let constsAsExprs : List Expr := consts.map toExpr
  let listExpr : Expr ← mkListLit (.const ``Name []) (constsAsExprs.take 1000)
  return listExpr

def consts := ["_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.match_1",
 "charRole.match_3",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.iterateLookaround",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.containsInOrderLower",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.selectBest",
 "CharType.toCtorIdx",
 "CharType.upper.sizeOf_spec",
 "CharType.casesOn",
 "CharRole.head.sizeOf_spec",
 "CharRole.tail.sizeOf_spec",
 "CharType.separator.sizeOf_spec",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore",
 "CharType.lower",
 "fuzzyMatchScoreWithThreshold?",
 "CharRole.noConfusionType",
 "CharType",
 "charRole.match_1",
 "CharType._sizeOf_inst",
 "CharRole.rec",
 "CharType.ctorIdx",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.match_3",
 "CharType._sizeOf_1",
 "charRole.match_7",
 "instInhabitedCharRole",
 "CharType.lower.sizeOf_spec",
 "CharRole.ctorElimType",
 "CharType.ctorElim",
 "CharRole.separator",
 "CharType.lower.elim",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.getIdx",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.matchResult.match_1",
 "defaultCharRole._@.external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean.2223406467._hygCtx._hyg.8",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.getMatch",
 "CharRole.toCtorIdx",
 "CharRole.casesOn",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.selectBest.match_1",
 "CharType.noConfusion",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.allowMatch",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.containsInOrderLower.match_1",
 "CharRole.tail.elim",
 "CharType.separator.elim",
 "CharType.recOn",
 "CharRole._sizeOf_inst",
 "CharRole.ctorIdx",
 "getConsts",
 "CharType.rec",
 "CharRole._sizeOf_1",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.getDoubleIdx",
 "CharType.upper",
 "CharRole.head",
 "fuzzyMatchScore?",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.skipPenalty.match_1",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.stringInfo",
 "charRole",
 "CharRole.noConfusion",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.skipPenalty",
 "CharRole.separator.elim",
 "CharRole.recOn",
 "charRole.match_5",
 "termConsts'",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.set",
 "charType",
 "CharRole.head.elim",
 "CharType.upper.elim",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.iterateLookaround._proof_1",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.stringInfo.match_1",
 "CharRole.separator.sizeOf_spec",
 "fuzzyMatch",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.matchResult",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.match_5",
 "CharRole",
 "CharType.noConfusionType",
 "_private.«external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean».0.fuzzyMatchCore.getMiss",
 "CharRole.tail",
 "CharType.ctorElimType",
 "charRole.match_9",
 "CharRole.ctorElim",
 "«_aux_external:file:///Users/paul/code/lean4/tests/bench/workspaceSymbolsNewRanges.lean___elabRules_termConsts'_1»",
 "CharType.separator",
 "Lean.Elab.CommandContextInfo._sizeOf_1",
 "Std.DTreeMap.Internal.Impl.insert._proof_32",
 "_private.Lean.PrettyPrinter.Parenthesizer.0.Lean.PrettyPrinter.Parenthesizer.rawStx.parenthesizer.match_1",
 "Lean.Meta.Instances.ctorIdx",
 "_private.Lean.Log.0.Lean.MessageData.appendDescriptionWidgetIfNamed.stripNestedTags.match_1",
 "Lean.Compiler.getDeclNamesForCodeGen",
 "Array.countP_eq_size._simp_1",
 "Lean.Grind.Linarith.Poly.denote'.go.match_1",
 "_private.Std.Data.DTreeMap.Internal.Balancing.0.Std.DTreeMap.Internal.Impl.balanceL._proof_13",
 "_private.Init.Data.SInt.Lemmas.0.ISize.le_refl._simp_1_1",
 "Std.DTreeMap.minKey!",
 "Std.PRange.RangeIterator.isSome_next_of_isPlausibleIndirectOutput",
 "decEqSum._proof_4._@.Init.Core.2394421412._hygCtx._hyg.3",
 "Sum._sizeOf_1",
 "_private.Init.Data.List.Count.0.List.count_pos_iff._simp_1_3",
 "Vector.toArray_pop",
 "Lean.IR.IRType.rec",
 "Vector.toList_singleton",
 "BitVec.lt_of_msb_false_of_msb_true._simp_1",
 "Lean.Elab.Term.withoutTacticIncrementality",
 "_private.Init.Data.List.Nat.TakeDrop.0.List.getElem?_drop._simp_1_1",
 "_private.Init.Data.Nat.Control.0.Nat.anyM.loop._unsafe_rec",
 "Lean.CollectAxioms.State.recOn",
 "BitVec.getMsbD_rotateLeftAux_of_lt",
 "_private.Init.Data.Fin.Lemmas.0.Fin.reverseInduction.go._proof_2",
 "IO.TaskState.ofNat",
 "Nat.div_eq_sub_mod_div",
 "Vector.not_all_eq_any_not",
 "Acc.brecOn",
 "instBEqFloat32",
 "Lean.MetavarContext.LevelMVarToParam.State.mk",
 "Int32.instNeg",
 "_private.Init.Data.Int.Cooper.0.Int.Cooper.resolve_left.eq_1",
 "Int.ofNat_eq_zero",
 "Iff.mp",
 "Repr",
 "Int64.shiftLeft_and",
 "Lean.Elab.Tactic.State.goals",
 "HEq.rfl",
 "_private.Lean.Meta.Basic.0.Lean.Meta.mkFreshExprMVarImpl",
 "Int.tdiv_eq_tdiv_of_mul_eq_mul",
 "StateRefT'",
 "Lean.Grind.Ring.OfSemiring.Expr.mul.inj",
 "Lean.FVarId._sizeOf_inst",
 "Lean.addDocStringCore'",
 "Lean.Grind.Config.exp._default",
 "Lean.Level.normLtAux._unary",
 "Lean.Meta.DSimp.Config.mk",
 "Rat.den_ofNat",
 "Lean.Grind.IsCharP.mk'",
 "Lean.ConstantInfo.levelParams",
 "List.IsSuffix.trans",
 "_private.Init.Data.Format.Basic.0.Std.Format.SpaceResult.foundFlattenedHardLine._default",
 "Lean.IR.IRType.tobject.sizeOf_spec",
 "Lean.Grind.AC.Seq.eraseDup.induct_unfolding",
 "Lean.Parser.registerParserCategory",
 "Vector.mapIdx_eq_mapIdx_iff",
 "List.forIn'_loop_congr",
 "instNegUInt8",
 "UInt64.toNat_sub_of_le",
 "Lean.Grind.IntModule.OfNatModule.instOrderedAddQ._proof_1",
 "Nat.SOM.Expr.add.elim",
 "Lean.Grind.CommRing.Power.x",
 "Lean.BaseMessage.ctorIdx",
 "Lean.Elab.Term.Context.heedElabAsElim",
 "_private.Lean.Parser.Term.0.Lean.Parser.Term.scientific._regBuiltin.Lean.Parser.Term.scientific_1",
 "Int64.toInt_minValue",
 "_private.Init.Data.UInt.Lemmas.0.UInt64.mk_toBitVec_eq.match_1_1",
 "Nat.bitwise_mod_two_pow",
 "Lean.Syntax._sizeOf_inst",
 "Int.recOn",
 "Nat.max_eq_left",
 "_private.Lean.Meta.Basic.0.Lean.Meta.InfoCacheKey.mk._flat_ctor",
 "Vector.size",
 "_private.Init.Data.List.Sublist.0.List.Sublist.subset.match_1_1._@.Init.Data.List.Sublist.3015053212._hygCtx._hyg.221",
 "Lean.Order.MonoBind.mk._flat_ctor",
 "«term_\\/_»",
 "GetElem?",
 "UInt64.add",
 "Vector.head",
 "Lean.Grind.CommRing.Expr.neg.elim",
 "Lean.KVMap.setNat",
 "Lean.Data.AC.Expr.ctorElim",
 "Lean.Order.instMonoBindExceptTOfCCPO._proof_1",
 "Lean.ReducibilityStatus.rec",
 "Lean.Grind.instCommRingInt8._proof_4",
 "Int8.add_eq_left",
 "Lean.logInfo",
 "_private.Lean.Environment.0.Lean.finalizePersistentExtensions.loop._unsafe_rec",
 "_private.Init.Data.Array.Zip.0.Array.zipWith_replicate._simp_1_1",
 "Lean.Compiler.LCNF.FVarSubst",
 "_private.Init.Data.Dyadic.Basic.0.Rat.toDyadic.match_1.eq_1",
 "_private.Std.Data.DHashMap.Internal.AssocList.Basic.0.Std.DHashMap.Internal.AssocList.foldlM.match_1",
 "Lean.JsonNumber.mk.inj",
 "Char.lt_def",
 "Lean.OpenDecl.casesOn",
 "_private.Lean.Meta.Check.0.Lean.Meta.addPPExplicitToExposeDiff.visit",
 "UInt8.lt_iff_toBitVec_lt._simp_1",
 "_private.Lean.Expr.0.Lean.Expr.isType.match_1",
 "Std.PRange.LawfulClosedOpenIntersection.mem_intersection_iff",
 "_private.Init.Data.Fin.Lemmas.0.Fin.reverseInduction._proof_3",
 "Vector.swapIfInBounds._proof_1",
 "List.findIdx_subtype",
 "LawfulMonad.mk",
 "_private.Lean.Parser.Command.0.Lean.Parser.Command.declaration._regBuiltin.Lean.Parser.Command.unsafe.parenthesizer_207",
 "Lean.DataValue.ofNat",
 "Lean.Elab.TerminationHints.mk.sizeOf_spec",
 "Std.Iterators.Iter.forIn_eq",
 "BitVec.instLawfulCommIdentityHMulOfNatOfNatNat",
 "Std.Slice.Internal.SubarrayData.mk.injEq",
 "Lean.PersistentArray.toArray",
 "Lean.PrettyPrinter.Parenthesizer.strLitNoAntiquot.parenthesizer",
 "Int.Linear.unsatEqDivCoeffCert.eq_1",
 "_private.Lean.Parser.Command.0.Lean.Parser.Command.where._regBuiltin.Lean.Parser.Command.where_1",
 "Lean.Meta.AbstractMVarsResult.mk._flat_ctor",
 "Lean.ExternEntry.opaque.sizeOf_spec",
 "_private.Lean.Parser.Basic.0.Lean.Parser.rawStrLitFnAux.normalState._unsafe_rec",
 "_private.Lean.Level.0.Lean.Level.mkMaxAux._unsafe_rec",
 "Lean.Grind.instFieldRat._proof_2",
 "Array.findIdx_eq_size_of_false",
 "_private.Init.Data.List.Sublist.0.List.infix_of_mem_flatten.match_1_3",
 "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR_go_eq",
 "Lean.Parser.categoryParserFnRef",
 "_private.Lean.Meta.Transform.0.Lean.Meta.transformWithCache.visit.visitLet._unsafe_rec",
 "Lean.Compiler.LCNF.LitValue.usize.injEq",
 "List.drop_replicate",
 "Lean.Grind.NatModule.noConfusion",
 "Lean.Meta.ExtractLetsConfig.mk._flat_ctor",
 "Nat.ToInt.of_diseq",
 "Std.Iterators.IterStep.done",
 "List.take_left",
 "Std.Range.forM_eq_forM_range'",
 "Lean.Parser.OrElseOnAntiquotBehavior.merge.elim",
 "Bool.beq_to_eq",
 "Nat.Simproc.eq_add_le",
 "Lean.Grind.Linarith.Expr.intMul.injEq",
 "Std.Slice.casesOn",
 "_private.Init.Data.Vector.Lemmas.0.Vector.forall_mem_append._simp_1_2",
 "Std.PRange.forIn'_eq_match.match_3",
 "Std.ToStream.casesOn",
 "Lean.Level.PP.Result.leaf.inj",
 "Lean.PrettyPrinter.Parenthesizer.Context._sizeOf_1",
 "Std.Format.tag",
 "Lean.Exception.recOn",
 "_private.Init.Grind.ToInt.0.Lean.Grind.decEqIntInterval._proof_6._@.Init.Grind.ToInt.3920380712._hygCtx._hyg.71",
 "_private.Init.Data.Int.DivMod.Lemmas.0.Int.emod_natAbs_of_nonneg.match_1_1",
 "Lean.Compiler.LCNF.CodeDecl.let.sizeOf_spec",
 "Lean.Meta.isListLevelDefEqAux._unsafe_rec",
 "USize.toISize_not",
 "Std.DTreeMap.Internal.Impl.SizedBalancedTree._sizeOf_inst",
 "USize.instTransOrd",
 "Lean.Grind.Config.canonHeartbeats",
 "Array.anyM_loop_iff_exists._unary",
 "Lean.instInhabitedTSyntax",
 "Lean.LocalContext.decls",
 "Int64.toInt_ofNat'",
 "Nat.mul_le_add_right",
 "Int32.pow._unsafe_rec",
 "Lean.Grind.instOfNatInt16SintOfNatNat._proof_4",
 "_private.Init.Data.List.Nat.Modify.0.List.eraseIdx_modify_of_lt._proof_1_3",
 "_private.Lean.Environment.0.Lean.ImportedModule.mk.inj",
 "Array.ext'",
 "«_aux_Init_NotationExtra___macroRules_term∃_,__1»",
 "_private.Init.Data.List.Lemmas.0.List.forall_mem_append._simp_1_2",
 "_private.Lean.Parser.Command.0.Lean.Parser.Command.declaration._regBuiltin.Lean.Parser.Command.structInstBinder.parenthesizer_341",
 "Nat.gcd_eq_left",
 "Array.foldl.eq_1",
 "List.getElem?_intersperse_two_mul",
 "Lean.Elab.InlayHintInfo.noConfusion",
 "Rat.normalize._proof_2",
 "Fin.val_add_one_le_of_lt",
 "Lean.Parser.Term.pipeProj.parenthesizer",
 "Lean.instValueLeanOptionValue",
 "Lean.Grind.Config.matchEqs._default",
 "Array.getElem_map._proof_1",
 "Lean.ClassEntry",
 "Option.pfilter_none",
 "Std.DTreeMap.Raw.keyAtIndexD",
 "MonadWithReader.mk",
 "Fin.foldrM_succ",
 "instAssociativeInt32HOr",
 "Rat.add_assoc",
 "_private.Init.Data.Int.Linear.0.Int.Linear.Poly.combine'.match_1.eq_4",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.toFin_shiftLeftZeroExtend._proof_1_2",
 "_private.Init.Data.Order.LemmasExtra.0.Std.instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd._simp_2",
 "Lean.AttributeApplicationTime.recOn",
 "Lean.MetavarContext.LevelMVarToParam.Context.mk.inj",
 "Nat.isPowerOfTwo_nextPowerOfTwo",
 "Int.negOfNat.match_1",
 "Lean.IR.IRType.struct.sizeOf_spec",
 "Int32.le_antisymm_iff",
 "Lean.Parser.Term.argument.formatter",
 "BitVec.getElem_setWidth'",
 "Std.instReflCmpCompareLex",
 "Nat.mul_pred",
 "Lean.Parser.Term.logNamedWarningAtMacro.formatter",
 "_private.Init.Data.Int.DivMod.Lemmas.0.Int.neg_fdiv._proof_1_2",
 "_private.Init.Data.Int.Gcd.0.Int.dvd_coe_gcd_iff.match_1_1",
 "UInt64.toNat_shiftLeft",
 "Lean.Parser.ParserExtension.OLeanEntry.token.elim",
 "_private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop.0.Std.Iterators.IterM.DefaultConsumers.toArrayMapped_eq_match_step.match_1.eq_1",
 "_private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.PRange.RangeIterator.instIteratorLoop.loop_eq.match_1.eq_2",
 "_private.Init.Data.Int.DivMod.Lemmas.0.Int.natAbs_fdiv_le_natAbs._proof_1_5",
 "List.pmap.match_1",
 "_private.Init.Data.Nat.Basic.0.Nat.le_add_of_sub_le.match_1_1",
 "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run'.match_1",
 "Array.mapIdx_eq_append_iff",
 "Lean.Grind.AC.Expr.toSeq.eq_1",
 "Rat.pow_pos",
 "Std.Internal.List.DistinctKeys.mk",
 "Int64.ofInt_tdiv",
 "Lean.Grind.Ring.toIntModule._proof_2",
 "Nat.exists_lt_succ_right'",
 "Lean.ExternEntry.inline",
 "Lean.Grind.CommRing.beqMon.«_@».Init.Grind.Ring.Poly.1150767823._hygCtx._hyg.26._unsafe_rec",
 "Vector.reflBEq_iff._simp_1",
 "_private.Lean.Parser.Term.0.Lean.Parser.Term.noImplicitLambda._regBuiltin.Lean.Parser.Term.noImplicitLambda.formatter_7",
 "Lean.Parser.ParserState",
 "Lean.instToMessageDataFormat",
 "Lean.Elab.ComputeKind",
 "Lean.PPFns.ppLevel",
 "Int.lt_of_add_one_le",
 "Vector.finRange_succ_last",
 "_private.Init.Data.Nat.SOM.0.Nat.SOM.Mon.mul_denote.go",
 "Lean.Parser.Tactic.rewrites_forbidden",
 "_private.Init.Data.Rat.Lemmas.0.Rat.le_iff_sub_nonneg._simp_1_2",
 "_private.Lean.Meta.DiscrTree.0.Lean.Meta.DiscrTree.getMatchWithExtra.go",
 "Lean.Grind.AC.Seq.sort'.eq_def",
 "Std.Iterators.IterM.DefaultConsumers.toArrayMapped.eq_1",
 "Lean.Meta.reduceNatNativeUnsafe",
 "Std.DTreeMap.Const.maxEntry?",
 "_private.Lean.Data.Json.Basic.0.Lean.JsonNumber.fromPositiveFloat!",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.append_assoc'._proof_1",
 "Array.flatMap_subtype",
 "Lean.ScopedEnvExtension.ScopedEntries.mk.injEq",
 "Lean.Meta.reduceMatcher?",
 "_private.Init.Data.List.Find.0.List.idxOf_lt_length_of_mem._simp_1_1",
 "Int64.ofBitVec_mul",
 "Lean.Parser.Command.example",
 "_private.Init.PropLemmas.0.decidable_of_bool._proof_1",
 "System.FilePath.withExtension",
 "_private.Init.Data.Vector.Basic.0.decEqVector._proof_2._@.Init.Data.Vector.Basic.509770449._hygCtx._hyg.42",
 "Nat.div_dvd_iff_dvd_mul",
 "BitVec.getLsbD.eq_1",
 "_private.Init.Data.Array.Lemmas.0.Array.getElem_range'._simp_1_1",
 "Lean.Expr.quickComp",
 "UInt32.zero_shiftRight",
 "_private.Init.Data.Int.DivMod.Lemmas.0.Int.tmod_two_eq.match_1_1",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.ult_eq_msb_of_msb_neq._simp_1_2",
 "_private.Init.Data.Vector.Basic.0.decEqVector.match_1._@.Init.Data.Vector.Basic.509770449._hygCtx._hyg.42",
 "Lean.Meta.Omega.OmegaConfig.ctorIdx",
 "_private.Init.Util.0.withPtrEqDecEq._proof_2",
 "Vector.getElem_reverse",
 "Float.fromJson?",
 "_private.Lean.Util.Path.0.Lean.findSysroot.match_1",
 "Eq.casesOn",
 "Lean.JsonNumber.instRepr",
 "isExclusiveUnsafe",
 "Std.DHashMap.instSingletonSigma.match_1",
 "_aux_Init_Data_ToString_Macro___macroRules_termS!__1",
 "_auto._@.Init.Data.Vector.Range.4110789332._hygCtx._hyg.6",
 "Lean.ConstructorVal.isUnsafeEx",
 "List.all",
 "BitVec.add_zero",
 "Lean.Grind.toInt_usize",
 "_private.Init.Data.Array.Erase.0.Array.size_eraseP_of_mem.match_1_1",
 "Lean.EffectiveImport.recOn",
 "Nat.mod_lt",
 "Lean.Omega.Coeffs.sdiv",
 "Lean.Expr.isHeadBetaTarget",
 "List.forIn'_toArray",
 "Std.DTreeMap.Raw.getKey!",
 "Lean.IR.Expr.ctorIdx",
 "ISize.add_comm",
 "_private.Init.Data.List.Nat.TakeDrop.0.List.getElem?_drop.match_1_4",
 "_private.Init.Data.Nat.Fold.0.Nat.dfoldRev._proof_12",
 "ForInStep.done.sizeOf_spec",
 "Lean.Meta.Omega.OmegaConfig.noConfusion",
 "_private.Lean.Parser.Term.0.Lean.Parser.Term.letMVar._regBuiltin.Lean.Parser.Term.letMVar.declRange_3",
 "instFiniteStateSubarrayId",
 "_private.Init.Meta.0.Lean.Syntax.unsetTrailing.match_1",
 "Int16.pow._sunfold",
 "Lean.Parser.Term.letOpts",
 "Lean.Macro.Methods._sizeOf_inst",
 "Lean.Parser.nameLitNoAntiquot",
 "Lean.Elab.defaultTerminationHints._@.Lean.Elab.PreDefinition.TerminationHint.3385859311._hygCtx._hyg.58",
 "Lean.AsyncConstantInfo.rec",
 "UInt32.toFin_ofNatLT",
 "Std.Packages.LinearPreorderOfOrdArgs.decidableLT._autoParam",
 "Option.bind.eq_2",
 "Lean.Parser.Term.match",
 "List.getElem_replace_of_ne",
 "Lean.Elab.Term.MVarErrorKind._sizeOf_1",
 "_private.Init.Data.List.Nat.Erase.0.List.getElem_eraseIdx_of_lt._proof_1_3",
 "Alternative",
 "Lean.registerTagAttribute",
 "Lean.Meta.FunInfo.mk.injEq",
 "Lean.Grind.instIsCharPInt16HPowNatOfNat._proof_2",
 "Std.DTreeMap.Internal.Impl.forIn",
 "Id.instLawfulMonadLiftTOfLawfulMonad._proof_2",
 "_private.Init.PropLemmas.0.decidable_of_bool._proof_2",
 "_private.Lean.DocString.Links.0.Lean.manualRoot.match_1",
 "Std.DTreeMap.Internal.Impl.getD",
 "Classical.axiomOfChoice",
 "TypeName.noConfusion",
 "instDecidableEqInt64",
 "Rat.den_pos",
 "Nat.eq_zero_or_pos",
 "Std.Iterators.IterM.map_unattach_toListRev_attachWith",
 "Std.DTreeMap.Internal.Impl.maxEntry!._proof_2",
 "List.appendTR",
 "PartialEquivBEq.trans",
 "BitVec.toFin_sub",
 "Vector.back_replicate",
 "BitVec.toNat_zero_length",
 "Lean.TSyntax.noConfusion",
 "Std.Iterators.IterM.toList_filterMap",
 "Nat.sub_succ'",
 "_private.Lean.Data.Json.Parser.0.Lean.Json.Parser.escapedChar._proof_2",
 "_private.Lean.Parser.Term.0.Lean.Parser.Term.leftact._regBuiltin.Lean.Parser.Term.leftact.declRange_5",
 "BitVec.getMsbD_twoPow",
 "WellFounded.recOn",
 "_private.Init.Data.Int.Linear.0.Int.Linear.gcd_dvd_step",
 "Std.Iterators.instForInPartialOfIteratorLoopPartialOfMonadLiftTOfMonad",
 "Lean.IR.FnBody.sset",
 "List.getLast._proof_1",
 "_private.Init.Data.Nat.MinMax.0.Nat.max_lt.match_1_1",
 "_private.Lean.Meta.Basic.0.Lean.Meta.processPostponedStep.match_1",
 "UInt16.xor_assoc",
 "IO.TaskState.noConfusionType",
 "Std.DTreeMap.Raw.Const.unitOfArray",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.msb_umod_of_msb_false_of_ne_zero._simp_1_1",
 "Lean.Grind.AC.Seq.insert.induct_unfolding",
 "_private.Init.Data.Int.DivMod.Lemmas.0.Int.fdiv_nonneg.match_1_1",
 "_private.Init.Data.List.Lemmas.0.List.splitAt.go.match_1.eq_2",
 "Std.Internal.Parsec.ParseResult.ctorIdx",
 "Lean.Parser.Term.forInMacro'.parenthesizer",
 "Lean.ToJson.noConfusionType",
 "BitVec.neg_neg",
 "_private.Init.Data.List.Sort.Basic.0.List.mergeSort.eq_def",
 "Lean.Meta.initFn._@.Lean.Meta.Coe.1330821246._hygCtx._hyg.4",
 "_private.Init.Data.List.Monadic.0.List.filterMapM_cons.match_1.splitter",
 "_private.Init.Data.UInt.Bitwise.0.UInt8.and_le_left._simp_1_1",
 "Lean.Omega.Coeffs.sub",
 "Array.mapFinIdxM.map.eq_2",
 "Array.le_total",
 "UInt16.ofBitVec_uInt32ToBitVec",
 "StdGen.rec",
 "_private.Std.Data.DTreeMap.Internal.Balancing.0.Std.DTreeMap.Internal.Impl.balanceR.match_1.eq_5",
 "Lean.Grind.CommRing.Poly.combineC.go._unsafe_rec",
 "_private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.testBit_bitwise._simp_1_2",
 "Lean.SourceInfo.none.elim",
 "Lean.Kernel.isDiagnosticsEnabled",
 "_private.Init.Data.List.Sublist.0.List.reverse_suffix.match_1_3",
 "List.find?_eq_some_iff_append",
 "dite_eq_left_iff",
 "Int.ofNat_toNat",
 "Vector.getElem_append_left'._proof_2",
 "Lean.Name.getRoot",
 "ForM.mk._flat_ctor",
 "Lean.Parser.withResetCache",
 "Nat.eq_div_of_mul_eq_right",
 "Array.find?_flatten_eq_some_iff",
 "Lean.Parser.Term.matchAlts.parenthesizer",
 "_private.Init.Data.List.ToArray.0.Array.back?.eq_1",
 "Lean.PrettyPrinter.Formatter.Context",
 "Option.get_dite'._proof_1",
 "CoeOTC.noConfusionType",
 "Int.gcd_gcd_self_right_right",
 "_private.Init.Data.Array.MapIdx.0.List.mapIdx.go.match_1.eq_2",
 "Lean.Nat.mkInstNatPow",
 "List.length_pos_of_mem",
 "UInt16.le_refl._simp_1",
 "Lean.StructureParentInfo._sizeOf_inst",
 "Nat.testBit",
 "Array.getElem_attach._proof_1",
 "Array.getElem?_setIfInBounds_ne",
 "Lean.DependsOn.State.mk.inj",
 "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevInTwo'_fst._proof_2",
 "_private.Lean.Environment.0.Lean.VisibilityMap.mk._flat_ctor",
 "instNatPowNat",
 "Lean.Parser.Tactic.Conv.convTrace_state",
 "Substring.recOn",
 "Lean.LevelMVarId.noConfusionType",
 "Nat.le_sub_of_add_le",
 "Int64.toInt32_mul",
 "Std.PRange.BoundShape.noConfusion",
 "Float.abs",
 "Vector.mk_eq",
 "_private.Lean.Syntax.0.Lean.SyntaxNode.getKind.match_1",
 "UInt64.toUSize_ofNatLT",
 "Int8.toInt64_ofIntLE",
 "_private.Init.Classical.0.Classical.em.match_1_1",
 "Vector.find?_eq_findSome?_guard",
 "Lean.Core.SavedState.traceState._inherited_default",
 "Lean.NameHashSet.empty",
 "Option.foldl_toArray",
 "Array.instForIn'InferInstanceMembership",
 "Lean.Expr.FindStep.done.sizeOf_spec",
 "Lean.ModuleArtifacts._sizeOf_inst",
 "Lean.LevelSet",
 "getElem?_neg",
 "Array.any_flatten",
 "Std.Packages.LinearPreorderOfOrdArgs.beq._autoParam",
 "Array.Perm.extract",
 "Nat.pos_of_mul_pos_right",
 "forall_apply_eq_imp_iff._simp_1",
 "Lean.IR.Arg.var.inj",
 "_private.Init.Data.UInt.Bitwise.0.UInt16.zero_shiftLeft._simp_1_1",
 "_private.Lean.Parser.Term.0.Lean.Parser.Term.pipeProj._regBuiltin.Lean.Parser.Term.pipeProj.docString_3",
 "Lean.MacroScopesView.mk._flat_ctor",
 "_private.Lean.Meta.WHNF.0.Lean.Meta.useWHNFCache",
 "_private.Init.Data.Option.Lemmas.0.Option.merge.match_1.eq_4",
 "Int.Linear.Poly.isUnsatEq",
 "Vector.vector₃_induction.match_1",
 "List.countP_nil",
 "_private.Init.Data.List.Control.0.List.getLast?.match_1.splitter",
 "Std.DTreeMap.Internal.Impl.getKeyLE",
 "Lean.Grind.CommRing.d_normEq0",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.umulOverflow_assoc._simp_1_3",
 "Std.LinearOrderPackage.toLinearPreorderPackage",
 "Lean.ClassEntry.name",
 "Std.Iterators.ToIterator.iterM_eq",
 "ByteArray.beqByteArray.match_1._@.Init.Data.ByteArray.Basic.4013209869._hygCtx._hyg.3",
 "Lean.Data.Trie._sizeOf_3",
 "Vector.unattach_mkVector",
 "List.isEmpty_eq_true",
 "Lean.LocalContext.renameUserName",
 "StateT.tryFinally",
 "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
 "BitVec.ushiftRight_eq'",
 "Int.trailingZeros.aux.fun_cases_unfolding",
 "_private.Init.Data.Option.Lemmas.0.Option.not_mem_none.match_1_1",
 "_private.Init.Data.BitVec.Bitblast.0.BitVec.msb_sdiv_eq_decide._simp_1_12",
 "Lean.instCoeNatLeanOptionValue",
 "USize.shiftLeft_zero",
 "Int.Linear.Expr.recOn",
 "Vector.mapFinIdx_mk._proof_2",
 "String.split",
 "Option.map_pbind",
 "Lean.Omega.LinearCombo.neg_eval",
 "_private.Init.Data.UInt.Lemmas.0.UInt32.lt_of_lt_of_le._simp_1_1",
 "Std.TreeSet.instMembership",
 "Classical.exists_true_of_nonempty",
 "Lean.ModuleSetup.mk",
 "_private.Init.Data.List.Impl.0.List.getLast?.match_1.eq_2",
 "Int.sub_left_le_of_le_add",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.getMsbD_twoPow._proof_1_2",
 "List.cons.injEq",
 "_private.Init.Data.Order.Ord.0.Std.instLawfulBEqOrd._simp_2",
 "Lean.Compiler.InlineAttributeKind._sizeOf_inst",
 "BitVec.resRec.eq_2",
 "Lean.ParserDescr.sepBy1.elim",
 "Rat.mkRat_eq_iff",
 "instSelfSliceSubarrayDataSubarray._proof_1",
 "Nat.max_min_distrib_right",
 "Lean.Syntax.instBEq",
 "List.dropLastTR",
 "Lean.ScopedEnvExtension.Descr.name._autoParam",
 "USize.toISize_and",
 "Lean.instExceptToEmojiOption",
 "_private.Init.Data.Nat.Lemmas.0.Nat.min_assoc.match_1_1",
 "Lean.PersistentArray.root",
 "List.set_drop",
 "Lean.Grind.Int.lt_eq",
 "Std.DTreeMap.Internal.Impl.Const.getEntryLE._unsafe_rec",
 "String._aux_Init_Data_String_Extra___macroRules_tacticDecreasing_trivial_1",
 "_private.Init.Data.UInt.Lemmas.0.UInt8.toUInt16_lt._simp_1_1",
 "Nat.instIdempotentOpMin",
 "Std.DTreeMap.Internal.Impl.keyAtIdxD._unsafe_rec",
 "Sum.bnot_isRight",
 "_private.Init.Data.Rat.Lemmas.0.Rat.divInt.match_3.eq_1",
 "List.mapA._unsafe_rec",
 "_private.Lean.Meta.GetUnfoldableConst.0.Lean.Meta.canUnfoldDefault",
 "Std.DTreeMap.Internal.Impl.maxView._proof_9",
 "Lean.Parser.Tactic.Conv.simpTrace",
 "_private.Lean.Parser.Command.0.Lean.Parser.Term.precheckedQuot._regBuiltin.Lean.Parser.Term.precheckedQuot.formatter_7",
 "Lean.Elab.ContextInfo.mk.inj",
 "Array.mem_attachWith",
 "Array.getInternal",
 "Lean.Parser.RecoveryContext",
 "Vector.range'_one",
 "Lean.MessageData.ofConstName",
 "_private.Init.Data.UInt.Lemmas.0.USize.toUInt16_eq._simp_1_2",
 "Lean.Language.Snapshot.mk._flat_ctor",
 "instInhabitedISize",
 "List.Perm.cons_inv",
 "Std.Iterators.PostconditionT.bind_pure",
 "Lean.Language.SnapshotTree._sizeOf_4",
 "Lean.Syntax.rec",
 "Lean.EnvExtension.mkInitial",
 "Lean.Parser.ParserModuleContext.currNamespace._default",
 "Int.Linear.le_of_le_diseq",
 "ISize.sub_right_inj._simp_1",
 "String.iter",
 "Int16.zero_or",
 "Nat.gcd_le_mul._simp_1",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.toNat_lt_two_pow_sub_clz._proof_1_5",
 "_private.Init.Data.BitVec.Bootstrap.0.BitVec.getElem_setWidth._proof_1_4",
 "_private.Lean.Data.Lsp.Utf16.0.String.utf16PosToCodepointPosFromAux._unsafe_rec",
 "Int16.toInt",
 "Lean.Elab.Term.SavedContext.mk.inj",
 "_private.Lean.Meta.DiscrTree.0.Lean.Meta.DiscrTree.getUnify.process._unsafe_rec",
 "List.cons.sizeOf_spec",
 "Std.DTreeMap.Internal.Impl.minKey._unary._proof_2",
 "Array.appendCore",
 "Array.foldrM_filter",
 "_private.Init.Data.SInt.Lemmas.0.Int8.toInt32_lt._simp_1_1",
 "_private.Init.Data.Int.DivMod.Lemmas.0.Int.mod_bmod_mul_of_pos._proof_1_4",
 "Lean.Meta.Config.zeta._default",
 "Lean.Elab.ElabInfo.noConfusion",
 "_aux_Init_Control_Basic___unexpand_Functor_mapRev_1",
 "Lean.beqIRPhases._@.Lean.Environment.3214907407._hygCtx._hyg.14",
 "_private.Init.Data.List.Lemmas.0.List.ne_nil_of_length_eq_add_one.match_1_1",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.toInt_sub_toInt_lt_twoPow_iff._proof_1_4",
 "Std.Packages.LinearOrderOfOrdArgs.max_eq._autoParam",
 "Lean.Parser.Priority.numPrio.formatter",
 "Lean.Omega.Coeffs.get_nil",
 "Nat.dvd_mul_left_of_dvd",
 "List.foldlM_cons",
 "_private.Lean.Meta.DiscrTree.0.Lean.Meta.DiscrTree.tmpMVarId",
 "Array.anyM",
 "Lean.Parser.Term.liftMethod.parenthesizer",
 "_private.Init.Data.UInt.Bitwise.0.UInt16.or_eq_zero_iff._simp_1_1",
 "_private.Init.Data.AC.0.Lean.Data.AC.evalList.match_1.eq_3",
 "Std.DTreeMap.Raw.empty",
 "Lean.Grind.Ring.toAddCommGroup._proof_3",
 "Lean.PrettyPrinter.Formatter.Context.options",
 "Lean.Grind.NoNatZeroDivisors.mk",
 "Array.elem_eq_mem",
 "Std.PartialOrderPackage.casesOn",
 "_private.Lean.Parser.Extension.0.Lean.Parser.isParserAlias.match_1",
 "Lean.Elab.Tactic.CacheKey.mk.injEq",
 "Std.PRange.instRangeSizeClosedNat",
 "Option.attach_map",
 "_private.Init.Data.Array.BinSearch.0.Array.binInsertAux.match_1.splitter",
 "Lean.Grind.CommRing.norm_int",
 "Lean.PersistentHashMap.insertAux._unsafe_rec",
 "List.Pairwise.filter",
 "Lean.belowSuffix",
 "Prod.instWellFoundedRelation",
 "_private.Std.Data.DTreeMap.Internal.Balancing.0.Std.DTreeMap.Internal.Impl.balance!_eq_balanceₘ._proof_1_9",
 "unexpandTSyntaxArray",
 "StateT.instMonad",
 "Int32.not_le",
 "_private.Init.Data.SInt.Bitwise.0.Int32.xor_left_inj._simp_1_1",
 "List.any_filterMap",
 "_private.Init.Data.Int.Lemmas.0.Int.add_assoc.aux1",
 "Lean.Omega.IntList.add_nil",
 "Std.DTreeMap.Internal.Impl.size_bin",
 "Int.neg_add",
 "_private.Lean.Environment.0.Lean.ImportedModule.publicModule?",
 "Lean.Omega.Constraint.combo",
 "Lean.ImportArtifacts.recOn",
 "List.range.loop.match_1",
 "Int64.toNatClampNeg_ofInt_of_le",
 "Int.fmod_eq_of_lt",
 "_private.Lean.Meta.WHNF.0.Lean.Meta.isWFRec",
 "USize.toUInt16_ofBitVec",
 "_private.Init.Data.Range.Polymorphic.Instances.0.Std.PRange.LawfulRangeSize.open_of_closed._simp_8",
 "UInt64.toFin_ofNatTruncate_of_le",
 "List.nil_prefix",
 "Lean.Server.RpcEncodable.recOn",
 "MonadReader.rec",
 "Bool.and_iff_left_iff_imp",
 "WellFoundedRelation.mk._flat_ctor",
 "Array.getElem_zero_filterMap._proof_1",
 "Lean.Parser.RecoveryContext.initialSize",
 "Lean.IR.LitVal.ctorElim",
 "USize.ofNat_sub",
 "Std.DTreeMap.Internal.Impl.Const.getThenInsertIfNew?.eq_1",
 "_private.Lean.Compiler.IR.Format.0.Lean.IR.formatIRType.match_1",
 "List.finIdxOf?",
 "List.head_append._proof_2",
 "Lean.ConstructorVal.casesOn",
 "Lean.Widget.WidgetInstance.casesOn",
 "Int32.le_iff_lt_or_eq",
 "Std.Iterators.IteratorLoop.WithWF.rec",
 "Lean.Grind.instDivUSizeUintNumBits",
 "UInt64.ofFin_mk",
 "Array.mem_ite_empty_left._simp_1",
 "UInt32.add",
 "Lean.Syntax.modifyArgs",
 "_private.Init.Data.Iterators.Lemmas.Consumers.Loop.0.Std.Iterators.IterM.DefaultConsumers.forIn'_eq_match_step.match_3.splitter",
 "Lean.IR.IRType.tobject",
 "Int32.toBitVec_toISize",
 "_private.Init.Data.List.Perm.0.List.not_perm_nil_cons.match_1_1",
 "Lean.Compiler.LCNF.LetValue.proj",
 "Vector.toList_eq_nil_iff._simp_1",
 "USize.intCast_neg",
 "Int32.ofNat_lt_iff_lt",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.reverse.match_1.eq_1",
 "Fin.subNat",
 "Array.forIn'._proof_2",
 "Nat.log2_terminates",
 "Vector.find?_range'_eq_none",
 "_private.Lean.Meta.DiscrTreeTypes.0.Lean.Meta.DiscrTree.reprKey.match_1._@.Lean.Meta.DiscrTreeTypes.1842282792._hygCtx._hyg.141",
 "ISize._sizeOf_1",
 "LT.rec",
 "List.findIdx.eq_1",
 "Lean.Grind.CommRing.Poly.powC.eq_3",
 "BitVec.udiv_eq_and",
 "_private.Init.Data.List.Nat.TakeDrop.0.List.take_eq_take_iff.match_1_1",
 "DoResultPR.recOn",
 "UInt64.shiftRight_and",
 "Array.getElem?_extract_of_lt",
 "_private.Lean.Parser.Term.0.Lean.Parser.Term.attrKind._regBuiltin.Lean.Parser.Term.attrKind.docString_1",
 "_private.Init.Data.UInt.Bitwise.0.USize.toUInt32_shiftLeft_mod._simp_1_1",
 "_private.Init.Data.List.Nat.TakeDrop.0.List.takeWhile_eq_take_findIdx_not._simp_1_1",
 "BitVec.toNat_intMin_of_pos",
 "Std.DTreeMap.Raw.maxEntry!",
 "_private.Init.Data.Int.Order.0.Int.eq_succ_of_zero_lt.match_1_1",
 "Lean.Meta.SynthInstanceCacheKey.ctorIdx",
 "Int.Linear.cmod_eq_zero_iff_emod_eq_zero",
 "Nat.mod_two_not_eq_one._simp_1",
 "_private.Lean.Environment.0.Lean.EnvExtension.modifyState.match_14",
 "Lean.Parser.SyntaxNodeKindSet.insert",
 "_private.Std.Data.DTreeMap.Internal.Operations.0.Std.DTreeMap.Internal.Impl.link2._proof_36",
 "BitVec.getElem_setWidth",
 "_private.Lean.Parser.Command.0.Lean.Parser.Command.include._regBuiltin.Lean.Parser.Command.include_1",
 "_private.Lean.Parser.Command.0.Lean.Parser.Command.print._regBuiltin.Lean.Parser.Command.print.declRange_3",
 "_private.Init.Data.List.Count.0.List.boole_getElem_le_countP._simp_1_1",
 "Lean.Expr.consumeTypeAnnotations._unsafe_rec",
 "UInt32.toNat_toUInt64",
 "Array._aux_Init_Data_Array_Perm___unexpand_Array_Perm_1",
 "CoeTail.mk",
 "Std.Iterators.LawfulIteratorCollect",
 "_private.Init.Data.SInt.Lemmas.0.ISize.ofInt_mul._simp_1_1",
 "Std.DTreeMap.Raw.getEntryGTD",
 "Nat.gcd_add_one",
 "_private.Init.Data.String.Extra.0.String.removeNumLeadingSpaces.consumeSpaces._mutual.eq_def",
 "Lean.PersistentLevelMap",
 "_private.Init.Data.Nat.Basic.0.Nat.pred_le_iff_le_succ.match_1_1",
 "List.not_of_lt_findIdx",
 "Lean.Elab.InfoTree.below_6",
 "_private.Lean.Parser.Do.0.Lean.Parser.Term.doLetRec._regBuiltin.Lean.Parser.Term.doLetRec.formatter_7",
 "_private.Lean.Elab.Attributes.0.Lean.Elab.elabAttr.match_3",
 "String.defaultRange._@.Lean.Syntax.2413389941._hygCtx._hyg.22",
 "Lean.Kernel.Exception.deterministicTimeout.sizeOf_spec",
 "Char.instDecidableLt",
 "Ne.intro",
 "List.instDecidablePairwise._unsafe_rec",
 "_private.Init.System.IO.0.IO.iterate.match_1",
 "List.foldrM_cons",
 "Vector.find?_push_eq_some._simp_1",
 "_private.Init.Data.List.Lemmas.0.List.getElem?_eq_some_iff.match_1_1",
 "Lean.Grind.Ring.toAddCommGroup",
 "Vector.back?_mapIdx",
 "_private.Init.Data.Vector.Attach.0.Vector.pmap_eq_pmapImpl._simp_1_3",
 "Thunk.mk.sizeOf_spec",
 "_private.Lean.Parser.Basic.0.Lean.Parser.orelseFnCore.match_1",
 "Std.Format.rec",
 "_private.Init.Meta.0.Lean.Syntax.setInfo.match_1",
 "Lean.Json.instToString",
 "Lean.ErrorExplanation.Metadata.severity",
 "IO.FS.Mode.readWrite.elim",
 "_private.Init.Data.Iterators.Lemmas.Combinators.Monadic.Attach.0.Std.Iterators.Types.Attach.Monadic.modifyStep.match_1.eq_1",
 "_private.Lean.Environment.0.Lean.subsumesInfo.match_1",
 "_private.Init.Data.List.Impl.0.List.modifyTR.eq_1",
 "Nat.any_eq_anyTR",
 "Lean.Elab.PartialContextInfo.commandCtx.sizeOf_spec",
 "Lean.Grind.CommRing.Poly.denote.match_1",
 "Vector.mem_singleton",
 "Lean.ErrorExplanation.toJsonMetadata._@.Lean.ErrorExplanation.4223505767._hygCtx._hyg.49",
 "Int.neg_lt_neg_iff",
 "Lean.Grind.CommRing.casesOn",
 "Lean.Elab.unsupportedSyntaxExceptionId",
 "_private.Lean.Meta.WHNF.0.Lean.Meta.getConstInfoNoEx?",
 "Array.getElem?_zipWith",
 "Lean.Expr.getAppNumArgs'",
 "Vector.map_inj_right",
 "UInt64.ofBitVec_pow",
 "List.map",
 "List.min_findIdx_findIdx",
 "_private.Init.Data.Format.Basic.0.Std.Format.WorkGroup._sizeOf_inst",
 "_private.Std.Data.DTreeMap.Internal.Queries.0.Std.DTreeMap.Internal.Impl.Const.maxEntry.match_1.eq_2",
 "List.mem_range",
 "Lean.Elab.CommandInfo._sizeOf_inst",
 "Array.foldlM_unattach.match_1",
 "Lean.Parser.Term.macroDollarArg.parenthesizer",
 "Lean.choiceKind",
 "Lean.Grind.Ring.OfSemiring.Expr.denote._unsafe_rec",
 "Bool.coe_iff_coe",
 "IntCast.casesOn",
 "Std.DTreeMap.getKeyGTD",
 "String.foldrAux",
 "Lean.Expr.eta._sunfold",
 "Std.Iterators.IteratorSize.ctorIdx",
 "Lean.mkOr",
 "Std.Internal.LawfulMonadLiftFunction.lift_seqLeft",
 "Lean.hashImport._@.Lean.Setup.2279959588._hygCtx._hyg.97",
 "Lean.IR.DeclInfo.recOn",
 "Lean.IR.instToFormatArg._private_1",
 "Int.ediv_nonneg_of_nonneg_of_nonneg",
 "Lean.ConstantInfo.value?",
 "_private.Std.Data.DTreeMap.Internal.Operations.0.Std.DTreeMap.Internal.Impl.insertMin._proof_14",
 "Lean.Elab.Tactic.TacticParsedSnapshot._sizeOf_5_eq",
 "Array.anyM.loop._unsafe_rec",
 "Fin.intCast",
 "_private.Init.Data.List.Lemmas.0.List.forall_mem_filterMap._simp_1_1",
 "Int.add_lt_add_iff_right._simp_1",
 "Lean.Syntax.setTailInfo",
 "Std.DTreeMap.Internal.Impl.Const.maxEntryD.match_1",
 "List.head_append_right._proof_1",
 "instInhabitedEIO",
 "Bind.recOn",
 "UInt8.val_val_eq_toNat",
 "Lean.Meta.reduceBinNatOp",
 "Std.DTreeMap.Raw.keyAtIdxD",
 "System.Platform.System.Platform.dvd_numBits",
 "Lean.Parser.SyntaxStack.noConfusion",
 "List.find?_filterMap",
 "Std.TreeMap.Raw.foldrM",
 "_private.Init.Data.List.Perm.0.List.isPerm_iff.match_1_1",
 "Lean.Server.ReferencedObject.obj",
 "Lean.ConstantInfo.opaqueInfo.inj",
 "USize.left_le_or",
 "instOrOpInt16",
 "_private.Init.Data.Vector.Lemmas.0.Vector.swap_mk._proof_1",
 "Std.PartialOrderPackage.toIsPartialOrder",
 "Array.foldlM.loop.congr_simp",
 "BitVec.umulOverflow",
 "instSizeOfDefault",
 "_private.Init.Data.List.Impl.0.List.insertIdxTR.go.eq_3",
 "Fin.pos_iff_nonempty",
 "Int.max_min_distrib_left",
 "_private.Init.Core.0.Quotient.rel._proof_1",
 "Int.toNat_sub''",
 "List.instDecidablePairwise.match_1",
 "Lean.Elab.defaultPartialFixpointType._@.Lean.Elab.PreDefinition.TerminationHint.2619529418._hygCtx._hyg.8",
 "_private.Init.Data.Vector.Extract.0.Vector.extract_set._proof_1",
 "Lean.Grind.IsCharP.natCast_eq_iff_of_lt",
 "Std.DTreeMap.Internal.Impl.singleL",
 "_private.Init.Data.Range.Lemmas.0.Std.Range.forIn'.eq_1",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.reverse_append._proof_1",
 "Lean.Parser.Term.matchDiscr.parenthesizer",
 "_private.Init.Data.List.Lemmas.0.List.foldl_filterMap.match_1.eq_2",
 "_private.Init.Data.List.Sort.Lemmas.0.List.mergeSort.eq_3",
 "Lean.Meta.PostponedEntry.mk",
 "USize.ofBitVec",
 "Array.flatten_mkArray_replicate",
 "Lean.Json.compress",
 "Std.DTreeMap.Internal.Impl.getEntryGT._unsafe_rec",
 "ISize.toUSize_xor",
 "_private.Std.Data.DTreeMap.Internal.Balancing.0.Std.DTreeMap.Internal.Impl.balance._proof_18",
 "_private.Init.Data.Array.Basic.0.Array.isPrefixOfAux._proof_1",
 "Fin.fin_one_eq_zero",
 "Lean.Grind.AC.simp_suffix_cert.eq_1",
 "_private.Lean.Exception.0.Lean.throwError.match_1",
 "_private.Lean.LocalContext.0.Lean.LocalContext.mkLocalDecl.match_1",
 "UInt16.toUSize_div",
 "Int.mul_left_comm",
 "_private.Init.Data.Vector.Range.0.Vector.zipIdx_eq_append_iff._simp_1_2",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.toNat_shiftConcat_lt_of_lt._proof_1_1",
 "Substring.contains",
 "Lean.Grind.ToInt.Div.mk",
 "Lean.Syntax.ident.sizeOf_spec",
 "Lean.Grind.ToInt.Sub.toInt_sub",
 "System.Uri.UriEscape.rfc3986ReservedChars",
 "Option.merge.eq_3",
 "Eq",
 "UInt32.ofBitVec_toBitVec_eq",
 "Lean.PrefixTreeNode.rec_2",
 "Std.Commutative.rec",
 "_private.Init.Data.List.ToArray.0.List.insertIdx_loop_toArray._simp_1_13",
 "Option.isSome_of_isSome_pfilter",
 "_private.Init.Data.Array.Basic.0.Array.findM?.match_1",
 "Lean.Parser.Tactic.DecideConfig.noConfusion",
 "_private.Init.Data.Rat.Lemmas.0.Rat.mul_neg._simp_1_1",
 "UInt32.add_eq_left",
 "Lean.Parser.ParserState.mergeErrors",
 "Std.DTreeMap.Raw.Const.get?",
 "Lean.Grind.AC.Seq.insert_k_eq_insert",
 "Lean.getStructureInfo",
 "_private.Lean.ErrorExplanation.0.Lean.ErrorExplanation.reprValidationState._@.Lean.ErrorExplanation.165795801._hygCtx._hyg.29",
 "Lean.PrettyPrinter.Formatter.node.formatter",
 "Lean.Meta.coerceToSort?",
 "Nat.mod_zero",
 "_private.Init.Meta.0.Lean.Syntax.isNatLitAux",
 "_private.Init.Data.BitVec.Bitblast.0.BitVec.getLsbD_add_add_bool.match_1_1",
 "MonadStateOf",
 "Vector.getElem?_push_size",
 "Lean.IR.Expr.isShared",
 "ISize.toInt8_and",
 "Lean.Parser.ppSpace.parenthesizer",
 "Lean.Grind.Linarith.eq_coeff",
 "Std.DTreeMap.Internal.Impl.minKey._unary.eq_def",
 "Lean.Meta.isExprDefEqGuarded",
 "Lean.Grind.CommRing.hashExpr.«_@».Init.Grind.Ring.Poly.3091913453._hygCtx._hyg.188._sunfold",
 "Bool.or_and_distrib_right",
 "List.get?._unsafe_rec",
 "Int.Linear.Poly.denote_div_eq_of_divAll",
 "Nat.eq_of_mul_eq_mul_left",
 "Lean.Grind.Ring.OfSemiring.Expr.add.sizeOf_spec",
 "BitVec.not_xor_left",
 "Vector.swap",
 "Lean.Meta.Instances.instanceNames",
 "_private.Init.Data.Array.MapIdx.0.Array.mapIdx_eq_mapIdx_iff._simp_1_1",
 "ISize.not_lt",
 "Int64.add_right_neg",
 "UInt64.toUInt8_mod",
 "ISize.ofInt_mul",
 "UInt64.and_zero",
 "_auto._@.Init.Data.Nat.Bitwise.Lemmas.3208365579._hygCtx._hyg.67",
 "_private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.PRange.RangeIterator.instFinitenessRelation._proof_1",
 "BitVec.not_lt",
 "BitVec.getElem_signExtend",
 "Lean.Parser.ParserAliasInfo.declName",
 "Int8.toInt8_toUInt8",
 "_private.Init.Data.Vector.Find.0.Vector.getElem_zero_flatten.proof._simp_1_6",
 "Lean.Core.CoreM",
 "_private.Init.Data.SInt.Bitwise.0.Bool.toInt8.eq_1",
 "Lean.Meta.DiscrTree.Key.other.elim",
 "Lean.ScopedEnvExtension.ScopedEntries.map",
 "Std.PRange.instDecidableRelBoundIsSatisfied",
 "Lean.Syntax.getHeadInfo?",
 "_private.Lean.Parser.Basic.0.Lean.Parser.nameLitAux",
 "_private.Std.Data.DTreeMap.Internal.Operations.0.Std.DTreeMap.Internal.Impl.link2._proof_29",
 "Lean.Meta.Config.casesOn",
 "_private.Init.Data.Array.InsertionSort.0.Array.insertionSort.traverse.match_1",
 "IO.instLETaskState",
 "Lean.Compiler.LCNF.LetDecl.rec",
 "_private.Lean.Parser.Basic.0.Lean.Parser.withAntiquotSuffixSpliceFn",
 "UInt64.toUInt16_lt._simp_1",
 "_private.Lean.ErrorExplanation.0.Lean.ErrorExplanation.ValidationState.ofSource",
 "_private.Lean.Meta.WHNF.0.Lean.Meta.mkNullaryCtor.match_1",
 "Std.Format.instBEqFlattenAllowability",
 "Lean.IR.CtorInfo.mk.inj",
 "StateT.get",
 "Lean.Parser.tokenFn",
 "UInt16.toFin.ofNat",
 "Lean.Compiler.LCNF.instBEqDecl",
 "_private.Init.Data.List.Nat.Sublist.0.List.IsSuffix.getElem._proof_1",
 "Lean.Parser.Term.dynamicQuot.formatter",
 "Std.instIrreflLtOfIsPreorderOfLawfulOrderLT",
 "Vector.find?_eq_none._simp_1",
 "Lean.LBool.toCtorIdx",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.getMsbD_setWidth._proof_1_1",
 "Nat.ge_two_pow_implies_high_bit_true",
 "Lean.Kernel.Environment.Diagnostics.isEnabled",
 "_private.Init.Data.List.Basic.0.List.drop_eq_nil_of_le.match_1_1",
 "toBoolUsing_eq_true",
 "Option.instForM",
 "_private.Init.Data.Range.Polymorphic.RangeIterator.0.Std.PRange.RangeIterator.instIteratorAccess.match_1.eq_2",
 "Lean.ModuleSetup.mk._flat_ctor",
 "Array.toArrayAux_eq",
 "Lean.Int.mkInstHMod",
 "Lean.Parser.ParserExtension.Entry.token.injEq",
 "Lean.IR.DeclInfo.mk.injEq",
 "Lean.Elab.Term.applyAttributesAt",
 "Option.mem_map_of_mem",
 "Vector.any_toArray",
 "Vector.forall_mem_singleton",
 "_private.Init.Data.Range.Basic.0.Std.Range.forIn'.loop.match_1",
 "_private.Init.Data.Array.Erase.0.Array.eraseIdx_set_gt._proof_4",
 "_private.Init.Data.List.Nat.Count.0.List.count_insert._proof_1_2",
 "Lean.Core.SavedState.mk.inj",
 "Lean.Ptr.mk._flat_ctor",
 "_private.Lean.Expr.0.Lean.intLEPred",
 "Lean.Parser.Term.doLetExpr",
 "_private.Std.Data.DTreeMap.Internal.Operations.0.Std.DTreeMap.Internal.Impl.insert.match_3.eq_3",
 "IO.CancelToken.recOn",
 "Std.PRange.instLawfulUpwardEnumerableLENat",
 "Lean.Order.«term_⊑_»",
 "Lean.TSyntax.noConfusionType",
 "BitVec.toInt_extractLsb'",
 "Vector.mapFinIdx_reverse._proof_2",
 "Fin.rev_zero",
 "_private.Lean.Meta.WHNF.0.Lean.Meta.getStuckMVar?.match_15",
 "ofBoolUsing_eq_true",
 "Fin.induction.go._proof_1",
 "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_5",
 "Std.Iterators.IterM.fold_eq_foldM",
 "ExceptT.bindCont.match_1",
 "_aux_Init_Notation___unexpand_Prod_1",
 "toBoolUsing",
 "Std.DTreeMap.Internal.Impl.Ordered.mem_inner_iff_mem_left",
 "_private.Std.Data.DTreeMap.Internal.Operations.0.Std.DTreeMap.Internal.Impl.erase._proof_5",
 "Lean.IR.Arg._sizeOf_1",
 "_private.Lean.Expr.0.Lean.Expr.isBinding.match_1",
 "Lean.Parser.Command.genInjectiveTheorems",
 "Lean.Compiler.LCNF.MonadFVarSubstState.mk",
 "Fin.castSucc_fin_succ",
 "_private.Init.Data.BitVec.Lemmas.0.BitVec.toNat_div_toNat_lt._proof_1_7",
 "ISize.zero_lt_one",
 "Lean.Compiler.LCNF.defaultPassInstaller._@.Lean.Compiler.LCNF.PassManager.3231648392._hygCtx._hyg.29",
 "Lean.getPPInstances",
 "Nat.modCore.go.congr_simp",
 "UInt32.not_neg_one",
 "Lean.Grind.CommRing.Expr.sub.inj",
 "Vector.mem_range",
 "Lean.Meta.ExtractLetsConfig.mk.sizeOf_spec",
 "Vector.replace_toArray",
 "_private.Init.Data.Fin.Lemmas.0.Fin.pos'.match_1_1",
 "Nat.xor_assoc",
 "_private.Init.Data.List.Lemmas.0.List.length_eq_one_iff.match_1_3",
 "Lean.Parser.numLit.parenthesizer",
 "List.drop_modifyHead_of_pos",
 "List.pairwise_map",
 "_private.Lean.Parser.Command.0.Lean.Parser.Tactic.open._regBuiltin.Lean.Parser.Tactic.open.declRange_5",
 "_private.Init.Data.BitVec.Bitblast.0.BitVec.carry_extractLsb'_eq_carry._simp_1_3",
 "Std.PRange.BoundedUpwardEnumerable.rec",
 "Lean.PersistentHashMap.Stats.casesOn",
 "_private.Init.Data.Array.Lemmas.0.Array.map_eq_iff._simp_1_1",
 "_private.Init.Meta.0.Lean.Name.appendBefore.match_1",
 "Lean.Elab.InlayHintLabel.ctorElim",
 "Lean.Grind.CommRing.Mon.revlexFuel.eq_4",
 "Bool.or_false",
 "Lean.Elab.Term.MVarErrorKind._sizeOf_inst",
 "Lean.Parser.Term.doMatchExprAlts.parenthesizer",
 "ST.Prim.Ref.modifyUnsafe",
 "Option.mem_def",
 "_private.Lean.Parser.Do.0.Lean.Parser.Term.doContinue._regBuiltin.Lean.Parser.Term.doContinue_1",
 "Option.pelim_join._proof_1",
 "BitVec.getElem_eq_testBit_toNat",
 "_private.Init.Data.Dyadic.Basic.0.Dyadic.blt_iff_toRat._simp_1_6",
 "Lean.Parser.AliasTable",
 "_private.Lean.Elab.Term.0.Lean.Elab.Term.elabUsingElabFnsAux.match_1",
 "Std.Iterators.Iter.Partial.fold",
 "Bool.and_iff_right_iff_imp",
 "Vector.pmap"]

@[noinline]
def bench (pattern : String) : IO Unit := do
  let mut n := 0
  for c in consts do
    if fuzzyMatch pattern c then n := n + 1
  IO.println s!"{n} matches"

public def main : IO Unit := do
  bench "L"
  bench "Lean."
  bench "Lean.Expr"
  bench "Lean.Expr.const"
  bench "B"
  bench "BitVec."
  bench "BitVec.not_lt"
  bench "I"
  bench "Int"
  bench "Int.add"
  bench "Int.add_"
  bench "Int.add_assoc"
