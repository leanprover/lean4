// Lean compiler output
// Module: Lean.Elab.SyntheticMVars
// Imports: Init Lean.Elab.Term Lean.Elab.Tactic.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__4;
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__4;
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2;
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__9;
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9;
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_6__synthesizeSyntheticMVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__8;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__8;
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10;
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__1(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___closed__1;
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_3__synthesizePendingInstMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_repr___main___closed__13;
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___boxed(lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__2;
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_1__resumeElabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__1;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__5;
lean_object* l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__3;
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_3__synthesizePendingInstMVar___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_4__synthesizePendingCoeInstMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_5__checkWithDefault(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_1__resumeElabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Term_liftTacticElabM(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__3;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__5;
lean_object* l___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___boxed(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__6;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___lambda__1___boxed(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__7;
lean_object* l___private_Lean_Elab_SyntheticMVars_6__synthesizeSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos___main(lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVarDeclMVars(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___lambda__1(lean_object*);
extern lean_object* l___private_Lean_Elab_Term_10__postponeElabTerm___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__2;
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__3;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__7;
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Format_repr___main___closed__16;
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__3___boxed(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_4__synthesizePendingCoeInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_EStateM_MonadState___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___closed__1;
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__3(uint8_t);
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__6;
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_box(0);
lean_ctor_set(x_4, 1, x_9);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_apply_2(x_2, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
lean_ctor_set(x_14, 1, x_7);
lean_ctor_set(x_12, 1, x_14);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 2);
x_21 = lean_ctor_get(x_14, 3);
x_22 = lean_ctor_get(x_14, 4);
x_23 = lean_ctor_get(x_14, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_12, 1, x_24);
return x_12;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 5);
lean_inc(x_30);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_31 = x_14;
} else {
 lean_dec_ref(x_14);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 6, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 1);
lean_dec(x_40);
lean_ctor_set(x_38, 1, x_7);
lean_ctor_set(x_12, 1, x_38);
lean_ctor_set(x_12, 0, x_37);
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 2);
x_43 = lean_ctor_get(x_38, 3);
x_44 = lean_ctor_get(x_38, 4);
x_45 = lean_ctor_get(x_38, 5);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_7);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_43);
lean_ctor_set(x_46, 4, x_44);
lean_ctor_set(x_46, 5, x_45);
lean_ctor_set(x_12, 1, x_46);
lean_ctor_set(x_12, 0, x_37);
return x_12;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 5);
lean_inc(x_55);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 lean_ctor_release(x_50, 5);
 x_56 = x_50;
} else {
 lean_dec_ref(x_50);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 6, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_7);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_53);
lean_ctor_set(x_57, 4, x_54);
lean_ctor_set(x_57, 5, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_59 = lean_ctor_get(x_4, 1);
x_60 = lean_ctor_get(x_3, 0);
x_61 = lean_ctor_get(x_3, 1);
x_62 = lean_ctor_get(x_3, 2);
x_63 = lean_ctor_get(x_3, 3);
x_64 = lean_ctor_get(x_3, 4);
x_65 = lean_ctor_get(x_3, 5);
x_66 = lean_ctor_get(x_3, 6);
x_67 = lean_ctor_get(x_3, 7);
x_68 = lean_ctor_get(x_3, 8);
x_69 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_70 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_71 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_72 = lean_ctor_get(x_3, 9);
lean_inc(x_72);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_3);
x_73 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set(x_73, 2, x_62);
lean_ctor_set(x_73, 3, x_63);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_65);
lean_ctor_set(x_73, 6, x_66);
lean_ctor_set(x_73, 7, x_67);
lean_ctor_set(x_73, 8, x_68);
lean_ctor_set(x_73, 9, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*10, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*10 + 1, x_70);
lean_ctor_set_uint8(x_73, sizeof(void*)*10 + 2, x_71);
lean_inc(x_1);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_1);
x_75 = lean_box(0);
lean_ctor_set(x_4, 1, x_75);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_4);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_apply_2(x_2, x_74, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 5);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 6, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_59);
lean_ctor_set(x_89, 2, x_84);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_86);
lean_ctor_set(x_89, 5, x_87);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_81);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_91 = lean_ctor_get(x_78, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_93 = x_78;
} else {
 lean_dec_ref(x_78);
 x_93 = lean_box(0);
}
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_91);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 4);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 5);
lean_inc(x_100);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 lean_ctor_release(x_95, 2);
 lean_ctor_release(x_95, 3);
 lean_ctor_release(x_95, 4);
 lean_ctor_release(x_95, 5);
 x_101 = x_95;
} else {
 lean_dec_ref(x_95);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 6, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_59);
lean_ctor_set(x_102, 2, x_97);
lean_ctor_set(x_102, 3, x_98);
lean_ctor_set(x_102, 4, x_99);
lean_ctor_set(x_102, 5, x_100);
if (lean_is_scalar(x_93)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_93;
}
lean_ctor_set(x_103, 0, x_94);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_104 = lean_ctor_get(x_4, 0);
x_105 = lean_ctor_get(x_4, 1);
x_106 = lean_ctor_get(x_4, 2);
x_107 = lean_ctor_get(x_4, 3);
x_108 = lean_ctor_get(x_4, 4);
x_109 = lean_ctor_get(x_4, 5);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_4);
x_110 = lean_ctor_get(x_3, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_3, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_3, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_3, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_3, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_3, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_3, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_3, 7);
lean_inc(x_117);
x_118 = lean_ctor_get(x_3, 8);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_120 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_121 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_122 = lean_ctor_get(x_3, 9);
lean_inc(x_122);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 x_123 = x_3;
} else {
 lean_dec_ref(x_3);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 10, 3);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_110);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_124, 2, x_112);
lean_ctor_set(x_124, 3, x_113);
lean_ctor_set(x_124, 4, x_114);
lean_ctor_set(x_124, 5, x_115);
lean_ctor_set(x_124, 6, x_116);
lean_ctor_set(x_124, 7, x_117);
lean_ctor_set(x_124, 8, x_118);
lean_ctor_set(x_124, 9, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*10, x_119);
lean_ctor_set_uint8(x_124, sizeof(void*)*10 + 1, x_120);
lean_ctor_set_uint8(x_124, sizeof(void*)*10 + 2, x_121);
lean_inc(x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_1);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_127, 0, x_104);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_106);
lean_ctor_set(x_127, 3, x_107);
lean_ctor_set(x_127, 4, x_108);
lean_ctor_set(x_127, 5, x_109);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_apply_2(x_2, x_125, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_132, 4);
lean_inc(x_138);
x_139 = lean_ctor_get(x_132, 5);
lean_inc(x_139);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 lean_ctor_release(x_132, 4);
 lean_ctor_release(x_132, 5);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 6, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_105);
lean_ctor_set(x_141, 2, x_136);
lean_ctor_set(x_141, 3, x_137);
lean_ctor_set(x_141, 4, x_138);
lean_ctor_set(x_141, 5, x_139);
if (lean_is_scalar(x_134)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_134;
}
lean_ctor_set(x_142, 0, x_133);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_143 = lean_ctor_get(x_130, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_130, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_145 = x_130;
} else {
 lean_dec_ref(x_130);
 x_145 = lean_box(0);
}
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_143);
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 4);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 5);
lean_inc(x_152);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 lean_ctor_release(x_147, 5);
 x_153 = x_147;
} else {
 lean_dec_ref(x_147);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 6, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_105);
lean_ctor_set(x_154, 2, x_149);
lean_ctor_set(x_154, 3, x_150);
lean_ctor_set(x_154, 4, x_151);
lean_ctor_set(x_154, 5, x_152);
if (lean_is_scalar(x_145)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_145;
}
lean_ctor_set(x_155, 0, x_146);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Term_withMVarContext___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftTacticElabM___rarg), 4, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic failed, result still contain metavariables");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_mkMVar(x_1);
lean_inc(x_2);
x_5 = l_Lean_Elab_Term_instantiateMVars(x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_hasExprMVar(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_5);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_7);
x_12 = l_Lean_indentExpr(x_11);
x_13 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Term_throwError___rarg(x_14, x_2, x_8);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = l_Lean_Expr_hasExprMVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = l_Lean_indentExpr(x_21);
x_23 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_Term_throwError___rarg(x_24, x_2, x_17);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_evalTactic___main(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Term_runTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
x_10 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_9, x_1);
lean_ctor_set(x_7, 1, x_10);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_Elab_Term_liftTacticElabM___rarg(x_1, x_5, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 9);
lean_inc(x_15);
x_16 = l_Lean_Syntax_getTailWithPos___main(x_15);
x_17 = l_List_isEmpty___rarg(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Elab_replaceRef(x_15, x_15);
lean_dec(x_15);
lean_ctor_set(x_3, 9, x_18);
if (x_17 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_reportUnsolvedGoals(x_12, x_3, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_12);
x_24 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_3, x_13);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = l_Lean_Elab_replaceRef(x_25, x_15);
lean_dec(x_15);
lean_dec(x_25);
lean_ctor_set(x_3, 9, x_26);
if (x_17 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_1);
x_27 = l_Lean_Elab_Term_reportUnsolvedGoals(x_12, x_3, x_13);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_12);
x_32 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_3, x_13);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_ctor_get(x_3, 3);
x_37 = lean_ctor_get(x_3, 4);
x_38 = lean_ctor_get(x_3, 5);
x_39 = lean_ctor_get(x_3, 6);
x_40 = lean_ctor_get(x_3, 7);
x_41 = lean_ctor_get(x_3, 8);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_45 = lean_ctor_get(x_3, 9);
lean_inc(x_45);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
lean_inc(x_45);
x_46 = l_Lean_Syntax_getTailWithPos___main(x_45);
x_47 = l_List_isEmpty___rarg(x_12);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_Elab_replaceRef(x_45, x_45);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_34);
lean_ctor_set(x_49, 2, x_35);
lean_ctor_set(x_49, 3, x_36);
lean_ctor_set(x_49, 4, x_37);
lean_ctor_set(x_49, 5, x_38);
lean_ctor_set(x_49, 6, x_39);
lean_ctor_set(x_49, 7, x_40);
lean_ctor_set(x_49, 8, x_41);
lean_ctor_set(x_49, 9, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_49, sizeof(void*)*10 + 1, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*10 + 2, x_44);
if (x_47 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_50 = l_Lean_Elab_Term_reportUnsolvedGoals(x_12, x_49, x_13);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_12);
x_55 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_49, x_13);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
lean_dec(x_46);
x_57 = l_Lean_Elab_replaceRef(x_56, x_45);
lean_dec(x_45);
lean_dec(x_56);
x_58 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_58, 0, x_33);
lean_ctor_set(x_58, 1, x_34);
lean_ctor_set(x_58, 2, x_35);
lean_ctor_set(x_58, 3, x_36);
lean_ctor_set(x_58, 4, x_37);
lean_ctor_set(x_58, 5, x_38);
lean_ctor_set(x_58, 6, x_39);
lean_ctor_set(x_58, 7, x_40);
lean_ctor_set(x_58, 8, x_41);
lean_ctor_set(x_58, 9, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 1, x_43);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 2, x_44);
if (x_47 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_59 = l_Lean_Elab_Term_reportUnsolvedGoals(x_12, x_58, x_13);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; 
lean_dec(x_12);
x_64 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_58, x_13);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_11);
if (x_65 == 0)
{
return x_11;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_11, 0);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_11);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_7, 0);
x_70 = lean_ctor_get(x_7, 1);
x_71 = lean_ctor_get(x_7, 2);
x_72 = lean_ctor_get(x_7, 3);
x_73 = lean_ctor_get(x_7, 4);
x_74 = lean_ctor_get(x_7, 5);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_7);
lean_inc(x_1);
x_75 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_70, x_1);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_72);
lean_ctor_set(x_76, 4, x_73);
lean_ctor_set(x_76, 5, x_74);
lean_ctor_set(x_4, 0, x_76);
lean_inc(x_3);
lean_inc(x_1);
x_77 = l_Lean_Elab_Term_liftTacticElabM___rarg(x_1, x_5, x_3, x_4);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_3, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_3, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_3, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_3, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_3, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_3, 8);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_90 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_91 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_92 = lean_ctor_get(x_3, 9);
lean_inc(x_92);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 x_93 = x_3;
} else {
 lean_dec_ref(x_3);
 x_93 = lean_box(0);
}
lean_inc(x_92);
x_94 = l_Lean_Syntax_getTailWithPos___main(x_92);
x_95 = l_List_isEmpty___rarg(x_78);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Lean_Elab_replaceRef(x_92, x_92);
lean_dec(x_92);
if (lean_is_scalar(x_93)) {
 x_97 = lean_alloc_ctor(0, 10, 3);
} else {
 x_97 = x_93;
}
lean_ctor_set(x_97, 0, x_80);
lean_ctor_set(x_97, 1, x_81);
lean_ctor_set(x_97, 2, x_82);
lean_ctor_set(x_97, 3, x_83);
lean_ctor_set(x_97, 4, x_84);
lean_ctor_set(x_97, 5, x_85);
lean_ctor_set(x_97, 6, x_86);
lean_ctor_set(x_97, 7, x_87);
lean_ctor_set(x_97, 8, x_88);
lean_ctor_set(x_97, 9, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*10, x_89);
lean_ctor_set_uint8(x_97, sizeof(void*)*10 + 1, x_90);
lean_ctor_set_uint8(x_97, sizeof(void*)*10 + 2, x_91);
if (x_95 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_1);
x_98 = l_Lean_Elab_Term_reportUnsolvedGoals(x_78, x_97, x_79);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_78);
x_103 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_97, x_79);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_94, 0);
lean_inc(x_104);
lean_dec(x_94);
x_105 = l_Lean_Elab_replaceRef(x_104, x_92);
lean_dec(x_92);
lean_dec(x_104);
if (lean_is_scalar(x_93)) {
 x_106 = lean_alloc_ctor(0, 10, 3);
} else {
 x_106 = x_93;
}
lean_ctor_set(x_106, 0, x_80);
lean_ctor_set(x_106, 1, x_81);
lean_ctor_set(x_106, 2, x_82);
lean_ctor_set(x_106, 3, x_83);
lean_ctor_set(x_106, 4, x_84);
lean_ctor_set(x_106, 5, x_85);
lean_ctor_set(x_106, 6, x_86);
lean_ctor_set(x_106, 7, x_87);
lean_ctor_set(x_106, 8, x_88);
lean_ctor_set(x_106, 9, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*10, x_89);
lean_ctor_set_uint8(x_106, sizeof(void*)*10 + 1, x_90);
lean_ctor_set_uint8(x_106, sizeof(void*)*10 + 2, x_91);
if (x_95 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_1);
x_107 = l_Lean_Elab_Term_reportUnsolvedGoals(x_78, x_106, x_79);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; 
lean_dec(x_78);
x_112 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_106, x_79);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_3);
lean_dec(x_1);
x_113 = lean_ctor_get(x_77, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_77, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_115 = x_77;
} else {
 lean_dec_ref(x_77);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
x_119 = lean_ctor_get(x_4, 2);
x_120 = lean_ctor_get(x_4, 3);
x_121 = lean_ctor_get(x_4, 4);
x_122 = lean_ctor_get(x_4, 5);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_123 = lean_ctor_get(x_117, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_117, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_117, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_117, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_117, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_117, 5);
lean_inc(x_128);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 x_129 = x_117;
} else {
 lean_dec_ref(x_117);
 x_129 = lean_box(0);
}
lean_inc(x_1);
x_130 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_124, x_1);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 6, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_123);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_131, 2, x_125);
lean_ctor_set(x_131, 3, x_126);
lean_ctor_set(x_131, 4, x_127);
lean_ctor_set(x_131, 5, x_128);
x_132 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_118);
lean_ctor_set(x_132, 2, x_119);
lean_ctor_set(x_132, 3, x_120);
lean_ctor_set(x_132, 4, x_121);
lean_ctor_set(x_132, 5, x_122);
lean_inc(x_3);
lean_inc(x_1);
x_133 = l_Lean_Elab_Term_liftTacticElabM___rarg(x_1, x_5, x_3, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_3, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_3, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_3, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_3, 5);
lean_inc(x_141);
x_142 = lean_ctor_get(x_3, 6);
lean_inc(x_142);
x_143 = lean_ctor_get(x_3, 7);
lean_inc(x_143);
x_144 = lean_ctor_get(x_3, 8);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_146 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_147 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_148 = lean_ctor_get(x_3, 9);
lean_inc(x_148);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 x_149 = x_3;
} else {
 lean_dec_ref(x_3);
 x_149 = lean_box(0);
}
lean_inc(x_148);
x_150 = l_Lean_Syntax_getTailWithPos___main(x_148);
x_151 = l_List_isEmpty___rarg(x_134);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Lean_Elab_replaceRef(x_148, x_148);
lean_dec(x_148);
if (lean_is_scalar(x_149)) {
 x_153 = lean_alloc_ctor(0, 10, 3);
} else {
 x_153 = x_149;
}
lean_ctor_set(x_153, 0, x_136);
lean_ctor_set(x_153, 1, x_137);
lean_ctor_set(x_153, 2, x_138);
lean_ctor_set(x_153, 3, x_139);
lean_ctor_set(x_153, 4, x_140);
lean_ctor_set(x_153, 5, x_141);
lean_ctor_set(x_153, 6, x_142);
lean_ctor_set(x_153, 7, x_143);
lean_ctor_set(x_153, 8, x_144);
lean_ctor_set(x_153, 9, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*10, x_145);
lean_ctor_set_uint8(x_153, sizeof(void*)*10 + 1, x_146);
lean_ctor_set_uint8(x_153, sizeof(void*)*10 + 2, x_147);
if (x_151 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_1);
x_154 = l_Lean_Elab_Term_reportUnsolvedGoals(x_134, x_153, x_135);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
else
{
lean_object* x_159; 
lean_dec(x_134);
x_159 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_153, x_135);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_150, 0);
lean_inc(x_160);
lean_dec(x_150);
x_161 = l_Lean_Elab_replaceRef(x_160, x_148);
lean_dec(x_148);
lean_dec(x_160);
if (lean_is_scalar(x_149)) {
 x_162 = lean_alloc_ctor(0, 10, 3);
} else {
 x_162 = x_149;
}
lean_ctor_set(x_162, 0, x_136);
lean_ctor_set(x_162, 1, x_137);
lean_ctor_set(x_162, 2, x_138);
lean_ctor_set(x_162, 3, x_139);
lean_ctor_set(x_162, 4, x_140);
lean_ctor_set(x_162, 5, x_141);
lean_ctor_set(x_162, 6, x_142);
lean_ctor_set(x_162, 7, x_143);
lean_ctor_set(x_162, 8, x_144);
lean_ctor_set(x_162, 9, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*10, x_145);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 1, x_146);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 2, x_147);
if (x_151 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_1);
x_163 = l_Lean_Elab_Term_reportUnsolvedGoals(x_134, x_162, x_135);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
lean_object* x_168; 
lean_dec(x_134);
x_168 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_162, x_135);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_ctor_get(x_133, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_133, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_171 = x_133;
} else {
 lean_dec_ref(x_133);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_1__resumeElabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*10 + 1, x_8);
x_9 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_8, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 5);
x_16 = lean_ctor_get(x_4, 6);
x_17 = lean_ctor_get(x_4, 7);
x_18 = lean_ctor_get(x_4, 8);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_21 = lean_ctor_get(x_4, 9);
lean_inc(x_21);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_12);
lean_ctor_set(x_23, 3, x_13);
lean_ctor_set(x_23, 4, x_14);
lean_ctor_set(x_23, 5, x_15);
lean_ctor_set(x_23, 6, x_16);
lean_ctor_set(x_23, 7, x_17);
lean_ctor_set(x_23, 8, x_18);
lean_ctor_set(x_23, 9, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 2, x_20);
x_24 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_22, x_23, x_5);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_ctor_set_uint8(x_4, sizeof(void*)*10 + 1, x_3);
x_26 = 0;
x_27 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_26, x_4, x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
x_30 = lean_ctor_get(x_4, 2);
x_31 = lean_ctor_get(x_4, 3);
x_32 = lean_ctor_get(x_4, 4);
x_33 = lean_ctor_get(x_4, 5);
x_34 = lean_ctor_get(x_4, 6);
x_35 = lean_ctor_get(x_4, 7);
x_36 = lean_ctor_get(x_4, 8);
x_37 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_38 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_39 = lean_ctor_get(x_4, 9);
lean_inc(x_39);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_40 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 4, x_32);
lean_ctor_set(x_40, 5, x_33);
lean_ctor_set(x_40, 6, x_34);
lean_ctor_set(x_40, 7, x_35);
lean_ctor_set(x_40, 8, x_36);
lean_ctor_set(x_40, 9, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*10, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*10 + 1, x_3);
lean_ctor_set_uint8(x_40, sizeof(void*)*10 + 2, x_38);
x_41 = 0;
x_42 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_41, x_40, x_5);
return x_42;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_1__resumeElabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Elab_SyntheticMVars_1__resumeElabTerm(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 4);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 5);
lean_inc(x_44);
x_45 = lean_ctor_get(x_6, 6);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 8);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_48 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_50 = lean_ctor_get(x_6, 9);
lean_inc(x_50);
lean_inc(x_50);
lean_inc(x_46);
lean_inc(x_2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
x_51 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_42);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_44);
lean_ctor_set(x_51, 6, x_45);
lean_ctor_set(x_51, 7, x_2);
lean_ctor_set(x_51, 8, x_46);
lean_ctor_set(x_51, 9, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*10, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*10 + 1, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*10 + 2, x_49);
x_52 = l_Lean_Elab_Term_getMVarDecl(x_3, x_51, x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_51);
x_56 = l_Lean_Elab_Term_instantiateMVars(x_55, x_51, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
if (x_1 == 0)
{
uint8_t x_60; lean_object* x_61; 
x_60 = 1;
lean_inc(x_51);
lean_inc(x_59);
lean_inc(x_4);
x_61 = l___private_Lean_Elab_SyntheticMVars_1__resumeElabTerm(x_4, x_59, x_60, x_51, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Elab_replaceRef(x_4, x_50);
lean_dec(x_50);
lean_dec(x_4);
x_65 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_65, 0, x_39);
lean_ctor_set(x_65, 1, x_40);
lean_ctor_set(x_65, 2, x_41);
lean_ctor_set(x_65, 3, x_42);
lean_ctor_set(x_65, 4, x_43);
lean_ctor_set(x_65, 5, x_44);
lean_ctor_set(x_65, 6, x_45);
lean_ctor_set(x_65, 7, x_2);
lean_ctor_set(x_65, 8, x_46);
lean_ctor_set(x_65, 9, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*10, x_47);
lean_ctor_set_uint8(x_65, sizeof(void*)*10 + 1, x_48);
lean_ctor_set_uint8(x_65, sizeof(void*)*10 + 2, x_49);
x_66 = l_Lean_Elab_Term_ensureHasType(x_59, x_62, x_65, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_6);
lean_dec(x_5);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_assignExprMVar(x_3, x_67, x_51, x_68);
lean_dec(x_51);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_box(x_60);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_box(x_60);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_51);
lean_dec(x_3);
x_76 = lean_ctor_get(x_66, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_66, 1);
lean_inc(x_77);
lean_dec(x_66);
x_8 = x_76;
x_9 = x_77;
goto block_38;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_59);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_61, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_61, 1);
lean_inc(x_79);
lean_dec(x_61);
x_8 = x_78;
x_9 = x_79;
goto block_38;
}
}
else
{
uint8_t x_80; lean_object* x_81; 
x_80 = 0;
lean_inc(x_51);
lean_inc(x_59);
lean_inc(x_4);
x_81 = l___private_Lean_Elab_SyntheticMVars_1__resumeElabTerm(x_4, x_59, x_80, x_51, x_58);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Elab_replaceRef(x_4, x_50);
lean_dec(x_50);
lean_dec(x_4);
x_85 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_85, 0, x_39);
lean_ctor_set(x_85, 1, x_40);
lean_ctor_set(x_85, 2, x_41);
lean_ctor_set(x_85, 3, x_42);
lean_ctor_set(x_85, 4, x_43);
lean_ctor_set(x_85, 5, x_44);
lean_ctor_set(x_85, 6, x_45);
lean_ctor_set(x_85, 7, x_2);
lean_ctor_set(x_85, 8, x_46);
lean_ctor_set(x_85, 9, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*10, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*10 + 1, x_48);
lean_ctor_set_uint8(x_85, sizeof(void*)*10 + 2, x_49);
x_86 = l_Lean_Elab_Term_ensureHasType(x_59, x_82, x_85, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_6);
lean_dec(x_5);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Elab_Term_assignExprMVar(x_3, x_87, x_51, x_88);
lean_dec(x_51);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
x_92 = 1;
x_93 = lean_box(x_92);
lean_ctor_set(x_89, 0, x_93);
return x_89;
}
else
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = 1;
x_96 = lean_box(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_51);
lean_dec(x_3);
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
x_8 = x_98;
x_9 = x_99;
goto block_38;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_59);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_ctor_get(x_81, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_81, 1);
lean_inc(x_101);
lean_dec(x_81);
x_8 = x_100;
x_9 = x_101;
goto block_38;
}
}
block_38:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_6);
if (x_1 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_9, 2);
x_14 = l_Std_PersistentArray_push___rarg(x_13, x_11);
lean_ctor_set(x_9, 2, x_14);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 2);
x_21 = lean_ctor_get(x_9, 3);
x_22 = lean_ctor_get(x_9, 4);
x_23 = lean_ctor_get(x_9, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_24 = l_Std_PersistentArray_push___rarg(x_20, x_11);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set(x_25, 5, x_23);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_9);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_32 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_33 = l_unreachable_x21___rarg(x_32);
x_34 = lean_apply_2(x_33, x_6, x_9);
return x_34;
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_6);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_MonadState___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_box(x_4);
lean_inc(x_2);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1___boxed), 7, 4);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_2);
x_9 = l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 9);
x_13 = l_Lean_Elab_replaceRef(x_2, x_12);
lean_dec(x_12);
lean_dec(x_2);
lean_ctor_set(x_5, 9, x_13);
x_14 = l_Lean_Elab_Term_withMVarContext___rarg(x_3, x_10, x_5, x_6);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
x_20 = lean_ctor_get(x_5, 5);
x_21 = lean_ctor_get(x_5, 6);
x_22 = lean_ctor_get(x_5, 7);
x_23 = lean_ctor_get(x_5, 8);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_27 = lean_ctor_get(x_5, 9);
lean_inc(x_27);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_28 = l_Lean_Elab_replaceRef(x_2, x_27);
lean_dec(x_27);
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 5, x_20);
lean_ctor_set(x_29, 6, x_21);
lean_ctor_set(x_29, 7, x_22);
lean_ctor_set(x_29, 8, x_23);
lean_ctor_set(x_29, 9, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*10, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*10 + 1, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*10 + 2, x_26);
x_30 = l_Lean_Elab_Term_withMVarContext___rarg(x_3, x_10, x_29, x_6);
lean_dec(x_3);
return x_30;
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Elab_SyntheticMVars_2__resumePostponed(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_3__synthesizePendingInstMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 2);
x_13 = l_Std_PersistentArray_push___rarg(x_12, x_10);
lean_ctor_set(x_8, 2, x_13);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 2);
x_19 = lean_ctor_get(x_8, 3);
x_20 = lean_ctor_get(x_8, 4);
x_21 = lean_ctor_get(x_8, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_22 = l_Std_PersistentArray_push___rarg(x_18, x_10);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
x_35 = l_Std_PersistentArray_push___rarg(x_30, x_27);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 6, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_42 = l_unreachable_x21___rarg(x_41);
x_43 = lean_apply_2(x_42, x_2, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
lean_dec(x_4);
x_45 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_46 = l_unreachable_x21___rarg(x_45);
x_47 = lean_apply_2(x_46, x_2, x_44);
return x_47;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_3__synthesizePendingInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_3__synthesizePendingInstMVar___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Term_withMVarContext___rarg(x_1, x_4, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_4__synthesizePendingCoeInstMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_2, x_3, x_4, x_5, x_14, x_6, x_11);
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_18 = l_unreachable_x21___rarg(x_17);
x_19 = lean_apply_2(x_18, x_6, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_22 = l_unreachable_x21___rarg(x_21);
x_23 = lean_apply_2(x_22, x_6, x_20);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_4__synthesizePendingCoeInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_4__synthesizePendingCoeInstMVar___lambda__1), 7, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_5);
x_9 = l_Lean_Elab_Term_withMVarContext___rarg(x_1, x_8, x_6, x_7);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_5__checkWithDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_mkMVar(x_1);
x_5 = l_Lean_Elab_Term_instantiateMVars(x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Expr_getAppFn___main(x_7);
lean_dec(x_7);
x_9 = l_Lean_Expr_isMVar(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = l_Lean_Expr_getAppFn___main(x_14);
lean_dec(x_14);
x_17 = l_Lean_Expr_isMVar(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_6__synthesizeSyntheticMVar(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 9);
x_10 = l_Lean_Elab_replaceRef(x_6, x_9);
lean_dec(x_9);
lean_ctor_set(x_4, 9, x_10);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Elab_SyntheticMVars_3__synthesizePendingInstMVar(x_11, x_4, x_5);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 3);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Elab_SyntheticMVars_4__synthesizePendingCoeInstMVar(x_17, x_13, x_14, x_15, x_16, x_4, x_5);
return x_18;
}
case 2:
{
lean_dec(x_6);
if (x_3 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_1);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_Elab_Term_runTactic(x_23, x_22, x_4, x_5);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = 1;
x_28 = lean_box(x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
case 3:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
lean_dec(x_7);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l___private_Lean_Elab_SyntheticMVars_2__resumePostponed(x_37, x_6, x_38, x_2, x_4, x_5);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l___private_Lean_Elab_SyntheticMVars_5__checkWithDefault(x_40, x_4, x_5);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
x_44 = lean_ctor_get(x_4, 2);
x_45 = lean_ctor_get(x_4, 3);
x_46 = lean_ctor_get(x_4, 4);
x_47 = lean_ctor_get(x_4, 5);
x_48 = lean_ctor_get(x_4, 6);
x_49 = lean_ctor_get(x_4, 7);
x_50 = lean_ctor_get(x_4, 8);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_52 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_53 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_54 = lean_ctor_get(x_4, 9);
lean_inc(x_54);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_55 = l_Lean_Elab_replaceRef(x_6, x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_44);
lean_ctor_set(x_56, 3, x_45);
lean_ctor_set(x_56, 4, x_46);
lean_ctor_set(x_56, 5, x_47);
lean_ctor_set(x_56, 6, x_48);
lean_ctor_set(x_56, 7, x_49);
lean_ctor_set(x_56, 8, x_50);
lean_ctor_set(x_56, 9, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*10, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 1, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 2, x_53);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_6);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = l___private_Lean_Elab_SyntheticMVars_3__synthesizePendingInstMVar(x_57, x_56, x_5);
return x_58;
}
case 1:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_6);
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_7, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_7, 3);
lean_inc(x_62);
lean_dec(x_7);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = l___private_Lean_Elab_SyntheticMVars_4__synthesizePendingCoeInstMVar(x_63, x_59, x_60, x_61, x_62, x_56, x_5);
return x_64;
}
case 2:
{
lean_dec(x_6);
if (x_3 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_1);
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_7, 0);
lean_inc(x_68);
lean_dec(x_7);
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
lean_dec(x_1);
x_70 = l_Lean_Elab_Term_runTactic(x_69, x_68, x_56, x_5);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = 1;
x_74 = lean_box(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
case 3:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_7, 0);
lean_inc(x_80);
lean_dec(x_7);
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec(x_1);
x_82 = l___private_Lean_Elab_SyntheticMVars_2__resumePostponed(x_80, x_6, x_81, x_2, x_56, x_5);
return x_82;
}
default: 
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_7);
lean_dec(x_6);
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
lean_dec(x_1);
x_84 = l___private_Lean_Elab_SyntheticMVars_5__checkWithDefault(x_83, x_56, x_5);
return x_84;
}
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_6__synthesizeSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Elab_SyntheticMVars_6__synthesizeSyntheticMVar(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not ready yet");
return x_1;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succeeded");
return x_1;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming ?");
return x_1;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_11 = x_4;
} else {
 lean_dec_ref(x_4);
 x_11 = lean_box(0);
}
x_18 = l___private_Lean_Elab_Term_10__postponeElabTerm___closed__1;
lean_inc(x_3);
x_19 = lean_name_mk_string(x_3, x_18);
x_47 = l_Lean_Elab_Term_getOptions(x_6, x_7);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_19);
x_50 = l_Lean_checkTraceOption(x_48, x_19);
lean_dec(x_48);
if (x_50 == 0)
{
x_20 = x_49;
goto block_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__9;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
lean_inc(x_19);
x_55 = l_Lean_Elab_Term_logTrace(x_19, x_54, x_6, x_49);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_20 = x_56;
goto block_46;
}
block_17:
{
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_9);
x_4 = x_10;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
if (lean_is_scalar(x_11)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_11;
}
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_5);
x_4 = x_10;
x_5 = x_15;
x_7 = x_13;
goto _start;
}
}
block_46:
{
lean_object* x_21; 
lean_inc(x_6);
lean_inc(x_9);
x_21 = l___private_Lean_Elab_SyntheticMVars_6__synthesizeSyntheticMVar(x_9, x_1, x_2, x_6, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_getOptions(x_6, x_23);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_19);
x_28 = l_Lean_checkTraceOption(x_26, x_19);
lean_dec(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_19);
x_29 = 1;
x_12 = x_29;
x_13 = x_27;
goto block_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__3;
x_31 = l_Lean_Elab_Term_logTrace(x_19, x_30, x_6, x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = 1;
x_12 = x_33;
x_13 = x_32;
goto block_17;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
lean_inc(x_19);
x_36 = l_Lean_checkTraceOption(x_34, x_19);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_19);
x_37 = 0;
x_12 = x_37;
x_13 = x_35;
goto block_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__6;
x_39 = l_Lean_Elab_Term_logTrace(x_19, x_38, x_6, x_35);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = 0;
x_12 = x_41;
x_13 = x_40;
goto block_17;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__3(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Format_repr___main___closed__13;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Format_repr___main___closed__16;
return x_3;
}
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming synthetic metavariables, mayPostpone: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", postponeOnError: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_99 = lean_ctor_get(x_3, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_3, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_3, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_3, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_3, 5);
lean_inc(x_104);
x_105 = lean_ctor_get(x_3, 6);
lean_inc(x_105);
x_106 = lean_ctor_get(x_3, 7);
lean_inc(x_106);
x_107 = lean_ctor_get(x_3, 8);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_109 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_110 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_111 = lean_ctor_get(x_3, 9);
lean_inc(x_111);
x_112 = lean_box(0);
x_113 = l_Lean_Elab_replaceRef(x_112, x_111);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_114, 0, x_99);
lean_ctor_set(x_114, 1, x_100);
lean_ctor_set(x_114, 2, x_101);
lean_ctor_set(x_114, 3, x_102);
lean_ctor_set(x_114, 4, x_103);
lean_ctor_set(x_114, 5, x_104);
lean_ctor_set(x_114, 6, x_105);
lean_ctor_set(x_114, 7, x_106);
lean_ctor_set(x_114, 8, x_107);
lean_ctor_set(x_114, 9, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*10, x_108);
lean_ctor_set_uint8(x_114, sizeof(void*)*10 + 1, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*10 + 2, x_110);
x_115 = l_Lean_Elab_Term_getOptions(x_114, x_4);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__2;
x_119 = l_Lean_checkTraceOption(x_116, x_118);
lean_dec(x_116);
if (x_119 == 0)
{
lean_dec(x_114);
x_5 = x_117;
goto block_98;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__3(x_108);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__5;
x_123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__8;
x_125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
if (x_1 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9;
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Elab_Term_logTrace(x_118, x_127, x_114, x_117);
lean_dec(x_114);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_5 = x_129;
goto block_98;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10;
x_131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_Elab_Term_logTrace(x_118, x_131, x_114, x_117);
lean_dec(x_114);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_5 = x_133;
goto block_98;
}
}
block_98:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthAux___main___rarg(x_7, x_8);
x_10 = l_List_reverse___rarg(x_7);
x_11 = lean_box(0);
lean_ctor_set(x_5, 1, x_11);
x_12 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_13 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2(x_1, x_2, x_12, x_10, x_11, x_3, x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_List_lengthAux___main___rarg(x_15, x_8);
x_18 = lean_nat_dec_eq(x_9, x_17);
lean_dec(x_17);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = l_List_append___rarg(x_20, x_15);
lean_ctor_set(x_16, 1, x_21);
if (x_18 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
uint8_t x_24; lean_object* x_25; 
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set(x_13, 0, x_25);
return x_13;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
x_28 = lean_ctor_get(x_16, 2);
x_29 = lean_ctor_get(x_16, 3);
x_30 = lean_ctor_get(x_16, 4);
x_31 = lean_ctor_get(x_16, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_32 = l_List_append___rarg(x_27, x_15);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set(x_33, 5, x_31);
if (x_18 == 0)
{
uint8_t x_34; lean_object* x_35; 
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_13, 1, x_33);
lean_ctor_set(x_13, 0, x_35);
return x_13;
}
else
{
uint8_t x_36; lean_object* x_37; 
x_36 = 0;
x_37 = lean_box(x_36);
lean_ctor_set(x_13, 1, x_33);
lean_ctor_set(x_13, 0, x_37);
return x_13;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_40 = l_List_lengthAux___main___rarg(x_38, x_8);
x_41 = lean_nat_dec_eq(x_9, x_40);
lean_dec(x_40);
lean_dec(x_9);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_39, 5);
lean_inc(x_47);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
 x_48 = lean_box(0);
}
x_49 = l_List_append___rarg(x_43, x_38);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 6, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
if (x_41 == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_51 = 1;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
return x_13;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_13, 0);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_13);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_5, 0);
x_62 = lean_ctor_get(x_5, 1);
x_63 = lean_ctor_get(x_5, 2);
x_64 = lean_ctor_get(x_5, 3);
x_65 = lean_ctor_get(x_5, 4);
x_66 = lean_ctor_get(x_5, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_5);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_List_lengthAux___main___rarg(x_62, x_67);
x_69 = l_List_reverse___rarg(x_62);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_63);
lean_ctor_set(x_71, 3, x_64);
lean_ctor_set(x_71, 4, x_65);
lean_ctor_set(x_71, 5, x_66);
x_72 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_73 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2(x_1, x_2, x_72, x_69, x_70, x_3, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = l_List_lengthAux___main___rarg(x_74, x_67);
x_78 = lean_nat_dec_eq(x_68, x_77);
lean_dec(x_77);
lean_dec(x_68);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_75, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 5);
lean_inc(x_84);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_85 = x_75;
} else {
 lean_dec_ref(x_75);
 x_85 = lean_box(0);
}
x_86 = l_List_append___rarg(x_80, x_74);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 6, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_81);
lean_ctor_set(x_87, 3, x_82);
lean_ctor_set(x_87, 4, x_83);
lean_ctor_set(x_87, 5, x_84);
if (x_78 == 0)
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_88 = 1;
x_89 = lean_box(x_88);
if (lean_is_scalar(x_76)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_76;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_91 = 0;
x_92 = lean_box(x_91);
if (lean_is_scalar(x_76)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_76;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_87);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_68);
x_94 = lean_ctor_get(x_73, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_73, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_96 = x_73;
} else {
 lean_dec_ref(x_73);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__3(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to assign default value to metavariable");
return x_1;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_getAppFn___main(x_2);
x_6 = l_Lean_Expr_isMVar(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_isDefEq(x_2, x_1, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__3;
x_15 = l_Lean_Elab_Term_throwError___rarg(x_14, x_3, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 4)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 6);
x_20 = lean_ctor_get(x_3, 7);
x_21 = lean_ctor_get(x_3, 8);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_25 = lean_ctor_get(x_3, 9);
x_26 = l_Lean_Elab_replaceRef(x_12, x_25);
lean_dec(x_12);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_27 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_15);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_17);
lean_ctor_set(x_27, 5, x_18);
lean_ctor_set(x_27, 6, x_19);
lean_ctor_set(x_27, 7, x_20);
lean_ctor_set(x_27, 8, x_21);
lean_ctor_set(x_27, 9, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*10, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*10 + 1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*10 + 2, x_24);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_inc(x_28);
x_29 = l_Lean_mkMVar(x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instantiateMVars), 3, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1), 4, 1);
lean_closure_set(x_31, 0, x_11);
x_32 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Term_withMVarContext___rarg(x_28, x_32, x_27, x_4);
lean_dec(x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_free_object(x_1);
lean_dec(x_6);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_1 = x_9;
x_4 = x_36;
goto _start;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_3 = x_38;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
lean_dec(x_7);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
x_50 = lean_ctor_get(x_3, 3);
x_51 = lean_ctor_get(x_3, 4);
x_52 = lean_ctor_get(x_3, 5);
x_53 = lean_ctor_get(x_3, 6);
x_54 = lean_ctor_get(x_3, 7);
x_55 = lean_ctor_get(x_3, 8);
x_56 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_57 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_59 = lean_ctor_get(x_3, 9);
x_60 = l_Lean_Elab_replaceRef(x_46, x_59);
lean_dec(x_46);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_61 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_49);
lean_ctor_set(x_61, 3, x_50);
lean_ctor_set(x_61, 4, x_51);
lean_ctor_set(x_61, 5, x_52);
lean_ctor_set(x_61, 6, x_53);
lean_ctor_set(x_61, 7, x_54);
lean_ctor_set(x_61, 8, x_55);
lean_ctor_set(x_61, 9, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*10, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*10 + 1, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*10 + 2, x_58);
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
lean_inc(x_62);
x_63 = l_Lean_mkMVar(x_62);
x_64 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instantiateMVars), 3, 1);
lean_closure_set(x_64, 0, x_63);
x_65 = lean_alloc_closure((void*)(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1), 4, 1);
lean_closure_set(x_65, 0, x_45);
x_66 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_66, 0, x_64);
lean_closure_set(x_66, 1, x_65);
x_67 = l_Lean_Elab_Term_withMVarContext___rarg(x_62, x_66, x_61, x_4);
lean_dec(x_62);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_6);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_1 = x_44;
x_4 = x_70;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_2);
x_1 = x_44;
x_2 = x_73;
x_4 = x_72;
goto _start;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_2);
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_77 = x_67;
} else {
 lean_dec_ref(x_67);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_7);
x_79 = !lean_is_exclusive(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_1, 1);
x_81 = lean_ctor_get(x_1, 0);
lean_dec(x_81);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_80;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_dec(x_1);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_6);
lean_ctor_set(x_84, 1, x_2);
x_1 = x_83;
x_2 = x_84;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_lengthAux___main___rarg(x_3, x_4);
x_6 = lean_box(0);
x_7 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1(x_3, x_6, x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_List_reverse___rarg(x_9);
x_12 = l_List_lengthAux___main___rarg(x_11, x_4);
x_13 = lean_nat_dec_eq(x_12, x_5);
lean_dec(x_5);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_10, 1);
lean_dec(x_15);
lean_ctor_set(x_10, 1, x_11);
if (x_13 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 2);
x_22 = lean_ctor_get(x_10, 3);
x_23 = lean_ctor_get(x_10, 4);
x_24 = lean_ctor_get(x_10, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
if (x_13 == 0)
{
uint8_t x_26; lean_object* x_27; 
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
else
{
uint8_t x_28; lean_object* x_29; 
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = l_List_reverse___rarg(x_30);
x_33 = l_List_lengthAux___main___rarg(x_32, x_4);
x_34 = lean_nat_dec_eq(x_33, x_5);
lean_dec(x_5);
lean_dec(x_33);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 5);
lean_inc(x_39);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 lean_ctor_release(x_31, 4);
 lean_ctor_release(x_31, 5);
 x_40 = x_31;
} else {
 lean_dec_ref(x_31);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 6, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_39);
if (x_34 == 0)
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_42 = 1;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
return x_7;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to create type class instance for ");
return x_1;
}
}
lean_object* _init_l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_indentExpr(x_5);
x_7 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = 2;
x_10 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_9, x_8, x_2, x_3);
return x_10;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_indentExpr(x_9);
x_11 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_13, x_6, x_7);
lean_dec(x_13);
return x_14;
}
}
lean_object* _init_l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_22 = lean_ctor_get(x_2, 9);
x_23 = l_Lean_Elab_replaceRef(x_8, x_22);
lean_dec(x_8);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_15);
lean_ctor_set(x_24, 6, x_16);
lean_ctor_set(x_24, 7, x_17);
lean_ctor_set(x_24, 8, x_18);
lean_ctor_set(x_24, 9, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*10 + 2, x_21);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___closed__1;
x_28 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Term_withMVarContext___rarg(x_25, x_28, x_24, x_3);
lean_dec(x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_1 = x_7;
x_3 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_7);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 3);
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
lean_dec(x_6);
lean_inc(x_40);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__2___boxed), 7, 4);
lean_closure_set(x_42, 0, x_36);
lean_closure_set(x_42, 1, x_37);
lean_closure_set(x_42, 2, x_38);
lean_closure_set(x_42, 3, x_39);
x_43 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_43, 0, x_41);
lean_closure_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Term_withMVarContext___rarg(x_40, x_43, x_24, x_3);
lean_dec(x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_1 = x_7;
x_3 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_7);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_9);
lean_dec(x_6);
x_51 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_52 = l_unreachable_x21___rarg(x_51);
x_53 = lean_apply_2(x_52, x_24, x_3);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_1 = x_7;
x_3 = x_54;
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
lean_object* _init_l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___closed__1;
x_4 = l_List_find_x3f___main___rarg(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
x_5 = l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_22 = lean_ctor_get(x_3, 9);
x_23 = l_Lean_Elab_replaceRef(x_6, x_22);
lean_dec(x_22);
lean_dec(x_6);
lean_inc(x_23);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_ctor_set(x_3, 9, x_23);
x_24 = lean_ctor_get(x_10, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_10, 4);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_3);
x_27 = x_7;
goto block_185;
}
else
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_186 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_187 = l_Lean_Elab_Term_throwError___rarg(x_186, x_3, x_7);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
return x_187;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_187);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
block_185:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_101; uint8_t x_102; 
x_29 = lean_ctor_get(x_10, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_10, 3);
lean_dec(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_24, x_31);
lean_dec(x_24);
lean_ctor_set(x_10, 3, x_32);
lean_inc(x_23);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_33 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_11);
lean_ctor_set(x_33, 2, x_12);
lean_ctor_set(x_33, 3, x_13);
lean_ctor_set(x_33, 4, x_14);
lean_ctor_set(x_33, 5, x_15);
lean_ctor_set(x_33, 6, x_16);
lean_ctor_set(x_33, 7, x_17);
lean_ctor_set(x_33, 8, x_18);
lean_ctor_set(x_33, 9, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_33, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_33, sizeof(void*)*10 + 2, x_21);
x_101 = lean_ctor_get(x_27, 1);
lean_inc(x_101);
x_102 = l_List_isEmpty___rarg(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_dec(x_8);
if (x_1 == 0)
{
uint8_t x_103; 
x_103 = 0;
x_34 = x_103;
goto block_100;
}
else
{
uint8_t x_104; 
x_104 = 1;
x_34 = x_104;
goto block_100;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_105 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_8;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_27);
return x_106;
}
block_100:
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_33);
x_36 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_35, x_35, x_33, x_27);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
if (x_34 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_11);
lean_ctor_set(x_40, 2, x_12);
lean_ctor_set(x_40, 3, x_13);
lean_ctor_set(x_40, 4, x_14);
lean_ctor_set(x_40, 5, x_15);
lean_ctor_set(x_40, 6, x_16);
lean_ctor_set(x_40, 7, x_17);
lean_ctor_set(x_40, 8, x_18);
lean_ctor_set(x_40, 9, x_23);
lean_ctor_set_uint8(x_40, sizeof(void*)*10, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_40, sizeof(void*)*10 + 2, x_21);
x_41 = 1;
lean_inc(x_40);
x_42 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_41, x_35, x_40, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault(x_33, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_35, x_35, x_40, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_33);
x_54 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_35, x_41, x_33, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars(x_33, x_57);
lean_dec(x_33);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_box(0);
x_2 = x_60;
x_3 = x_33;
x_4 = x_59;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_33);
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_dec(x_50);
x_67 = lean_box(0);
x_2 = x_67;
x_3 = x_33;
x_4 = x_66;
goto _start;
}
}
else
{
uint8_t x_69; 
lean_dec(x_33);
x_69 = !lean_is_exclusive(x_50);
if (x_69 == 0)
{
return x_50;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_50, 0);
x_71 = lean_ctor_get(x_50, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_50);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_40);
x_73 = lean_ctor_get(x_46, 1);
lean_inc(x_73);
lean_dec(x_46);
x_74 = lean_box(0);
x_2 = x_74;
x_3 = x_33;
x_4 = x_73;
goto _start;
}
}
else
{
uint8_t x_76; 
lean_dec(x_40);
lean_dec(x_33);
x_76 = !lean_is_exclusive(x_46);
if (x_76 == 0)
{
return x_46;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_46, 0);
x_78 = lean_ctor_get(x_46, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_40);
x_80 = lean_ctor_get(x_42, 1);
lean_inc(x_80);
lean_dec(x_42);
x_81 = lean_box(0);
x_2 = x_81;
x_3 = x_33;
x_4 = x_80;
goto _start;
}
}
else
{
uint8_t x_83; 
lean_dec(x_40);
lean_dec(x_33);
x_83 = !lean_is_exclusive(x_42);
if (x_83 == 0)
{
return x_42;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_42, 0);
x_85 = lean_ctor_get(x_42, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_42);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_87 = !lean_is_exclusive(x_36);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_36, 0);
lean_dec(x_88);
x_89 = lean_box(0);
lean_ctor_set(x_36, 0, x_89);
return x_36;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_36, 1);
lean_inc(x_90);
lean_dec(x_36);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_10);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_93 = lean_ctor_get(x_36, 1);
lean_inc(x_93);
lean_dec(x_36);
x_94 = lean_box(0);
x_2 = x_94;
x_3 = x_33;
x_4 = x_93;
goto _start;
}
}
else
{
uint8_t x_96; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_96 = !lean_is_exclusive(x_36);
if (x_96 == 0)
{
return x_36;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_36, 0);
x_98 = lean_ctor_get(x_36, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_36);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_179; uint8_t x_180; 
x_107 = lean_ctor_get(x_10, 0);
x_108 = lean_ctor_get(x_10, 1);
x_109 = lean_ctor_get(x_10, 2);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_10);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_24, x_110);
lean_dec(x_24);
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_111);
lean_ctor_set(x_112, 4, x_25);
lean_inc(x_23);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_112);
x_113 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_11);
lean_ctor_set(x_113, 2, x_12);
lean_ctor_set(x_113, 3, x_13);
lean_ctor_set(x_113, 4, x_14);
lean_ctor_set(x_113, 5, x_15);
lean_ctor_set(x_113, 6, x_16);
lean_ctor_set(x_113, 7, x_17);
lean_ctor_set(x_113, 8, x_18);
lean_ctor_set(x_113, 9, x_23);
lean_ctor_set_uint8(x_113, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_113, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_113, sizeof(void*)*10 + 2, x_21);
x_179 = lean_ctor_get(x_27, 1);
lean_inc(x_179);
x_180 = l_List_isEmpty___rarg(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_dec(x_8);
if (x_1 == 0)
{
uint8_t x_181; 
x_181 = 0;
x_114 = x_181;
goto block_178;
}
else
{
uint8_t x_182; 
x_182 = 1;
x_114 = x_182;
goto block_178;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_183 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_8;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_27);
return x_184;
}
block_178:
{
uint8_t x_115; lean_object* x_116; 
x_115 = 0;
lean_inc(x_113);
x_116 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_115, x_115, x_113, x_27);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
if (x_114 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_120, 0, x_112);
lean_ctor_set(x_120, 1, x_11);
lean_ctor_set(x_120, 2, x_12);
lean_ctor_set(x_120, 3, x_13);
lean_ctor_set(x_120, 4, x_14);
lean_ctor_set(x_120, 5, x_15);
lean_ctor_set(x_120, 6, x_16);
lean_ctor_set(x_120, 7, x_17);
lean_ctor_set(x_120, 8, x_18);
lean_ctor_set(x_120, 9, x_23);
lean_ctor_set_uint8(x_120, sizeof(void*)*10, x_115);
lean_ctor_set_uint8(x_120, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_120, sizeof(void*)*10 + 2, x_21);
x_121 = 1;
lean_inc(x_120);
x_122 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_121, x_115, x_120, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = l___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault(x_113, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_115, x_115, x_120, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
lean_inc(x_113);
x_134 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_115, x_121, x_113, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = l___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars(x_113, x_137);
lean_dec(x_113);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_dec(x_134);
x_140 = lean_box(0);
x_2 = x_140;
x_3 = x_113;
x_4 = x_139;
goto _start;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_113);
x_142 = lean_ctor_get(x_134, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_134, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_144 = x_134;
} else {
 lean_dec_ref(x_134);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_130, 1);
lean_inc(x_146);
lean_dec(x_130);
x_147 = lean_box(0);
x_2 = x_147;
x_3 = x_113;
x_4 = x_146;
goto _start;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_113);
x_149 = lean_ctor_get(x_130, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_130, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_151 = x_130;
} else {
 lean_dec_ref(x_130);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_120);
x_153 = lean_ctor_get(x_126, 1);
lean_inc(x_153);
lean_dec(x_126);
x_154 = lean_box(0);
x_2 = x_154;
x_3 = x_113;
x_4 = x_153;
goto _start;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_120);
lean_dec(x_113);
x_156 = lean_ctor_get(x_126, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_126, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_158 = x_126;
} else {
 lean_dec_ref(x_126);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_120);
x_160 = lean_ctor_get(x_122, 1);
lean_inc(x_160);
lean_dec(x_122);
x_161 = lean_box(0);
x_2 = x_161;
x_3 = x_113;
x_4 = x_160;
goto _start;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_120);
lean_dec(x_113);
x_163 = lean_ctor_get(x_122, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_122, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_165 = x_122;
} else {
 lean_dec_ref(x_122);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_167 = lean_ctor_get(x_116, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_168 = x_116;
} else {
 lean_dec_ref(x_116);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_112);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_171 = lean_ctor_get(x_116, 1);
lean_inc(x_171);
lean_dec(x_116);
x_172 = lean_box(0);
x_2 = x_172;
x_3 = x_113;
x_4 = x_171;
goto _start;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_174 = lean_ctor_get(x_116, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_116, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_176 = x_116;
} else {
 lean_dec_ref(x_116);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; 
x_192 = lean_ctor_get(x_3, 0);
x_193 = lean_ctor_get(x_3, 1);
x_194 = lean_ctor_get(x_3, 2);
x_195 = lean_ctor_get(x_3, 3);
x_196 = lean_ctor_get(x_3, 4);
x_197 = lean_ctor_get(x_3, 5);
x_198 = lean_ctor_get(x_3, 6);
x_199 = lean_ctor_get(x_3, 7);
x_200 = lean_ctor_get(x_3, 8);
x_201 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_202 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_203 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_204 = lean_ctor_get(x_3, 9);
lean_inc(x_204);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_3);
x_205 = l_Lean_Elab_replaceRef(x_6, x_204);
lean_dec(x_204);
lean_dec(x_6);
lean_inc(x_205);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
x_206 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_206, 0, x_192);
lean_ctor_set(x_206, 1, x_193);
lean_ctor_set(x_206, 2, x_194);
lean_ctor_set(x_206, 3, x_195);
lean_ctor_set(x_206, 4, x_196);
lean_ctor_set(x_206, 5, x_197);
lean_ctor_set(x_206, 6, x_198);
lean_ctor_set(x_206, 7, x_199);
lean_ctor_set(x_206, 8, x_200);
lean_ctor_set(x_206, 9, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*10, x_201);
lean_ctor_set_uint8(x_206, sizeof(void*)*10 + 1, x_202);
lean_ctor_set_uint8(x_206, sizeof(void*)*10 + 2, x_203);
x_207 = lean_ctor_get(x_192, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_192, 4);
lean_inc(x_208);
x_209 = lean_nat_dec_eq(x_207, x_208);
if (x_209 == 0)
{
lean_dec(x_206);
x_210 = x_7;
goto block_290;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_8);
x_291 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_292 = l_Lean_Elab_Term_throwError___rarg(x_291, x_206, x_7);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
block_290:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_284; uint8_t x_285; 
x_211 = lean_ctor_get(x_192, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_192, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_192, 2);
lean_inc(x_213);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 x_214 = x_192;
} else {
 lean_dec_ref(x_192);
 x_214 = lean_box(0);
}
x_215 = lean_unsigned_to_nat(1u);
x_216 = lean_nat_add(x_207, x_215);
lean_dec(x_207);
if (lean_is_scalar(x_214)) {
 x_217 = lean_alloc_ctor(0, 5, 0);
} else {
 x_217 = x_214;
}
lean_ctor_set(x_217, 0, x_211);
lean_ctor_set(x_217, 1, x_212);
lean_ctor_set(x_217, 2, x_213);
lean_ctor_set(x_217, 3, x_216);
lean_ctor_set(x_217, 4, x_208);
lean_inc(x_205);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_217);
x_218 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_193);
lean_ctor_set(x_218, 2, x_194);
lean_ctor_set(x_218, 3, x_195);
lean_ctor_set(x_218, 4, x_196);
lean_ctor_set(x_218, 5, x_197);
lean_ctor_set(x_218, 6, x_198);
lean_ctor_set(x_218, 7, x_199);
lean_ctor_set(x_218, 8, x_200);
lean_ctor_set(x_218, 9, x_205);
lean_ctor_set_uint8(x_218, sizeof(void*)*10, x_201);
lean_ctor_set_uint8(x_218, sizeof(void*)*10 + 1, x_202);
lean_ctor_set_uint8(x_218, sizeof(void*)*10 + 2, x_203);
x_284 = lean_ctor_get(x_210, 1);
lean_inc(x_284);
x_285 = l_List_isEmpty___rarg(x_284);
lean_dec(x_284);
if (x_285 == 0)
{
lean_dec(x_8);
if (x_1 == 0)
{
uint8_t x_286; 
x_286 = 0;
x_219 = x_286;
goto block_283;
}
else
{
uint8_t x_287; 
x_287 = 1;
x_219 = x_287;
goto block_283;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_205);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
x_288 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_8;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_210);
return x_289;
}
block_283:
{
uint8_t x_220; lean_object* x_221; 
x_220 = 0;
lean_inc(x_218);
x_221 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_220, x_220, x_218, x_210);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
if (x_219 == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_225, 0, x_217);
lean_ctor_set(x_225, 1, x_193);
lean_ctor_set(x_225, 2, x_194);
lean_ctor_set(x_225, 3, x_195);
lean_ctor_set(x_225, 4, x_196);
lean_ctor_set(x_225, 5, x_197);
lean_ctor_set(x_225, 6, x_198);
lean_ctor_set(x_225, 7, x_199);
lean_ctor_set(x_225, 8, x_200);
lean_ctor_set(x_225, 9, x_205);
lean_ctor_set_uint8(x_225, sizeof(void*)*10, x_220);
lean_ctor_set_uint8(x_225, sizeof(void*)*10 + 1, x_202);
lean_ctor_set_uint8(x_225, sizeof(void*)*10 + 2, x_203);
x_226 = 1;
lean_inc(x_225);
x_227 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_226, x_220, x_225, x_224);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_unbox(x_228);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = l___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault(x_218, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_unbox(x_232);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec(x_231);
x_235 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_220, x_220, x_225, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_unbox(x_236);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
lean_inc(x_218);
x_239 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep(x_220, x_226, x_218, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_unbox(x_240);
lean_dec(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
lean_dec(x_239);
x_243 = l___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars(x_218, x_242);
lean_dec(x_218);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_239, 1);
lean_inc(x_244);
lean_dec(x_239);
x_245 = lean_box(0);
x_2 = x_245;
x_3 = x_218;
x_4 = x_244;
goto _start;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_218);
x_247 = lean_ctor_get(x_239, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_239, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_249 = x_239;
} else {
 lean_dec_ref(x_239);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_235, 1);
lean_inc(x_251);
lean_dec(x_235);
x_252 = lean_box(0);
x_2 = x_252;
x_3 = x_218;
x_4 = x_251;
goto _start;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_218);
x_254 = lean_ctor_get(x_235, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_235, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_256 = x_235;
} else {
 lean_dec_ref(x_235);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_225);
x_258 = lean_ctor_get(x_231, 1);
lean_inc(x_258);
lean_dec(x_231);
x_259 = lean_box(0);
x_2 = x_259;
x_3 = x_218;
x_4 = x_258;
goto _start;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_225);
lean_dec(x_218);
x_261 = lean_ctor_get(x_231, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_231, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_263 = x_231;
} else {
 lean_dec_ref(x_231);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; 
lean_dec(x_225);
x_265 = lean_ctor_get(x_227, 1);
lean_inc(x_265);
lean_dec(x_227);
x_266 = lean_box(0);
x_2 = x_266;
x_3 = x_218;
x_4 = x_265;
goto _start;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_225);
lean_dec(x_218);
x_268 = lean_ctor_get(x_227, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_227, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_270 = x_227;
} else {
 lean_dec_ref(x_227);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_205);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
x_272 = lean_ctor_get(x_221, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_273 = x_221;
} else {
 lean_dec_ref(x_221);
 x_273 = lean_box(0);
}
x_274 = lean_box(0);
if (lean_is_scalar(x_273)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_273;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_272);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_217);
lean_dec(x_205);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
x_276 = lean_ctor_get(x_221, 1);
lean_inc(x_276);
lean_dec(x_221);
x_277 = lean_box(0);
x_2 = x_277;
x_3 = x_218;
x_4 = x_276;
goto _start;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_205);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
x_279 = lean_ctor_get(x_221, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_221, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_281 = x_221;
} else {
 lean_dec_ref(x_221);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_37; lean_object* x_38; 
x_5 = lean_ctor_get(x_3, 1);
x_37 = lean_box(0);
lean_ctor_set(x_3, 1, x_37);
lean_inc(x_2);
x_38 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 0;
x_42 = lean_box(0);
x_43 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_41, x_42, x_2, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_39);
x_6 = x_45;
x_7 = x_44;
goto block_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_6 = x_48;
x_7 = x_47;
goto block_36;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_6 = x_51;
x_7 = x_50;
goto block_36;
}
block_36:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_List_append___rarg(x_10, x_5);
lean_ctor_set(x_7, 1, x_11);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_ctor_get(x_7, 3);
x_17 = lean_ctor_get(x_7, 4);
x_18 = lean_ctor_get(x_7, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_19 = l_List_append___rarg(x_14, x_5);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 1);
x_25 = l_List_append___rarg(x_24, x_5);
lean_ctor_set(x_7, 1, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = lean_ctor_get(x_7, 4);
x_32 = lean_ctor_get(x_7, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_33 = l_List_append___rarg(x_28, x_5);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_ctor_get(x_3, 2);
x_55 = lean_ctor_get(x_3, 3);
x_56 = lean_ctor_get(x_3, 4);
x_57 = lean_ctor_get(x_3, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_3);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_52);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_54);
lean_ctor_set(x_84, 3, x_55);
lean_ctor_set(x_84, 4, x_56);
lean_ctor_set(x_84, 5, x_57);
lean_inc(x_2);
x_85 = lean_apply_2(x_1, x_2, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = 0;
x_89 = lean_box(0);
x_90 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_88, x_89, x_2, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_86);
x_58 = x_92;
x_59 = x_91;
goto block_82;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_86);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_93);
x_58 = x_95;
x_59 = x_94;
goto block_82;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_2);
x_96 = lean_ctor_get(x_85, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_85, 1);
lean_inc(x_97);
lean_dec(x_85);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_58 = x_98;
x_59 = x_97;
goto block_82;
}
block_82:
{
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 5);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
x_68 = l_List_append___rarg(x_62, x_53);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_63);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set(x_69, 4, x_65);
lean_ctor_set(x_69, 5, x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
lean_dec(x_58);
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_59, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_59, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_59, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_59, 5);
lean_inc(x_77);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_78 = x_59;
} else {
 lean_dec_ref(x_59);
 x_78 = lean_box(0);
}
x_79 = l_List_append___rarg(x_73, x_53);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 6, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_74);
lean_ctor_set(x_80, 3, x_75);
lean_ctor_set(x_80, 4, x_76);
lean_ctor_set(x_80, 5, x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_withSynthesize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = 1;
x_6 = lean_box(x_5);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 5, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 9);
x_10 = l_Lean_Elab_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_dec(x_1);
lean_ctor_set(x_3, 9, x_10);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_withSynthesize___rarg(x_7, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_instantiateMVars(x_12, x_3, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
x_23 = lean_ctor_get(x_3, 4);
x_24 = lean_ctor_get(x_3, 5);
x_25 = lean_ctor_get(x_3, 6);
x_26 = lean_ctor_get(x_3, 7);
x_27 = lean_ctor_get(x_3, 8);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_31 = lean_ctor_get(x_3, 9);
lean_inc(x_31);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_32 = l_Lean_Elab_replaceRef(x_1, x_31);
lean_dec(x_31);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set(x_33, 5, x_24);
lean_ctor_set(x_33, 6, x_25);
lean_ctor_set(x_33, 7, x_26);
lean_ctor_set(x_33, 8, x_27);
lean_ctor_set(x_33, 9, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*10, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*10 + 1, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*10 + 2, x_30);
lean_inc(x_33);
x_34 = l_Lean_Elab_Term_withSynthesize___rarg(x_7, x_33, x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_instantiateMVars(x_35, x_33, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_40 = x_34;
} else {
 lean_dec_ref(x_34);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1 = _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1);
l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2 = _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2);
l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3 = _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3);
l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___closed__1);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__1 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__1();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__1);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__2 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__2();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__2);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__3 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__3();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__3);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__4 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__4();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__4);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__5 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__5();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__5);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__6 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__6();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__6);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__7 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__7();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__7);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__8 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__8();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__8);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__9 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__9();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___spec__2___closed__9);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__1);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__2);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__3);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__4);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__5);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__6 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__6();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__6);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__7 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__7();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__7);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__8 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__8();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__8);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9);
l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10 = _init_l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__1 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__1);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__2 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__2);
l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__3 = _init_l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Lean_Elab_SyntheticMVars_8__synthesizeUsingDefault___spec__1___lambda__1___closed__3);
l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1 = _init_l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1);
l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2 = _init_l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2);
l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3 = _init_l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3);
l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___closed__1 = _init_l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___closed__1();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_SyntheticMVars_9__reportStuckSyntheticMVars___spec__1___closed__1);
l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_10__getSomeSynthethicMVarsRef___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
