// Lean compiler output
// Module: Init.Lean.Elab.SynthesizeSyntheticMVars
// Imports: Init.Lean.Elab.Term Init.Lean.Elab.Tactic.Basic
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__5;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_5__synthesizeSyntheticMVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__3;
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__3(uint8_t);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__1;
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__2;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_5__synthesizeSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__6;
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__1;
extern lean_object* l_Lean_Format_repr___main___closed__13;
lean_object* l_Lean_Syntax_getTailWithInfo___main(lean_object*);
extern lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__3;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__7;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_4__checkWithDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___boxed(lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__4;
extern lean_object* l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__1;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__9;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__8;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___boxed(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__1;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__10;
lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___closed__1;
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__2;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___closed__1;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__6;
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__8;
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVarDeclMVars(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__3___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__9;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__5;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__4;
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__3;
extern lean_object* l_Lean_Format_repr___main___closed__16;
uint8_t l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___lambda__1(lean_object*);
extern lean_object* l_EStateM_MonadState___closed__2;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__7;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_4__checkWithDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_2);
x_10 = lean_box(0);
lean_ctor_set(x_5, 1, x_10);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_apply_2(x_3, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_13, 1, x_15);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 2);
x_22 = lean_ctor_get(x_15, 3);
x_23 = lean_ctor_get(x_15, 4);
x_24 = lean_ctor_get(x_15, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set(x_13, 1, x_25);
return x_13;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_15, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_15, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 5);
lean_inc(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 6, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_8);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set(x_33, 5, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 1);
lean_dec(x_41);
lean_ctor_set(x_39, 1, x_8);
lean_ctor_set(x_13, 1, x_39);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 2);
x_44 = lean_ctor_get(x_39, 3);
x_45 = lean_ctor_get(x_39, 4);
x_46 = lean_ctor_get(x_39, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_8);
lean_ctor_set(x_47, 2, x_43);
lean_ctor_set(x_47, 3, x_44);
lean_ctor_set(x_47, 4, x_45);
lean_ctor_set(x_47, 5, x_46);
lean_ctor_set(x_13, 1, x_47);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_13, 0);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_13);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 5);
lean_inc(x_56);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 lean_ctor_release(x_51, 5);
 x_57 = x_51;
} else {
 lean_dec_ref(x_51);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_8);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_55);
lean_ctor_set(x_58, 5, x_56);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_60 = lean_ctor_get(x_5, 1);
x_61 = lean_ctor_get(x_4, 0);
x_62 = lean_ctor_get(x_4, 1);
x_63 = lean_ctor_get(x_4, 2);
x_64 = lean_ctor_get(x_4, 3);
x_65 = lean_ctor_get(x_4, 4);
x_66 = lean_ctor_get(x_4, 5);
x_67 = lean_ctor_get(x_4, 6);
x_68 = lean_ctor_get(x_4, 7);
x_69 = lean_ctor_get(x_4, 8);
x_70 = lean_ctor_get(x_4, 9);
x_71 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_72 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_63);
lean_ctor_set(x_73, 3, x_64);
lean_ctor_set(x_73, 4, x_65);
lean_ctor_set(x_73, 5, x_66);
lean_ctor_set(x_73, 6, x_67);
lean_ctor_set(x_73, 7, x_68);
lean_ctor_set(x_73, 8, x_69);
lean_ctor_set(x_73, 9, x_70);
lean_ctor_set_uint8(x_73, sizeof(void*)*10, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*10 + 1, x_72);
lean_inc(x_1);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_1);
lean_ctor_set(x_74, 2, x_2);
x_75 = lean_box(0);
lean_ctor_set(x_5, 1, x_75);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_apply_2(x_3, x_74, x_77);
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
lean_ctor_set(x_89, 1, x_60);
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
lean_ctor_set(x_102, 1, x_60);
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
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_104 = lean_ctor_get(x_5, 0);
x_105 = lean_ctor_get(x_5, 1);
x_106 = lean_ctor_get(x_5, 2);
x_107 = lean_ctor_get(x_5, 3);
x_108 = lean_ctor_get(x_5, 4);
x_109 = lean_ctor_get(x_5, 5);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_5);
x_110 = lean_ctor_get(x_4, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_4, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_4, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_4, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_4, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_4, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_4, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_4, 7);
lean_inc(x_117);
x_118 = lean_ctor_get(x_4, 8);
lean_inc(x_118);
x_119 = lean_ctor_get(x_4, 9);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_121 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 x_122 = x_4;
} else {
 lean_dec_ref(x_4);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 10, 2);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_110);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_123, 2, x_112);
lean_ctor_set(x_123, 3, x_113);
lean_ctor_set(x_123, 4, x_114);
lean_ctor_set(x_123, 5, x_115);
lean_ctor_set(x_123, 6, x_116);
lean_ctor_set(x_123, 7, x_117);
lean_ctor_set(x_123, 8, x_118);
lean_ctor_set(x_123, 9, x_119);
lean_ctor_set_uint8(x_123, sizeof(void*)*10, x_120);
lean_ctor_set_uint8(x_123, sizeof(void*)*10 + 1, x_121);
lean_inc(x_1);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_1);
lean_ctor_set(x_124, 2, x_2);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_126, 0, x_104);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_106);
lean_ctor_set(x_126, 3, x_107);
lean_ctor_set(x_126, 4, x_108);
lean_ctor_set(x_126, 5, x_109);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_apply_2(x_3, x_124, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_133 = x_129;
} else {
 lean_dec_ref(x_129);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 5);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 6, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_134);
lean_ctor_set(x_140, 1, x_105);
lean_ctor_set(x_140, 2, x_135);
lean_ctor_set(x_140, 3, x_136);
lean_ctor_set(x_140, 4, x_137);
lean_ctor_set(x_140, 5, x_138);
if (lean_is_scalar(x_133)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_133;
}
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_142 = lean_ctor_get(x_129, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_129, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_144 = x_129;
} else {
 lean_dec_ref(x_129);
 x_144 = lean_box(0);
}
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_142);
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 2);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 5);
lean_inc(x_151);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 lean_ctor_release(x_146, 5);
 x_152 = x_146;
} else {
 lean_dec_ref(x_146);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 6, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_147);
lean_ctor_set(x_153, 1, x_105);
lean_ctor_set(x_153, 2, x_148);
lean_ctor_set(x_153, 3, x_149);
lean_ctor_set(x_153, 4, x_150);
lean_ctor_set(x_153, 5, x_151);
if (lean_is_scalar(x_144)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_144;
}
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1), 5, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lean_Elab_Term_withMVarContext___rarg(x_2, x_6, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftTacticElabM___rarg), 5, 0);
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
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_mkMVar(x_2);
lean_inc(x_3);
x_6 = l_Lean_Elab_Term_instantiateMVars(x_1, x_5, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_3);
x_11 = lean_box(0);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_6);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_8);
x_13 = l_Lean_indentExpr(x_12);
x_14 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Term_throwError___rarg(x_1, x_15, x_3, x_9);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_23 = l_Lean_indentExpr(x_22);
x_24 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_Term_throwError___rarg(x_1, x_25, x_3, x_18);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureAssignmentHasNoMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_runTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_runTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_2);
x_10 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_9, x_2);
lean_ctor_set(x_7, 1, x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 3, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l_Lean_Elab_Term_runTactic___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Elab_Term_liftTacticElabM___rarg(x_1, x_2, x_13, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_Syntax_getTailWithInfo___main(x_1);
x_18 = l_List_isEmpty___rarg(x_15);
if (lean_obj_tag(x_17) == 0)
{
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_2);
x_19 = l_Lean_Elab_Term_reportUnsolvedGoals(x_1, x_15, x_4, x_16);
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
lean_dec(x_15);
x_24 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_2, x_4, x_16);
lean_dec(x_1);
return x_24;
}
}
else
{
lean_dec(x_1);
if (x_18 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = l_Lean_Elab_Term_reportUnsolvedGoals(x_25, x_15, x_4, x_16);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_15);
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
x_32 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_31, x_2, x_4, x_16);
lean_dec(x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
x_39 = lean_ctor_get(x_7, 2);
x_40 = lean_ctor_get(x_7, 3);
x_41 = lean_ctor_get(x_7, 4);
x_42 = lean_ctor_get(x_7, 5);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
lean_inc(x_2);
x_43 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_38, x_2);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set(x_44, 5, x_42);
lean_ctor_set(x_5, 0, x_44);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 3, 1);
lean_closure_set(x_45, 0, x_3);
x_46 = l_Lean_Elab_Term_runTactic___closed__1;
x_47 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_47, 0, x_45);
lean_closure_set(x_47, 1, x_46);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_Elab_Term_liftTacticElabM___rarg(x_1, x_2, x_47, x_4, x_5);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_1);
x_51 = l_Lean_Syntax_getTailWithInfo___main(x_1);
x_52 = l_List_isEmpty___rarg(x_49);
if (lean_obj_tag(x_51) == 0)
{
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
x_53 = l_Lean_Elab_Term_reportUnsolvedGoals(x_1, x_49, x_4, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec(x_49);
x_58 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_2, x_4, x_50);
lean_dec(x_1);
return x_58;
}
}
else
{
lean_dec(x_1);
if (x_52 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
lean_dec(x_51);
x_60 = l_Lean_Elab_Term_reportUnsolvedGoals(x_59, x_49, x_4, x_50);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_49);
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
lean_dec(x_51);
x_66 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_65, x_2, x_4, x_50);
lean_dec(x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_ctor_get(x_48, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_69 = x_48;
} else {
 lean_dec_ref(x_48);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_71 = lean_ctor_get(x_5, 0);
x_72 = lean_ctor_get(x_5, 1);
x_73 = lean_ctor_get(x_5, 2);
x_74 = lean_ctor_get(x_5, 3);
x_75 = lean_ctor_get(x_5, 4);
x_76 = lean_ctor_get(x_5, 5);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_5);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_71, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 5);
lean_inc(x_82);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 x_83 = x_71;
} else {
 lean_dec_ref(x_71);
 x_83 = lean_box(0);
}
lean_inc(x_2);
x_84 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_78, x_2);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 6, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_80);
lean_ctor_set(x_85, 4, x_81);
lean_ctor_set(x_85, 5, x_82);
x_86 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_72);
lean_ctor_set(x_86, 2, x_73);
lean_ctor_set(x_86, 3, x_74);
lean_ctor_set(x_86, 4, x_75);
lean_ctor_set(x_86, 5, x_76);
x_87 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 3, 1);
lean_closure_set(x_87, 0, x_3);
x_88 = l_Lean_Elab_Term_runTactic___closed__1;
x_89 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_89, 0, x_87);
lean_closure_set(x_89, 1, x_88);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Lean_Elab_Term_liftTacticElabM___rarg(x_1, x_2, x_89, x_4, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_1);
x_93 = l_Lean_Syntax_getTailWithInfo___main(x_1);
x_94 = l_List_isEmpty___rarg(x_91);
if (lean_obj_tag(x_93) == 0)
{
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_2);
x_95 = l_Lean_Elab_Term_reportUnsolvedGoals(x_1, x_91, x_4, x_92);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
else
{
lean_object* x_100; 
lean_dec(x_91);
x_100 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_1, x_2, x_4, x_92);
lean_dec(x_1);
return x_100;
}
}
else
{
lean_dec(x_1);
if (x_94 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_2);
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
lean_dec(x_93);
x_102 = l_Lean_Elab_Term_reportUnsolvedGoals(x_101, x_91, x_4, x_92);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_91);
x_107 = lean_ctor_get(x_93, 0);
lean_inc(x_107);
lean_dec(x_93);
x_108 = l_Lean_Elab_Term_ensureAssignmentHasNoMVars(x_107, x_2, x_4, x_92);
lean_dec(x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_ctor_get(x_90, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_90, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_111 = x_90;
} else {
 lean_dec_ref(x_90);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
lean_object* l_Lean_Elab_Term_runTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_runTactic___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_8, x_1, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 5);
x_16 = lean_ctor_get(x_4, 6);
x_17 = lean_ctor_get(x_4, 7);
x_18 = lean_ctor_get(x_4, 8);
x_19 = lean_ctor_get(x_4, 9);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
lean_inc(x_19);
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
x_21 = 0;
x_22 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_12);
lean_ctor_set(x_22, 3, x_13);
lean_ctor_set(x_22, 4, x_14);
lean_ctor_set(x_22, 5, x_15);
lean_ctor_set(x_22, 6, x_16);
lean_ctor_set(x_22, 7, x_17);
lean_ctor_set(x_22, 8, x_18);
lean_ctor_set(x_22, 9, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*10 + 1, x_21);
x_23 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_21, x_1, x_22, x_5);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; 
lean_ctor_set_uint8(x_4, sizeof(void*)*10 + 1, x_3);
x_25 = 0;
x_26 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_25, x_1, x_4, x_5);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
x_33 = lean_ctor_get(x_4, 6);
x_34 = lean_ctor_get(x_4, 7);
x_35 = lean_ctor_get(x_4, 8);
x_36 = lean_ctor_get(x_4, 9);
x_37 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_38 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set(x_38, 3, x_30);
lean_ctor_set(x_38, 4, x_31);
lean_ctor_set(x_38, 5, x_32);
lean_ctor_set(x_38, 6, x_33);
lean_ctor_set(x_38, 7, x_34);
lean_ctor_set(x_38, 8, x_35);
lean_ctor_set(x_38, 9, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*10, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*10 + 1, x_3);
x_39 = 0;
x_40 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_39, x_1, x_38, x_5);
return x_40;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_inhabited___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
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
x_46 = lean_ctor_get(x_6, 7);
lean_inc(x_46);
x_47 = lean_ctor_get(x_6, 9);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_50 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set(x_50, 3, x_42);
lean_ctor_set(x_50, 4, x_43);
lean_ctor_set(x_50, 5, x_44);
lean_ctor_set(x_50, 6, x_45);
lean_ctor_set(x_50, 7, x_46);
lean_ctor_set(x_50, 8, x_2);
lean_ctor_set(x_50, 9, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*10, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 1, x_49);
x_51 = l_Lean_Elab_Term_getMVarDecl(x_3, x_50, x_7);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = l_Lean_Elab_Term_instantiateMVars(x_4, x_54, x_50, x_53);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
if (x_1 == 0)
{
uint8_t x_59; lean_object* x_60; 
x_59 = 1;
lean_inc(x_50);
x_60 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm(x_4, x_58, x_59, x_50, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_6);
lean_dec(x_5);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Elab_Term_assignExprMVar(x_3, x_61, x_50, x_62);
lean_dec(x_50);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(x_59);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(x_59);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_50);
lean_dec(x_3);
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
lean_dec(x_60);
x_8 = x_70;
x_9 = x_71;
goto block_38;
}
}
else
{
uint8_t x_72; lean_object* x_73; 
x_72 = 0;
lean_inc(x_50);
x_73 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm(x_4, x_58, x_72, x_50, x_57);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_6);
lean_dec(x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_assignExprMVar(x_3, x_74, x_50, x_75);
lean_dec(x_50);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = 1;
x_80 = lean_box(x_79);
lean_ctor_set(x_76, 0, x_80);
return x_76;
}
else
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_dec(x_76);
x_82 = 1;
x_83 = lean_box(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_50);
lean_dec(x_3);
x_85 = lean_ctor_get(x_73, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
x_8 = x_85;
x_9 = x_86;
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
x_14 = l_PersistentArray_push___rarg(x_13, x_11);
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
x_24 = l_PersistentArray_push___rarg(x_20, x_11);
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
x_32 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1;
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
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_MonadState___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_box(x_4);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___boxed), 7, 4);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_2);
x_9 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_Term_withMVarContext___rarg(x_3, x_10, x_5, x_6);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 2);
x_14 = l_PersistentArray_push___rarg(x_13, x_11);
lean_ctor_set(x_9, 2, x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
x_19 = lean_ctor_get(x_9, 2);
x_20 = lean_ctor_get(x_9, 3);
x_21 = lean_ctor_get(x_9, 4);
x_22 = lean_ctor_get(x_9, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_23 = l_PersistentArray_push___rarg(x_19, x_11);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_22);
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 5);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
x_36 = l_PersistentArray_push___rarg(x_31, x_28);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 6, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_34);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
x_42 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1;
x_43 = l_unreachable_x21___rarg(x_42);
x_44 = lean_apply_2(x_43, x_3, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_5, 1);
lean_inc(x_45);
lean_dec(x_5);
x_46 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1;
x_47 = l_unreachable_x21___rarg(x_46);
x_48 = lean_apply_2(x_47, x_3, x_45);
return x_48;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Term_withMVarContext___rarg(x_2, x_5, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_4__checkWithDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_mkMVar(x_2);
x_6 = l_Lean_Elab_Term_instantiateMVars(x_1, x_5, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_Expr_getAppFn___main(x_8);
lean_dec(x_8);
x_10 = l_Lean_Expr_isMVar(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = l_Lean_Expr_getAppFn___main(x_15);
lean_dec(x_15);
x_18 = l_Lean_Expr_isMVar(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_4__checkWithDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_4__checkWithDefault(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_5__synthesizeSyntheticMVar(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar(x_7, x_8, x_4, x_5);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_runTactic(x_11, x_12, x_10, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed(x_26, x_27, x_28, x_2, x_4, x_5);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_4__checkWithDefault(x_30, x_31, x_4, x_5);
lean_dec(x_30);
return x_32;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_5__synthesizeSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_5__synthesizeSyntheticMVar(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not ready yet");
return x_1;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succeeded");
return x_1;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming ?");
return x_1;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
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
x_18 = l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__1;
lean_inc(x_3);
x_19 = lean_name_mk_string(x_3, x_18);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
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
lean_dec(x_20);
x_22 = x_49;
goto block_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_20);
x_52 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__9;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_inc(x_19);
x_54 = l_Lean_Elab_Term_logTrace(x_19, x_21, x_53, x_6, x_49);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_22 = x_55;
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
lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_9);
x_23 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_5__synthesizeSyntheticMVar(x_9, x_1, x_2, x_6, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_getOptions(x_6, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_19);
x_29 = l_Lean_checkTraceOption(x_27, x_19);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_19);
x_30 = lean_unbox(x_24);
lean_dec(x_24);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 1;
x_12 = x_31;
x_13 = x_28;
goto block_17;
}
else
{
uint8_t x_32; 
x_32 = 0;
x_12 = x_32;
x_13 = x_28;
goto block_17;
}
}
else
{
uint8_t x_33; 
x_33 = lean_unbox(x_24);
lean_dec(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__3;
x_35 = l_Lean_Elab_Term_logTrace(x_19, x_21, x_34, x_6, x_28);
lean_dec(x_21);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = 1;
x_12 = x_37;
x_13 = x_36;
goto block_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__6;
x_39 = l_Lean_Elab_Term_logTrace(x_19, x_21, x_38, x_6, x_28);
lean_dec(x_21);
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
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
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
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__3(uint8_t x_1) {
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
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
x_2 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming synthetic metavariables, mayPostpone: ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", postponeOnError: ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = l_Lean_Elab_Term_getOptions(x_3, x_4);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__2;
x_106 = l_Lean_checkTraceOption(x_103, x_105);
lean_dec(x_103);
if (x_106 == 0)
{
x_5 = x_104;
goto block_101;
}
else
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_108 = l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__3(x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__5;
x_111 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__8;
x_113 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
if (x_1 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__9;
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_box(0);
x_117 = l_Lean_Elab_Term_logTrace(x_105, x_116, x_115, x_3, x_104);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_5 = x_118;
goto block_101;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__10;
x_120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_box(0);
x_122 = l_Lean_Elab_Term_logTrace(x_105, x_121, x_120, x_3, x_104);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_5 = x_123;
goto block_101;
}
}
block_101:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthAux___main___rarg(x_7, x_8);
x_10 = lean_box(0);
lean_ctor_set(x_5, 1, x_10);
x_11 = l_List_reverse___rarg(x_7);
x_12 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
x_13 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2(x_1, x_2, x_12, x_11, x_10, x_3, x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_19 = l_List_append___rarg(x_18, x_17);
lean_ctor_set(x_15, 1, x_19);
x_20 = l_List_lengthAux___main___rarg(x_17, x_8);
lean_dec(x_17);
x_21 = lean_nat_dec_eq(x_9, x_20);
lean_dec(x_20);
lean_dec(x_9);
if (x_21 == 0)
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
x_29 = lean_ctor_get(x_15, 2);
x_30 = lean_ctor_get(x_15, 3);
x_31 = lean_ctor_get(x_15, 4);
x_32 = lean_ctor_get(x_15, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
lean_inc(x_26);
x_33 = l_List_append___rarg(x_28, x_26);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = l_List_lengthAux___main___rarg(x_26, x_8);
lean_dec(x_26);
x_36 = lean_nat_dec_eq(x_9, x_35);
lean_dec(x_35);
lean_dec(x_9);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; 
x_37 = 1;
x_38 = lean_box(x_37);
lean_ctor_set(x_13, 1, x_34);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
else
{
uint8_t x_39; lean_object* x_40; 
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_13, 1, x_34);
lean_ctor_set(x_13, 0, x_40);
return x_13;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_41 = lean_ctor_get(x_13, 1);
x_42 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
lean_inc(x_42);
x_50 = l_List_append___rarg(x_44, x_42);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 6, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_46);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
x_52 = l_List_lengthAux___main___rarg(x_42, x_8);
lean_dec(x_42);
x_53 = lean_nat_dec_eq(x_9, x_52);
lean_dec(x_52);
lean_dec(x_9);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_13);
if (x_60 == 0)
{
return x_13;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_13, 0);
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_13);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_64 = lean_ctor_get(x_5, 0);
x_65 = lean_ctor_get(x_5, 1);
x_66 = lean_ctor_get(x_5, 2);
x_67 = lean_ctor_get(x_5, 3);
x_68 = lean_ctor_get(x_5, 4);
x_69 = lean_ctor_get(x_5, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_5);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_List_lengthAux___main___rarg(x_65, x_70);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_66);
lean_ctor_set(x_73, 3, x_67);
lean_ctor_set(x_73, 4, x_68);
lean_ctor_set(x_73, 5, x_69);
x_74 = l_List_reverse___rarg(x_65);
x_75 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
x_76 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2(x_1, x_2, x_75, x_74, x_72, x_3, x_73);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 5);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
lean_inc(x_78);
x_87 = l_List_append___rarg(x_81, x_78);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 6, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_82);
lean_ctor_set(x_88, 3, x_83);
lean_ctor_set(x_88, 4, x_84);
lean_ctor_set(x_88, 5, x_85);
x_89 = l_List_lengthAux___main___rarg(x_78, x_70);
lean_dec(x_78);
x_90 = lean_nat_dec_eq(x_71, x_89);
lean_dec(x_89);
lean_dec(x_71);
if (x_90 == 0)
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_91 = 1;
x_92 = lean_box(x_91);
if (lean_is_scalar(x_79)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_79;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_88);
return x_93;
}
else
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_94 = 0;
x_95 = lean_box(x_94);
if (lean_is_scalar(x_79)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_79;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_88);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_71);
x_97 = lean_ctor_get(x_76, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_76, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_99 = x_76;
} else {
 lean_dec_ref(x_76);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
}
}
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__3(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to assign default value to metavariable");
return x_1;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_getAppFn___main(x_3);
x_7 = l_Lean_Expr_isMVar(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; 
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_isDefEq(x_1, x_3, x_2, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__3;
x_16 = l_Lean_Elab_Term_throwError___rarg(x_1, x_15, x_4, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
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
if (lean_obj_tag(x_7) == 3)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_mkMVar(x_12);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instantiateMVars___boxed), 4, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___boxed), 5, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_11);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_withMVarContext___rarg(x_12, x_17, x_3, x_4);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_1);
lean_dec(x_6);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_1 = x_9;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_3 = x_23;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
uint8_t x_25; 
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
x_33 = l_Lean_mkMVar(x_31);
lean_inc(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instantiateMVars___boxed), 4, 2);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___boxed), 5, 2);
lean_closure_set(x_35, 0, x_32);
lean_closure_set(x_35, 1, x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
lean_inc(x_3);
x_37 = l_Lean_Elab_Term_withMVarContext___rarg(x_31, x_36, x_3, x_4);
lean_dec(x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_6);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_1 = x_29;
x_4 = x_40;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_2);
x_1 = x_29;
x_2 = x_43;
x_4 = x_42;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_47 = x_37;
} else {
 lean_dec_ref(x_37);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_7);
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_50;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_2);
x_1 = x_53;
x_2 = x_54;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_lengthAux___main___rarg(x_3, x_4);
x_6 = lean_box(0);
x_7 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1(x_3, x_6, x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_List_reverse___rarg(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
lean_inc(x_11);
lean_ctor_set(x_10, 1, x_11);
x_14 = l_List_lengthAux___main___rarg(x_11, x_4);
lean_dec(x_11);
x_15 = lean_nat_dec_eq(x_14, x_5);
lean_dec(x_5);
lean_dec(x_14);
if (x_15 == 0)
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
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
lean_inc(x_11);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
x_26 = l_List_lengthAux___main___rarg(x_11, x_4);
lean_dec(x_11);
x_27 = lean_nat_dec_eq(x_26, x_5);
lean_dec(x_5);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
x_28 = 1;
x_29 = lean_box(x_28);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
else
{
uint8_t x_30; lean_object* x_31; 
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = l_List_reverse___rarg(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 5);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 lean_ctor_release(x_33, 4);
 lean_ctor_release(x_33, 5);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
lean_inc(x_34);
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 6, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_39);
x_42 = l_List_lengthAux___main___rarg(x_34, x_4);
lean_dec(x_34);
x_43 = lean_nat_dec_eq(x_42, x_5);
lean_dec(x_5);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_44 = 1;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
return x_7;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to create type class instance for ");
return x_1;
}
}
lean_object* _init_l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_indentExpr(x_7);
x_9 = l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 2;
x_12 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_5, x_11, x_10, x_3, x_4);
return x_12;
}
}
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_11, 0, x_6);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_inc(x_2);
x_13 = l_Lean_Elab_Term_withMVarContext___rarg(x_9, x_12, x_2, x_3);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_1 = x_8;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1;
x_22 = l_unreachable_x21___rarg(x_21);
lean_inc(x_2);
x_23 = lean_apply_2(x_22, x_2, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_1 = x_20;
x_3 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
uint8_t l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___lambda__1(lean_object* x_1) {
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
lean_object* _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___closed__1;
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
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_dec(x_2);
x_5 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg(x_4);
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
x_282 = lean_ctor_get(x_3, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_282, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 4);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_nat_dec_eq(x_283, x_284);
lean_dec(x_284);
lean_dec(x_283);
if (x_285 == 0)
{
lean_dec(x_6);
x_9 = x_7;
goto block_281;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_dec(x_8);
x_286 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_287 = l_Lean_Elab_Term_throwError___rarg(x_6, x_286, x_3, x_7);
lean_dec(x_6);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
return x_287;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_287, 0);
x_290 = lean_ctor_get(x_287, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_287);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
block_281:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_93; uint8_t x_94; 
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_3, 6);
x_19 = lean_ctor_get(x_3, 7);
x_20 = lean_ctor_get(x_3, 8);
x_21 = lean_ctor_get(x_3, 9);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_23 = lean_ctor_get(x_11, 3);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_23);
lean_ctor_set(x_11, 3, x_25);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
x_93 = lean_ctor_get(x_9, 1);
lean_inc(x_93);
x_94 = l_List_isEmpty___rarg(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_dec(x_8);
if (x_1 == 0)
{
uint8_t x_95; 
x_95 = 0;
x_26 = x_95;
goto block_92;
}
else
{
uint8_t x_96; 
x_96 = 1;
x_26 = x_96;
goto block_92;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_3);
lean_dec(x_11);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_97 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_8;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_9);
return x_98;
}
block_92:
{
uint8_t x_27; lean_object* x_28; 
x_27 = 0;
lean_inc(x_3);
x_28 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_27, x_27, x_3, x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
if (x_26 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set(x_32, 2, x_14);
lean_ctor_set(x_32, 3, x_15);
lean_ctor_set(x_32, 4, x_16);
lean_ctor_set(x_32, 5, x_17);
lean_ctor_set(x_32, 6, x_18);
lean_ctor_set(x_32, 7, x_19);
lean_ctor_set(x_32, 8, x_20);
lean_ctor_set(x_32, 9, x_21);
lean_ctor_set_uint8(x_32, sizeof(void*)*10, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*10 + 1, x_22);
x_33 = 1;
lean_inc(x_32);
x_34 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_33, x_27, x_32, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_3);
x_38 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(x_3, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_27, x_27, x_32, x_41);
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
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_27, x_33, x_3, x_45);
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
x_50 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(x_3, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_box(0);
x_2 = x_52;
x_4 = x_51;
goto _start;
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_dec(x_42);
x_59 = lean_box(0);
x_2 = x_59;
x_4 = x_58;
goto _start;
}
}
else
{
uint8_t x_61; 
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
return x_42;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_42);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_32);
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
lean_dec(x_38);
x_66 = lean_box(0);
x_2 = x_66;
x_4 = x_65;
goto _start;
}
}
else
{
uint8_t x_68; 
lean_dec(x_32);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_38);
if (x_68 == 0)
{
return x_38;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_38, 0);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_38);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_32);
x_72 = lean_ctor_get(x_34, 1);
lean_inc(x_72);
lean_dec(x_34);
x_73 = lean_box(0);
x_2 = x_73;
x_4 = x_72;
goto _start;
}
}
else
{
uint8_t x_75; 
lean_dec(x_32);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_34);
if (x_75 == 0)
{
return x_34;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_34, 0);
x_77 = lean_ctor_get(x_34, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_34);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_3);
lean_dec(x_11);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_79 = !lean_is_exclusive(x_28);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_28, 0);
lean_dec(x_80);
x_81 = lean_box(0);
lean_ctor_set(x_28, 0, x_81);
return x_28;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_28, 1);
lean_inc(x_82);
lean_dec(x_28);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_11);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_85 = lean_ctor_get(x_28, 1);
lean_inc(x_85);
lean_dec(x_28);
x_86 = lean_box(0);
x_2 = x_86;
x_4 = x_85;
goto _start;
}
}
else
{
uint8_t x_88; 
lean_dec(x_3);
lean_dec(x_11);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_88 = !lean_is_exclusive(x_28);
if (x_88 == 0)
{
return x_28;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_28, 0);
x_90 = lean_ctor_get(x_28, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_28);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_182; uint8_t x_183; 
x_99 = lean_ctor_get(x_3, 1);
x_100 = lean_ctor_get(x_3, 2);
x_101 = lean_ctor_get(x_3, 3);
x_102 = lean_ctor_get(x_3, 4);
x_103 = lean_ctor_get(x_3, 5);
x_104 = lean_ctor_get(x_3, 6);
x_105 = lean_ctor_get(x_3, 7);
x_106 = lean_ctor_get(x_3, 8);
x_107 = lean_ctor_get(x_3, 9);
x_108 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_109 = lean_ctor_get(x_11, 0);
x_110 = lean_ctor_get(x_11, 1);
x_111 = lean_ctor_get(x_11, 2);
x_112 = lean_ctor_get(x_11, 3);
x_113 = lean_ctor_get(x_11, 4);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_11);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_add(x_112, x_114);
lean_dec(x_112);
x_116 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_110);
lean_ctor_set(x_116, 2, x_111);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set(x_116, 4, x_113);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_116);
lean_ctor_set(x_3, 0, x_116);
x_182 = lean_ctor_get(x_9, 1);
lean_inc(x_182);
x_183 = l_List_isEmpty___rarg(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_dec(x_8);
if (x_1 == 0)
{
uint8_t x_184; 
x_184 = 0;
x_117 = x_184;
goto block_181;
}
else
{
uint8_t x_185; 
x_185 = 1;
x_117 = x_185;
goto block_181;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_3);
lean_dec(x_116);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
x_186 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_8;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_9);
return x_187;
}
block_181:
{
uint8_t x_118; lean_object* x_119; 
x_118 = 0;
lean_inc(x_3);
x_119 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_118, x_118, x_3, x_9);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
if (x_117 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_123, 0, x_116);
lean_ctor_set(x_123, 1, x_99);
lean_ctor_set(x_123, 2, x_100);
lean_ctor_set(x_123, 3, x_101);
lean_ctor_set(x_123, 4, x_102);
lean_ctor_set(x_123, 5, x_103);
lean_ctor_set(x_123, 6, x_104);
lean_ctor_set(x_123, 7, x_105);
lean_ctor_set(x_123, 8, x_106);
lean_ctor_set(x_123, 9, x_107);
lean_ctor_set_uint8(x_123, sizeof(void*)*10, x_118);
lean_ctor_set_uint8(x_123, sizeof(void*)*10 + 1, x_108);
x_124 = 1;
lean_inc(x_123);
x_125 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_124, x_118, x_123, x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
lean_inc(x_3);
x_129 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(x_3, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_118, x_118, x_123, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
lean_inc(x_3);
x_137 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_118, x_124, x_3, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(x_3, x_140);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_137, 1);
lean_inc(x_142);
lean_dec(x_137);
x_143 = lean_box(0);
x_2 = x_143;
x_4 = x_142;
goto _start;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_3);
x_145 = lean_ctor_get(x_137, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_137, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_147 = x_137;
} else {
 lean_dec_ref(x_137);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_133, 1);
lean_inc(x_149);
lean_dec(x_133);
x_150 = lean_box(0);
x_2 = x_150;
x_4 = x_149;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_3);
x_152 = lean_ctor_get(x_133, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_133, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_154 = x_133;
} else {
 lean_dec_ref(x_133);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_123);
x_156 = lean_ctor_get(x_129, 1);
lean_inc(x_156);
lean_dec(x_129);
x_157 = lean_box(0);
x_2 = x_157;
x_4 = x_156;
goto _start;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_123);
lean_dec(x_3);
x_159 = lean_ctor_get(x_129, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_129, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_161 = x_129;
} else {
 lean_dec_ref(x_129);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_123);
x_163 = lean_ctor_get(x_125, 1);
lean_inc(x_163);
lean_dec(x_125);
x_164 = lean_box(0);
x_2 = x_164;
x_4 = x_163;
goto _start;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_123);
lean_dec(x_3);
x_166 = lean_ctor_get(x_125, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_125, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_168 = x_125;
} else {
 lean_dec_ref(x_125);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_3);
lean_dec(x_116);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
x_170 = lean_ctor_get(x_119, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_171 = x_119;
} else {
 lean_dec_ref(x_119);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_116);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
x_174 = lean_ctor_get(x_119, 1);
lean_inc(x_174);
lean_dec(x_119);
x_175 = lean_box(0);
x_2 = x_175;
x_4 = x_174;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_3);
lean_dec(x_116);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
x_177 = lean_ctor_get(x_119, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_119, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_179 = x_119;
} else {
 lean_dec_ref(x_119);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_275; uint8_t x_276; 
x_188 = lean_ctor_get(x_3, 0);
x_189 = lean_ctor_get(x_3, 1);
x_190 = lean_ctor_get(x_3, 2);
x_191 = lean_ctor_get(x_3, 3);
x_192 = lean_ctor_get(x_3, 4);
x_193 = lean_ctor_get(x_3, 5);
x_194 = lean_ctor_get(x_3, 6);
x_195 = lean_ctor_get(x_3, 7);
x_196 = lean_ctor_get(x_3, 8);
x_197 = lean_ctor_get(x_3, 9);
x_198 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_199 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_3);
x_200 = lean_ctor_get(x_188, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_188, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_188, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_188, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_188, 4);
lean_inc(x_204);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 x_205 = x_188;
} else {
 lean_dec_ref(x_188);
 x_205 = lean_box(0);
}
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_add(x_203, x_206);
lean_dec(x_203);
if (lean_is_scalar(x_205)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_205;
}
lean_ctor_set(x_208, 0, x_200);
lean_ctor_set(x_208, 1, x_201);
lean_ctor_set(x_208, 2, x_202);
lean_ctor_set(x_208, 3, x_207);
lean_ctor_set(x_208, 4, x_204);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_208);
x_209 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_189);
lean_ctor_set(x_209, 2, x_190);
lean_ctor_set(x_209, 3, x_191);
lean_ctor_set(x_209, 4, x_192);
lean_ctor_set(x_209, 5, x_193);
lean_ctor_set(x_209, 6, x_194);
lean_ctor_set(x_209, 7, x_195);
lean_ctor_set(x_209, 8, x_196);
lean_ctor_set(x_209, 9, x_197);
lean_ctor_set_uint8(x_209, sizeof(void*)*10, x_198);
lean_ctor_set_uint8(x_209, sizeof(void*)*10 + 1, x_199);
x_275 = lean_ctor_get(x_9, 1);
lean_inc(x_275);
x_276 = l_List_isEmpty___rarg(x_275);
lean_dec(x_275);
if (x_276 == 0)
{
lean_dec(x_8);
if (x_1 == 0)
{
uint8_t x_277; 
x_277 = 0;
x_210 = x_277;
goto block_274;
}
else
{
uint8_t x_278; 
x_278 = 1;
x_210 = x_278;
goto block_274;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
x_279 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_8;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_9);
return x_280;
}
block_274:
{
uint8_t x_211; lean_object* x_212; 
x_211 = 0;
lean_inc(x_209);
x_212 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_211, x_211, x_209, x_9);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_unbox(x_213);
lean_dec(x_213);
if (x_214 == 0)
{
if (x_210 == 0)
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_dec(x_212);
x_216 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_216, 0, x_208);
lean_ctor_set(x_216, 1, x_189);
lean_ctor_set(x_216, 2, x_190);
lean_ctor_set(x_216, 3, x_191);
lean_ctor_set(x_216, 4, x_192);
lean_ctor_set(x_216, 5, x_193);
lean_ctor_set(x_216, 6, x_194);
lean_ctor_set(x_216, 7, x_195);
lean_ctor_set(x_216, 8, x_196);
lean_ctor_set(x_216, 9, x_197);
lean_ctor_set_uint8(x_216, sizeof(void*)*10, x_211);
lean_ctor_set_uint8(x_216, sizeof(void*)*10 + 1, x_199);
x_217 = 1;
lean_inc(x_216);
x_218 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_217, x_211, x_216, x_215);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_unbox(x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
lean_inc(x_209);
x_222 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(x_209, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_unbox(x_223);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_211, x_211, x_216, x_225);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_unbox(x_227);
lean_dec(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
lean_inc(x_209);
x_230 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_211, x_217, x_209, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(x_209, x_233);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_230, 1);
lean_inc(x_235);
lean_dec(x_230);
x_236 = lean_box(0);
x_2 = x_236;
x_3 = x_209;
x_4 = x_235;
goto _start;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_209);
x_238 = lean_ctor_get(x_230, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_230, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_240 = x_230;
} else {
 lean_dec_ref(x_230);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_226, 1);
lean_inc(x_242);
lean_dec(x_226);
x_243 = lean_box(0);
x_2 = x_243;
x_3 = x_209;
x_4 = x_242;
goto _start;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_209);
x_245 = lean_ctor_get(x_226, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_226, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_247 = x_226;
} else {
 lean_dec_ref(x_226);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_216);
x_249 = lean_ctor_get(x_222, 1);
lean_inc(x_249);
lean_dec(x_222);
x_250 = lean_box(0);
x_2 = x_250;
x_3 = x_209;
x_4 = x_249;
goto _start;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_216);
lean_dec(x_209);
x_252 = lean_ctor_get(x_222, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_222, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_254 = x_222;
} else {
 lean_dec_ref(x_222);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_216);
x_256 = lean_ctor_get(x_218, 1);
lean_inc(x_256);
lean_dec(x_218);
x_257 = lean_box(0);
x_2 = x_257;
x_3 = x_209;
x_4 = x_256;
goto _start;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_216);
lean_dec(x_209);
x_259 = lean_ctor_get(x_218, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_218, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_261 = x_218;
} else {
 lean_dec_ref(x_218);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
x_263 = lean_ctor_get(x_212, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_264 = x_212;
} else {
 lean_dec_ref(x_212);
 x_264 = lean_box(0);
}
x_265 = lean_box(0);
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_263);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_208);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
x_267 = lean_ctor_get(x_212, 1);
lean_inc(x_267);
lean_dec(x_212);
x_268 = lean_box(0);
x_2 = x_268;
x_3 = x_209;
x_4 = x_267;
goto _start;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
x_270 = lean_ctor_get(x_212, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_212, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_272 = x_212;
} else {
 lean_dec_ref(x_212);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(x_1, x_4, x_2, x_3);
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
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Elab_Tactic_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_SynthesizeSyntheticMVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1 = _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__1);
l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2 = _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__2);
l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3 = _init_l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_ensureAssignmentHasNoMVars___closed__3);
l_Lean_Elab_Term_runTactic___closed__1 = _init_l_Lean_Elab_Term_runTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_runTactic___closed__1);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___closed__1 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___closed__1);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__1 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__1();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__1);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__2 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__2();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__2);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__3 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__3();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__3);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__4 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__4();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__4);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__5 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__5();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__5);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__6 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__6();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__6);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__7 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__7();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__7);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__8 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__8();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__8);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__9 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__9();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__9);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__1 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__1);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__2 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__2);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__3 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__3);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__4 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__4);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__5 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__5);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__6 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__6);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__7 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__7);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__8 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__8);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__9 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__9);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__10 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__10);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__1 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__1);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__2 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__2);
l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__3 = _init_l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__3);
l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1 = _init_l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__1);
l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2 = _init_l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__2);
l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3 = _init_l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3);
l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___closed__1 = _init_l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
