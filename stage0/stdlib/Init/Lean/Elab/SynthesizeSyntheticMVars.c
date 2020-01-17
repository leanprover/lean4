// Lean compiler output
// Module: Init.Lean.Elab.SynthesizeSyntheticMVars
// Imports: Init.Lean.Elab.Term Init.Lean.Elab.Tactic
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
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__5;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_5__synthesizeSyntheticMVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__3;
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__3(uint8_t);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__1;
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__2;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_5__synthesizeSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__6;
lean_object* l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
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
lean_object* l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__1;
extern lean_object* l_Lean_Format_repr___main___closed__13;
extern lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__3;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__7;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_4__checkWithDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___closed__1;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault___spec__1___lambda__1___closed__2;
extern lean_object* l___private_Init_Lean_Elab_Term_8__postponeElabTerm___closed__1;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___boxed(lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__4;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__9;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__8;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___boxed(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__1;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__10;
lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__2;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___closed__1;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_3__synthesizePendingInstMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__6;
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__8;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__3___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__9;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__5;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__4;
lean_object* l_List_forM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__3;
extern lean_object* l_Lean_Format_repr___main___closed__16;
uint8_t l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg___lambda__1(lean_object*);
extern lean_object* l_EStateM_MonadState___closed__2;
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___spec__2___closed__7;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_4__checkWithDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_1__resumeElabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_6, x_3, x_1, x_4, x_5);
return x_7;
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
lean_object* l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1___rarg___boxed), 3, 0);
return x_2;
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
lean_object* x_8; lean_object* x_9; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
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
x_49 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_41);
lean_ctor_set(x_49, 3, x_42);
lean_ctor_set(x_49, 4, x_43);
lean_ctor_set(x_49, 5, x_44);
lean_ctor_set(x_49, 6, x_45);
lean_ctor_set(x_49, 7, x_46);
lean_ctor_set(x_49, 8, x_2);
lean_ctor_set(x_49, 9, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*10, x_48);
x_50 = l_Lean_Elab_Term_getMVarDecl(x_3, x_49, x_7);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 2);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_49);
x_54 = l_Lean_Elab_Term_instantiateMVars(x_4, x_53, x_49, x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
if (x_1 == 0)
{
uint8_t x_58; uint8_t x_59; lean_object* x_60; 
x_58 = 0;
x_59 = 1;
lean_inc(x_49);
x_60 = l_Lean_Elab_Term_elabTermAux___main(x_57, x_58, x_59, x_4, x_49, x_56);
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
x_63 = l_Lean_Elab_Term_assignExprMVar(x_3, x_61, x_49, x_62);
lean_dec(x_49);
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
lean_dec(x_49);
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
lean_inc(x_49);
x_73 = l_Lean_Elab_Term_elabTermAux___main(x_57, x_72, x_72, x_4, x_49, x_56);
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
x_76 = l_Lean_Elab_Term_assignExprMVar(x_3, x_74, x_49, x_75);
lean_dec(x_49);
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
lean_dec(x_49);
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
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1___rarg___boxed), 3, 1);
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
lean_object* l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_lift___at___private_Init_Lean_Elab_SynthesizeSyntheticMVars_2__resumePostponed___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
x_18 = l___private_Init_Lean_Elab_Term_8__postponeElabTerm___closed__1;
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
x_53 = lean_alloc_ctor(8, 2, 0);
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
x_111 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__8;
x_113 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
if (x_1 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep___closed__9;
x_115 = lean_alloc_ctor(8, 2, 0);
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
x_120 = lean_alloc_ctor(8, 2, 0);
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
x_10 = lean_alloc_ctor(8, 2, 0);
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_2);
x_5 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_9__getSomeSynthethicMVarsRef___rarg(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 9);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 2);
x_24 = lean_ctor_get(x_6, 3);
x_25 = lean_ctor_get(x_6, 4);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_107; uint8_t x_108; 
x_28 = lean_ctor_get(x_3, 9);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 8);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 7);
lean_dec(x_30);
x_31 = lean_ctor_get(x_3, 6);
lean_dec(x_31);
x_32 = lean_ctor_get(x_3, 5);
lean_dec(x_32);
x_33 = lean_ctor_get(x_3, 4);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 3);
lean_dec(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_3, 0);
lean_dec(x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_24, x_38);
lean_dec(x_24);
lean_ctor_set(x_6, 3, x_39);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_107 = lean_ctor_get(x_9, 1);
lean_inc(x_107);
x_108 = l_List_isEmpty___rarg(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_free_object(x_5);
if (x_1 == 0)
{
uint8_t x_109; 
x_109 = 0;
x_40 = x_109;
goto block_106;
}
else
{
uint8_t x_110; 
x_110 = 1;
x_40 = x_110;
goto block_106;
}
}
else
{
lean_object* x_111; 
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_111 = lean_box(0);
lean_ctor_set(x_5, 0, x_111);
return x_5;
}
block_106:
{
uint8_t x_41; lean_object* x_42; 
x_41 = 0;
lean_inc(x_3);
x_42 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_41, x_41, x_3, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
if (x_40 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(x_3, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_10);
lean_ctor_set(x_50, 2, x_11);
lean_ctor_set(x_50, 3, x_12);
lean_ctor_set(x_50, 4, x_13);
lean_ctor_set(x_50, 5, x_14);
lean_ctor_set(x_50, 6, x_15);
lean_ctor_set(x_50, 7, x_16);
lean_ctor_set(x_50, 8, x_17);
lean_ctor_set(x_50, 9, x_18);
lean_ctor_set_uint8(x_50, sizeof(void*)*10, x_41);
x_51 = 1;
lean_inc(x_50);
x_52 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_51, x_41, x_50, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_41, x_41, x_50, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
lean_inc(x_3);
x_60 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_41, x_51, x_3, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(x_3, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_box(0);
x_2 = x_66;
x_4 = x_65;
goto _start;
}
}
else
{
uint8_t x_68; 
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_60, 0);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_60);
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
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
lean_dec(x_56);
x_73 = lean_box(0);
x_2 = x_73;
x_4 = x_72;
goto _start;
}
}
else
{
uint8_t x_75; 
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_56);
if (x_75 == 0)
{
return x_56;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_56, 0);
x_77 = lean_ctor_get(x_56, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_56);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_50);
x_79 = lean_ctor_get(x_52, 1);
lean_inc(x_79);
lean_dec(x_52);
x_80 = lean_box(0);
x_2 = x_80;
x_4 = x_79;
goto _start;
}
}
else
{
uint8_t x_82; 
lean_dec(x_50);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_52);
if (x_82 == 0)
{
return x_52;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_52, 0);
x_84 = lean_ctor_get(x_52, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_52);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_86 = lean_ctor_get(x_46, 1);
lean_inc(x_86);
lean_dec(x_46);
x_87 = lean_box(0);
x_2 = x_87;
x_4 = x_86;
goto _start;
}
}
else
{
uint8_t x_89; 
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_89 = !lean_is_exclusive(x_46);
if (x_89 == 0)
{
return x_46;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_46, 0);
x_91 = lean_ctor_get(x_46, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_46);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_93 = !lean_is_exclusive(x_42);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_42, 0);
lean_dec(x_94);
x_95 = lean_box(0);
lean_ctor_set(x_42, 0, x_95);
return x_42;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_42, 1);
lean_inc(x_96);
lean_dec(x_42);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_99 = lean_ctor_get(x_42, 1);
lean_inc(x_99);
lean_dec(x_42);
x_100 = lean_box(0);
x_2 = x_100;
x_4 = x_99;
goto _start;
}
}
else
{
uint8_t x_102; 
lean_dec(x_3);
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_102 = !lean_is_exclusive(x_42);
if (x_102 == 0)
{
return x_42;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_42, 0);
x_104 = lean_ctor_get(x_42, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_42);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_180; uint8_t x_181; 
lean_dec(x_3);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_24, x_112);
lean_dec(x_24);
lean_ctor_set(x_6, 3, x_113);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_114 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_114, 0, x_6);
lean_ctor_set(x_114, 1, x_10);
lean_ctor_set(x_114, 2, x_11);
lean_ctor_set(x_114, 3, x_12);
lean_ctor_set(x_114, 4, x_13);
lean_ctor_set(x_114, 5, x_14);
lean_ctor_set(x_114, 6, x_15);
lean_ctor_set(x_114, 7, x_16);
lean_ctor_set(x_114, 8, x_17);
lean_ctor_set(x_114, 9, x_18);
lean_ctor_set_uint8(x_114, sizeof(void*)*10, x_20);
x_180 = lean_ctor_get(x_9, 1);
lean_inc(x_180);
x_181 = l_List_isEmpty___rarg(x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_free_object(x_5);
if (x_1 == 0)
{
uint8_t x_182; 
x_182 = 0;
x_115 = x_182;
goto block_179;
}
else
{
uint8_t x_183; 
x_183 = 1;
x_115 = x_183;
goto block_179;
}
}
else
{
lean_object* x_184; 
lean_dec(x_114);
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_184 = lean_box(0);
lean_ctor_set(x_5, 0, x_184);
return x_5;
}
block_179:
{
uint8_t x_116; lean_object* x_117; 
x_116 = 0;
lean_inc(x_114);
x_117 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_116, x_116, x_114, x_9);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
if (x_115 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
lean_inc(x_114);
x_121 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(x_114, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_125, 0, x_6);
lean_ctor_set(x_125, 1, x_10);
lean_ctor_set(x_125, 2, x_11);
lean_ctor_set(x_125, 3, x_12);
lean_ctor_set(x_125, 4, x_13);
lean_ctor_set(x_125, 5, x_14);
lean_ctor_set(x_125, 6, x_15);
lean_ctor_set(x_125, 7, x_16);
lean_ctor_set(x_125, 8, x_17);
lean_ctor_set(x_125, 9, x_18);
lean_ctor_set_uint8(x_125, sizeof(void*)*10, x_116);
x_126 = 1;
lean_inc(x_125);
x_127 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_126, x_116, x_125, x_124);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_116, x_116, x_125, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
lean_inc(x_114);
x_135 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_116, x_126, x_114, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(x_114, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
lean_dec(x_135);
x_141 = lean_box(0);
x_2 = x_141;
x_3 = x_114;
x_4 = x_140;
goto _start;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_114);
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_145 = x_135;
} else {
 lean_dec_ref(x_135);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_131, 1);
lean_inc(x_147);
lean_dec(x_131);
x_148 = lean_box(0);
x_2 = x_148;
x_3 = x_114;
x_4 = x_147;
goto _start;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_114);
x_150 = lean_ctor_get(x_131, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_131, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_152 = x_131;
} else {
 lean_dec_ref(x_131);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_125);
x_154 = lean_ctor_get(x_127, 1);
lean_inc(x_154);
lean_dec(x_127);
x_155 = lean_box(0);
x_2 = x_155;
x_3 = x_114;
x_4 = x_154;
goto _start;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_125);
lean_dec(x_114);
x_157 = lean_ctor_get(x_127, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_127, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_159 = x_127;
} else {
 lean_dec_ref(x_127);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_161 = lean_ctor_get(x_121, 1);
lean_inc(x_161);
lean_dec(x_121);
x_162 = lean_box(0);
x_2 = x_162;
x_3 = x_114;
x_4 = x_161;
goto _start;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_114);
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_164 = lean_ctor_get(x_121, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_121, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_166 = x_121;
} else {
 lean_dec_ref(x_121);
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
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_114);
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_168 = lean_ctor_get(x_117, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_169 = x_117;
} else {
 lean_dec_ref(x_117);
 x_169 = lean_box(0);
}
x_170 = lean_box(0);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_168);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_172 = lean_ctor_get(x_117, 1);
lean_inc(x_172);
lean_dec(x_117);
x_173 = lean_box(0);
x_2 = x_173;
x_3 = x_114;
x_4 = x_172;
goto _start;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_114);
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_175 = lean_ctor_get(x_117, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_117, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_177 = x_117;
} else {
 lean_dec_ref(x_117);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_free_object(x_6);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_185 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_186 = l_Lean_Elab_Term_throwError___rarg(x_8, x_185, x_3, x_9);
lean_dec(x_8);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
return x_186;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_186);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_191 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_192 = lean_ctor_get(x_6, 0);
x_193 = lean_ctor_get(x_6, 1);
x_194 = lean_ctor_get(x_6, 2);
x_195 = lean_ctor_get(x_6, 3);
x_196 = lean_ctor_get(x_6, 4);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_6);
x_197 = lean_nat_dec_eq(x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_268; uint8_t x_269; 
lean_dec(x_8);
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
 x_198 = x_3;
} else {
 lean_dec_ref(x_3);
 x_198 = lean_box(0);
}
x_199 = lean_unsigned_to_nat(1u);
x_200 = lean_nat_add(x_195, x_199);
lean_dec(x_195);
x_201 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_201, 0, x_192);
lean_ctor_set(x_201, 1, x_193);
lean_ctor_set(x_201, 2, x_194);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_196);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_201);
if (lean_is_scalar(x_198)) {
 x_202 = lean_alloc_ctor(0, 10, 1);
} else {
 x_202 = x_198;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_10);
lean_ctor_set(x_202, 2, x_11);
lean_ctor_set(x_202, 3, x_12);
lean_ctor_set(x_202, 4, x_13);
lean_ctor_set(x_202, 5, x_14);
lean_ctor_set(x_202, 6, x_15);
lean_ctor_set(x_202, 7, x_16);
lean_ctor_set(x_202, 8, x_17);
lean_ctor_set(x_202, 9, x_18);
lean_ctor_set_uint8(x_202, sizeof(void*)*10, x_191);
x_268 = lean_ctor_get(x_9, 1);
lean_inc(x_268);
x_269 = l_List_isEmpty___rarg(x_268);
lean_dec(x_268);
if (x_269 == 0)
{
lean_free_object(x_5);
if (x_1 == 0)
{
uint8_t x_270; 
x_270 = 0;
x_203 = x_270;
goto block_267;
}
else
{
uint8_t x_271; 
x_271 = 1;
x_203 = x_271;
goto block_267;
}
}
else
{
lean_object* x_272; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_272 = lean_box(0);
lean_ctor_set(x_5, 0, x_272);
return x_5;
}
block_267:
{
uint8_t x_204; lean_object* x_205; 
x_204 = 0;
lean_inc(x_202);
x_205 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_204, x_204, x_202, x_9);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_unbox(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
if (x_203 == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
lean_inc(x_202);
x_209 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(x_202, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_unbox(x_210);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_213, 0, x_201);
lean_ctor_set(x_213, 1, x_10);
lean_ctor_set(x_213, 2, x_11);
lean_ctor_set(x_213, 3, x_12);
lean_ctor_set(x_213, 4, x_13);
lean_ctor_set(x_213, 5, x_14);
lean_ctor_set(x_213, 6, x_15);
lean_ctor_set(x_213, 7, x_16);
lean_ctor_set(x_213, 8, x_17);
lean_ctor_set(x_213, 9, x_18);
lean_ctor_set_uint8(x_213, sizeof(void*)*10, x_204);
x_214 = 1;
lean_inc(x_213);
x_215 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_214, x_204, x_213, x_212);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
x_219 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_204, x_204, x_213, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_unbox(x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
lean_inc(x_202);
x_223 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_204, x_214, x_202, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; uint8_t x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(x_202, x_226);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
lean_dec(x_223);
x_229 = lean_box(0);
x_2 = x_229;
x_3 = x_202;
x_4 = x_228;
goto _start;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_202);
x_231 = lean_ctor_get(x_223, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_223, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_233 = x_223;
} else {
 lean_dec_ref(x_223);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_219, 1);
lean_inc(x_235);
lean_dec(x_219);
x_236 = lean_box(0);
x_2 = x_236;
x_3 = x_202;
x_4 = x_235;
goto _start;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_202);
x_238 = lean_ctor_get(x_219, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_219, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_240 = x_219;
} else {
 lean_dec_ref(x_219);
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
lean_dec(x_213);
x_242 = lean_ctor_get(x_215, 1);
lean_inc(x_242);
lean_dec(x_215);
x_243 = lean_box(0);
x_2 = x_243;
x_3 = x_202;
x_4 = x_242;
goto _start;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_213);
lean_dec(x_202);
x_245 = lean_ctor_get(x_215, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_215, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_247 = x_215;
} else {
 lean_dec_ref(x_215);
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
lean_dec(x_201);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_249 = lean_ctor_get(x_209, 1);
lean_inc(x_249);
lean_dec(x_209);
x_250 = lean_box(0);
x_2 = x_250;
x_3 = x_202;
x_4 = x_249;
goto _start;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_252 = lean_ctor_get(x_209, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_209, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_254 = x_209;
} else {
 lean_dec_ref(x_209);
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
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_256 = lean_ctor_get(x_205, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_257 = x_205;
} else {
 lean_dec_ref(x_205);
 x_257 = lean_box(0);
}
x_258 = lean_box(0);
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_256);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_201);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_260 = lean_ctor_get(x_205, 1);
lean_inc(x_260);
lean_dec(x_205);
x_261 = lean_box(0);
x_2 = x_261;
x_3 = x_202;
x_4 = x_260;
goto _start;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_263 = lean_ctor_get(x_205, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_205, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_265 = x_205;
} else {
 lean_dec_ref(x_205);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_5);
x_273 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_274 = l_Lean_Elab_Term_throwError___rarg(x_8, x_273, x_3, x_9);
lean_dec(x_8);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_279 = lean_ctor_get(x_5, 0);
x_280 = lean_ctor_get(x_5, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_5);
x_281 = lean_ctor_get(x_3, 1);
lean_inc(x_281);
x_282 = lean_ctor_get(x_3, 2);
lean_inc(x_282);
x_283 = lean_ctor_get(x_3, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_3, 4);
lean_inc(x_284);
x_285 = lean_ctor_get(x_3, 5);
lean_inc(x_285);
x_286 = lean_ctor_get(x_3, 6);
lean_inc(x_286);
x_287 = lean_ctor_get(x_3, 7);
lean_inc(x_287);
x_288 = lean_ctor_get(x_3, 8);
lean_inc(x_288);
x_289 = lean_ctor_get(x_3, 9);
lean_inc(x_289);
x_290 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_291 = lean_ctor_get(x_6, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_6, 1);
lean_inc(x_292);
x_293 = lean_ctor_get(x_6, 2);
lean_inc(x_293);
x_294 = lean_ctor_get(x_6, 3);
lean_inc(x_294);
x_295 = lean_ctor_get(x_6, 4);
lean_inc(x_295);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_296 = x_6;
} else {
 lean_dec_ref(x_6);
 x_296 = lean_box(0);
}
x_297 = lean_nat_dec_eq(x_294, x_295);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_368; uint8_t x_369; 
lean_dec(x_279);
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
 x_298 = x_3;
} else {
 lean_dec_ref(x_3);
 x_298 = lean_box(0);
}
x_299 = lean_unsigned_to_nat(1u);
x_300 = lean_nat_add(x_294, x_299);
lean_dec(x_294);
if (lean_is_scalar(x_296)) {
 x_301 = lean_alloc_ctor(0, 5, 0);
} else {
 x_301 = x_296;
}
lean_ctor_set(x_301, 0, x_291);
lean_ctor_set(x_301, 1, x_292);
lean_ctor_set(x_301, 2, x_293);
lean_ctor_set(x_301, 3, x_300);
lean_ctor_set(x_301, 4, x_295);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_301);
if (lean_is_scalar(x_298)) {
 x_302 = lean_alloc_ctor(0, 10, 1);
} else {
 x_302 = x_298;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_281);
lean_ctor_set(x_302, 2, x_282);
lean_ctor_set(x_302, 3, x_283);
lean_ctor_set(x_302, 4, x_284);
lean_ctor_set(x_302, 5, x_285);
lean_ctor_set(x_302, 6, x_286);
lean_ctor_set(x_302, 7, x_287);
lean_ctor_set(x_302, 8, x_288);
lean_ctor_set(x_302, 9, x_289);
lean_ctor_set_uint8(x_302, sizeof(void*)*10, x_290);
x_368 = lean_ctor_get(x_280, 1);
lean_inc(x_368);
x_369 = l_List_isEmpty___rarg(x_368);
lean_dec(x_368);
if (x_369 == 0)
{
if (x_1 == 0)
{
uint8_t x_370; 
x_370 = 0;
x_303 = x_370;
goto block_367;
}
else
{
uint8_t x_371; 
x_371 = 1;
x_303 = x_371;
goto block_367;
}
}
else
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
x_372 = lean_box(0);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_280);
return x_373;
}
block_367:
{
uint8_t x_304; lean_object* x_305; 
x_304 = 0;
lean_inc(x_302);
x_305 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_304, x_304, x_302, x_280);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; uint8_t x_307; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_unbox(x_306);
lean_dec(x_306);
if (x_307 == 0)
{
if (x_303 == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_dec(x_305);
lean_inc(x_302);
x_309 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_7__synthesizeUsingDefault(x_302, x_308);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; uint8_t x_311; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_unbox(x_310);
lean_dec(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
lean_dec(x_309);
x_313 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_313, 0, x_301);
lean_ctor_set(x_313, 1, x_281);
lean_ctor_set(x_313, 2, x_282);
lean_ctor_set(x_313, 3, x_283);
lean_ctor_set(x_313, 4, x_284);
lean_ctor_set(x_313, 5, x_285);
lean_ctor_set(x_313, 6, x_286);
lean_ctor_set(x_313, 7, x_287);
lean_ctor_set(x_313, 8, x_288);
lean_ctor_set(x_313, 9, x_289);
lean_ctor_set_uint8(x_313, sizeof(void*)*10, x_304);
x_314 = 1;
lean_inc(x_313);
x_315 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_314, x_304, x_313, x_312);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_unbox(x_316);
lean_dec(x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_dec(x_315);
x_319 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_304, x_304, x_313, x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_unbox(x_320);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
lean_inc(x_302);
x_323 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_6__synthesizeSyntheticMVarsStep(x_304, x_314, x_302, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_unbox(x_324);
lean_dec(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_dec(x_323);
x_327 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_8__reportStuckSyntheticMVars(x_302, x_326);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_323, 1);
lean_inc(x_328);
lean_dec(x_323);
x_329 = lean_box(0);
x_2 = x_329;
x_3 = x_302;
x_4 = x_328;
goto _start;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_302);
x_331 = lean_ctor_get(x_323, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_323, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_333 = x_323;
} else {
 lean_dec_ref(x_323);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_319, 1);
lean_inc(x_335);
lean_dec(x_319);
x_336 = lean_box(0);
x_2 = x_336;
x_3 = x_302;
x_4 = x_335;
goto _start;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_302);
x_338 = lean_ctor_get(x_319, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_319, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_340 = x_319;
} else {
 lean_dec_ref(x_319);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_313);
x_342 = lean_ctor_get(x_315, 1);
lean_inc(x_342);
lean_dec(x_315);
x_343 = lean_box(0);
x_2 = x_343;
x_3 = x_302;
x_4 = x_342;
goto _start;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_313);
lean_dec(x_302);
x_345 = lean_ctor_get(x_315, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_315, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_347 = x_315;
} else {
 lean_dec_ref(x_315);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_301);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
x_349 = lean_ctor_get(x_309, 1);
lean_inc(x_349);
lean_dec(x_309);
x_350 = lean_box(0);
x_2 = x_350;
x_3 = x_302;
x_4 = x_349;
goto _start;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
x_352 = lean_ctor_get(x_309, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_309, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_354 = x_309;
} else {
 lean_dec_ref(x_309);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
x_356 = lean_ctor_get(x_305, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_357 = x_305;
} else {
 lean_dec_ref(x_305);
 x_357 = lean_box(0);
}
x_358 = lean_box(0);
if (lean_is_scalar(x_357)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_357;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_356);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_301);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
x_360 = lean_ctor_get(x_305, 1);
lean_inc(x_360);
lean_dec(x_305);
x_361 = lean_box(0);
x_2 = x_361;
x_3 = x_302;
x_4 = x_360;
goto _start;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
x_363 = lean_ctor_get(x_305, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_305, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_365 = x_305;
} else {
 lean_dec_ref(x_305);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
x_374 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_375 = l_Lean_Elab_Term_throwError___rarg(x_279, x_374, x_3, x_280);
lean_dec(x_279);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
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
lean_object* initialize_Init_Lean_Elab_Tactic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_SynthesizeSyntheticMVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Tactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
