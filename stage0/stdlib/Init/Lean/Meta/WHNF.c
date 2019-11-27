// Lean compiler output
// Module: Init.Lean.Meta.WHNF
// Imports: Init.Lean.AuxRecursor Init.Lean.WHNF Init.Lean.Meta.Basic Init.Lean.Meta.LevelDefEq
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
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isRecStuck___at_Lean_Meta_unfoldDefinition___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_Iterator_extract___closed__1;
extern lean_object* l_EIO_Monad___closed__1;
extern lean_object* l_Lean_noConfusionExt;
lean_object* l___private_Init_Lean_WHNF_4__getRecRuleFor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_WHNF_6__isIdRhsApp(lean_object*);
lean_object* l_Lean_WHNF_reduceRec___at_Lean_Meta_whnfCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef___closed__1;
lean_object* l_Lean_Meta_isAuxDef_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at_Lean_Meta_unfoldDefinition___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_8__deltaDefinition___at_Lean_Meta_unfoldDefinition___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setWHNFRef(lean_object*);
lean_object* l___private_Init_Lean_WHNF_3__toCtorIfLit(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_unfoldDefinition___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceRec___at_Lean_Meta_unfoldDefinition___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isQuotRecStuck___at_Lean_Meta_unfoldDefinition___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_1__getFirstCtor___at_Lean_Meta_unfoldDefinition___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_lparams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_WHNF_getStuckMVar___main___at_Lean_Meta_unfoldDefinition___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l___private_Init_Lean_WHNF_8__deltaDefinition___at_Lean_Meta_unfoldDefinition___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceRec___at_Lean_Meta_unfoldDefinition___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_whnfCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_WHNF_smartUnfoldingSuffix;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_7__extractIdRhs(lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isQuotRecStuck___at_Lean_Meta_unfoldDefinition___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_whnfCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_Meta_synthPending(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_whnfCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImpl___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9___closed__1;
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_unfoldDefinition___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_isRecStuck___at_Lean_Meta_unfoldDefinition___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at_Lean_Meta_unfoldDefinition___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at_Lean_Meta_unfoldDefinition___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfImpl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_reduceRec___at_Lean_Meta_whnfCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isAuxDef_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_auxRecExt;
x_6 = l_Lean_TagDeclarationExtension_isTagged(x_5, x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_noConfusionExt;
x_8 = l_Lean_TagDeclarationExtension_isTagged(x_7, x_4, x_1);
lean_dec(x_4);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
lean_object* l_Lean_Meta_isAuxDef_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isAuxDef_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_WHNF_8__deltaDefinition___at_Lean_Meta_unfoldDefinition___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_ConstantInfo_lparams(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_List_lengthAux___main___rarg(x_5, x_6);
lean_dec(x_5);
x_8 = l_List_lengthAux___main___rarg(x_2, x_6);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_String_Iterator_extract___closed__1;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_instantiate_value_lparams(x_1, x_2);
x_12 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_instantiate_value_lparams(x_1, x_2);
x_19 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_ConstantInfo_lparams(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_List_lengthAux___main___rarg(x_6, x_7);
lean_dec(x_6);
x_9 = l_List_lengthAux___main___rarg(x_2, x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_String_Iterator_extract___closed__1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_instantiate_value_lparams(x_1, x_2);
x_13 = l_Lean_Expr_betaRev(x_12, x_3);
lean_dec(x_12);
x_14 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_instantiate_value_lparams(x_1, x_2);
x_21 = l_Lean_Expr_betaRev(x_20, x_3);
lean_dec(x_20);
x_22 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_ConstantInfo_lparams(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___main___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthAux___main___rarg(x_5, x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_String_Iterator_extract___closed__1;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_15 = lean_instantiate_value_lparams(x_4, x_5);
x_16 = l_Lean_Expr_betaRev(x_15, x_6);
lean_dec(x_15);
x_17 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_16);
x_18 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_17, x_7, x_8);
return x_18;
}
else
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_expr_eqv(x_2, x_3);
x_20 = 1;
x_21 = l_Bool_DecidableEq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_26 = lean_instantiate_value_lparams(x_4, x_5);
x_27 = l_Lean_Expr_betaRev(x_26, x_6);
lean_dec(x_26);
x_28 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_27);
x_29 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_28, x_7, x_8);
return x_29;
}
else
{
uint8_t x_30; uint8_t x_31; uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_expr_eqv(x_2, x_3);
x_31 = 1;
x_32 = l_Bool_DecidableEq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
}
}
}
lean_object* l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_unfoldDefinition___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_143; lean_object* x_144; 
x_143 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_144 = lean_box(x_143);
switch (lean_obj_tag(x_144)) {
case 2:
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_unsigned_to_nat(5u);
x_146 = lean_unsigned_to_nat(3u);
x_9 = x_145;
x_10 = x_146;
goto block_142;
}
case 3:
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_unsigned_to_nat(4u);
x_148 = lean_unsigned_to_nat(3u);
x_9 = x_147;
x_10 = x_148;
goto block_142;
}
default: 
{
uint8_t x_149; uint8_t x_150; uint8_t x_151; 
lean_dec(x_144);
lean_dec(x_7);
x_149 = lean_expr_eqv(x_2, x_3);
x_150 = 1;
x_151 = l_Bool_DecidableEq(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_8);
return x_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_1);
lean_ctor_set(x_154, 1, x_8);
return x_154;
}
}
}
block_142:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_lt(x_9, x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_7);
x_13 = lean_expr_eqv(x_2, x_3);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_6, x_9);
lean_inc(x_7);
x_20 = l_Lean_Meta_whnf(x_19, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 5)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = 0;
x_29 = l_Lean_Meta_getConstAux(x_27, x_28, x_7, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_expr_eqv(x_2, x_3);
x_34 = 1;
x_35 = l_Bool_DecidableEq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_36);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_expr_eqv(x_2, x_3);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
lean_dec(x_30);
if (lean_obj_tag(x_44) == 4)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
x_47 = lean_box(x_46);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = l_Lean_Expr_Inhabited;
x_50 = lean_array_get(x_49, x_6, x_10);
x_51 = l_Lean_mkApp(x_50, x_26);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_9, x_52);
x_54 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_11, x_6, x_53, x_51);
lean_dec(x_11);
x_55 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_54, x_7, x_48);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_47);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_29);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_29, 0);
lean_dec(x_57);
x_58 = lean_expr_eqv(x_2, x_3);
x_59 = 1;
x_60 = l_Bool_DecidableEq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_61);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_dec(x_29);
x_63 = lean_expr_eqv(x_2, x_3);
x_64 = 1;
x_65 = l_Bool_DecidableEq(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_44);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
x_69 = !lean_is_exclusive(x_29);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_29, 0);
lean_dec(x_70);
x_71 = lean_expr_eqv(x_2, x_3);
x_72 = 1;
x_73 = l_Bool_DecidableEq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_74);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_29, 1);
lean_inc(x_75);
lean_dec(x_29);
x_76 = lean_expr_eqv(x_2, x_3);
x_77 = 1;
x_78 = l_Bool_DecidableEq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_29);
if (x_82 == 0)
{
return x_29;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_29, 0);
x_84 = lean_ctor_get(x_29, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_29);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_7);
x_86 = !lean_is_exclusive(x_20);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_20, 0);
lean_dec(x_87);
x_88 = lean_expr_eqv(x_2, x_3);
x_89 = 1;
x_90 = l_Bool_DecidableEq(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_20, 0, x_91);
return x_20;
}
else
{
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
}
else
{
lean_object* x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_20, 1);
lean_inc(x_92);
lean_dec(x_20);
x_93 = lean_expr_eqv(x_2, x_3);
x_94 = 1;
x_95 = l_Bool_DecidableEq(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
return x_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_92);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_7);
x_99 = !lean_is_exclusive(x_20);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_20, 0);
lean_dec(x_100);
x_101 = lean_expr_eqv(x_2, x_3);
x_102 = 1;
x_103 = l_Bool_DecidableEq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_20, 0, x_104);
return x_20;
}
else
{
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
}
else
{
lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_20, 1);
lean_inc(x_105);
lean_dec(x_20);
x_106 = lean_expr_eqv(x_2, x_3);
x_107 = 1;
x_108 = l_Bool_DecidableEq(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_105);
return x_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_105);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_7);
x_112 = !lean_is_exclusive(x_20);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_20, 0);
lean_dec(x_113);
x_114 = lean_expr_eqv(x_2, x_3);
x_115 = 1;
x_116 = l_Bool_DecidableEq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_20, 0, x_117);
return x_20;
}
else
{
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
}
else
{
lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_20, 1);
lean_inc(x_118);
lean_dec(x_20);
x_119 = lean_expr_eqv(x_2, x_3);
x_120 = 1;
x_121 = l_Bool_DecidableEq(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_118);
return x_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_118);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_7);
x_125 = !lean_is_exclusive(x_20);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_20, 0);
lean_dec(x_126);
x_127 = lean_expr_eqv(x_2, x_3);
x_128 = 1;
x_129 = l_Bool_DecidableEq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_20, 0, x_130);
return x_20;
}
else
{
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
}
else
{
lean_object* x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_20, 1);
lean_inc(x_131);
lean_dec(x_20);
x_132 = lean_expr_eqv(x_2, x_3);
x_133 = 1;
x_134 = l_Bool_DecidableEq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_131);
return x_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_131);
return x_137;
}
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_20);
if (x_138 == 0)
{
return x_20;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_20, 0);
x_140 = lean_ctor_get(x_20, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_20);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_1__getFirstCtor___at_Lean_Meta_unfoldDefinition___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_14) == 5)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_free_object(x_6);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_6, 0, x_25);
return x_5;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
lean_ctor_set(x_6, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_6);
lean_dec(x_14);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_5, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_6, 0);
lean_inc(x_35);
lean_dec(x_6);
if (lean_obj_tag(x_35) == 5)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 4);
lean_inc(x_37);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_39 = x_5;
} else {
 lean_dec_ref(x_5);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_43 = x_5;
} else {
 lean_dec_ref(x_5);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_35);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_48 = x_5;
} else {
 lean_dec_ref(x_5);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_5);
if (x_51 == 0)
{
return x_5;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_5, 0);
x_53 = lean_ctor_get(x_5, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_5);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at_Lean_Meta_unfoldDefinition___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_WHNF_1__getFirstCtor___at_Lean_Meta_unfoldDefinition___spec__11(x_1, x_7, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = l_Lean_mkConst(x_20, x_8);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_22);
x_24 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_25, x_27);
x_29 = l_Array_shrink___main___rarg(x_28, x_3);
x_30 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_29, x_29, x_22, x_21);
lean_dec(x_29);
lean_ctor_set(x_10, 0, x_30);
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec(x_10);
x_32 = l_Lean_mkConst(x_31, x_8);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_33);
x_35 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_36, x_38);
x_40 = l_Array_shrink___main___rarg(x_39, x_3);
x_41 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_40, x_40, x_33, x_32);
lean_dec(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_9, 0, x_42);
return x_9;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_dec(x_9);
x_44 = lean_ctor_get(x_10, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_45 = x_10;
} else {
 lean_dec_ref(x_10);
 x_45 = lean_box(0);
}
x_46 = l_Lean_mkConst(x_44, x_8);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_47);
x_49 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_48);
x_50 = lean_mk_array(x_48, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_48, x_51);
lean_dec(x_48);
x_53 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_50, x_52);
x_54 = l_Array_shrink___main___rarg(x_53, x_3);
x_55 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_54, x_54, x_47, x_46);
lean_dec(x_54);
if (lean_is_scalar(x_45)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_45;
}
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_43);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_9);
if (x_58 == 0)
{
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_5);
return x_63;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_Expr_hasExprMVar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_hasExprMVar(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_2 = lean_box(0);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
lean_object* _init_l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getConstNoEx___boxed), 3, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_inferType(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
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
lean_inc(x_3);
x_9 = l_Lean_Meta_whnf(x_6, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_80; uint8_t x_81; lean_object* x_101; uint8_t x_102; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_80 = l_Lean_Expr_getAppFn___main(x_10);
x_101 = l_Lean_RecursorVal_getInduct(x_1);
x_102 = l_Lean_Expr_isConstOf(x_80, x_101);
lean_dec(x_101);
lean_dec(x_80);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = 1;
x_81 = x_103;
goto block_100;
}
else
{
uint8_t x_104; 
x_104 = 0;
x_81 = x_104;
goto block_100;
}
block_79:
{
uint8_t x_14; uint8_t x_15; 
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9___closed__1;
lean_inc(x_3);
lean_inc(x_10);
x_18 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at_Lean_Meta_unfoldDefinition___spec__10(x_17, x_10, x_16, x_3, x_11);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_3);
lean_inc(x_26);
x_27 = l_Lean_Meta_inferType(x_26, x_3, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_isExprDefEq(x_10, x_28, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = l_Bool_DecidableEq(x_33, x_14);
if (x_34 == 0)
{
lean_object* x_35; 
lean_free_object(x_19);
lean_dec(x_26);
x_35 = lean_box(0);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_39 = l_Bool_DecidableEq(x_38, x_14);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_19);
lean_dec(x_26);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_free_object(x_19);
lean_dec(x_26);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_19);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_19, 0);
lean_inc(x_51);
lean_dec(x_19);
lean_inc(x_3);
lean_inc(x_51);
x_52 = l_Lean_Meta_inferType(x_51, x_3, x_24);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Meta_isExprDefEq(x_10, x_53, x_3, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_unbox(x_56);
lean_dec(x_56);
x_60 = l_Bool_DecidableEq(x_59, x_14);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
x_61 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_51);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_51);
x_65 = lean_ctor_get(x_55, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_67 = x_55;
} else {
 lean_dec_ref(x_55);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec(x_3);
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_71 = x_52;
} else {
 lean_dec_ref(x_52);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_10);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_18);
if (x_73 == 0)
{
return x_18;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_18, 0);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_18);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_77 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_12;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_11);
return x_78;
}
}
block_100:
{
uint8_t x_82; uint8_t x_83; 
x_82 = 1;
x_83 = l_Bool_DecidableEq(x_81, x_82);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_8);
x_84 = l_Lean_Expr_hasExprMVar(x_10);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = 0;
x_13 = x_85;
goto block_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_86);
x_88 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_87);
x_89 = lean_mk_array(x_87, x_88);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_sub(x_87, x_90);
lean_dec(x_87);
lean_inc(x_10);
x_92 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_10, x_89, x_91);
x_93 = lean_ctor_get(x_1, 2);
lean_inc(x_93);
x_94 = lean_array_get_size(x_92);
x_95 = lean_nat_dec_le(x_94, x_94);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__12(x_10, x_92, x_94, x_93);
lean_dec(x_94);
lean_dec(x_92);
x_13 = x_96;
goto block_79;
}
else
{
uint8_t x_97; 
x_97 = l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__13(x_10, lean_box(0), x_92, x_94, x_93);
lean_dec(x_94);
lean_dec(x_92);
x_13 = x_97;
goto block_79;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_8;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_11);
return x_99;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_9);
if (x_105 == 0)
{
return x_9;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_9, 0);
x_107 = lean_ctor_get(x_9, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_9);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_5);
if (x_109 == 0)
{
return x_5;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_5, 0);
x_111 = lean_ctor_get(x_5, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_5);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
lean_object* l_Lean_WHNF_reduceRec___at_Lean_Meta_unfoldDefinition___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_RecursorVal_getMajorIdx(x_4);
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_expr_eqv(x_2, x_3);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_6, x_9);
lean_inc(x_7);
x_19 = l_Lean_Meta_whnf(x_18, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_91; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_91 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = l_String_Iterator_extract___closed__1;
if (x_92 == 0)
{
lean_object* x_93; 
lean_inc(x_7);
lean_inc(x_20);
lean_inc(x_4);
x_93 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9(x_4, x_20, x_7, x_21);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_23 = x_20;
x_24 = x_95;
goto block_90;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_20);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_dec(x_94);
x_23 = x_97;
x_24 = x_96;
goto block_90;
}
}
else
{
uint8_t x_98; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_93);
if (x_98 == 0)
{
return x_93;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_93, 0);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_93);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_22);
x_102 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_20);
lean_dec(x_20);
lean_inc(x_4);
x_103 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_4, x_102);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; uint8_t x_105; uint8_t x_106; 
lean_dec(x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_104 = lean_expr_eqv(x_2, x_3);
x_105 = 1;
x_106 = l_Bool_DecidableEq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_21);
return x_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_21);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Lean_Expr_getAppNumArgsAux___main(x_102, x_111);
x_113 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_112);
x_114 = lean_mk_array(x_112, x_113);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_sub(x_112, x_115);
lean_dec(x_112);
x_117 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_102, x_114, x_116);
x_118 = l_List_lengthAux___main___rarg(x_5, x_111);
x_119 = lean_ctor_get(x_4, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_List_lengthAux___main___rarg(x_120, x_111);
x_122 = lean_nat_dec_eq(x_118, x_121);
lean_dec(x_121);
lean_dec(x_118);
if (x_122 == 0)
{
uint8_t x_123; uint8_t x_124; uint8_t x_125; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_110);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_123 = lean_expr_eqv(x_2, x_3);
x_124 = 1;
x_125 = l_Bool_DecidableEq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_21);
return x_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_21);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_1);
x_130 = lean_ctor_get(x_110, 2);
lean_inc(x_130);
x_131 = lean_instantiate_lparams(x_130, x_120, x_5);
x_132 = lean_ctor_get(x_4, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_4, 4);
lean_inc(x_133);
x_134 = lean_nat_add(x_132, x_133);
lean_dec(x_133);
lean_dec(x_132);
x_135 = lean_ctor_get(x_4, 5);
lean_inc(x_135);
lean_dec(x_4);
x_136 = lean_nat_add(x_134, x_135);
lean_dec(x_135);
lean_dec(x_134);
x_137 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_136, x_6, x_111, x_131);
lean_dec(x_136);
x_138 = lean_array_get_size(x_117);
x_139 = lean_ctor_get(x_110, 1);
lean_inc(x_139);
lean_dec(x_110);
x_140 = lean_nat_sub(x_138, x_139);
lean_dec(x_139);
x_141 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_138, x_117, x_140, x_137);
lean_dec(x_117);
lean_dec(x_138);
x_142 = lean_nat_add(x_9, x_115);
lean_dec(x_9);
x_143 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_10, x_6, x_142, x_141);
lean_dec(x_10);
x_144 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_143, x_7, x_21);
return x_144;
}
else
{
uint8_t x_145; uint8_t x_146; uint8_t x_147; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_110);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_145 = lean_expr_eqv(x_2, x_3);
x_146 = 1;
x_147 = l_Bool_DecidableEq(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_21);
return x_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_1);
lean_ctor_set(x_150, 1, x_21);
return x_150;
}
}
}
}
}
}
else
{
uint8_t x_151; 
x_151 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_151 == 0)
{
lean_object* x_152; 
lean_inc(x_7);
lean_inc(x_20);
lean_inc(x_4);
x_152 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9(x_4, x_20, x_7, x_21);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_23 = x_20;
x_24 = x_154;
goto block_90;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_20);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
lean_dec(x_153);
x_23 = x_156;
x_24 = x_155;
goto block_90;
}
}
else
{
uint8_t x_157; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_152);
if (x_157 == 0)
{
return x_152;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_152, 0);
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_152);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_22);
x_161 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_20);
lean_dec(x_20);
lean_inc(x_4);
x_162 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_4, x_161);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; uint8_t x_164; uint8_t x_165; 
lean_dec(x_161);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_163 = lean_expr_eqv(x_2, x_3);
x_164 = 1;
x_165 = l_Bool_DecidableEq(x_163, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_21);
return x_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_21);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_169 = lean_ctor_get(x_162, 0);
lean_inc(x_169);
lean_dec(x_162);
x_170 = lean_unsigned_to_nat(0u);
x_171 = l_Lean_Expr_getAppNumArgsAux___main(x_161, x_170);
x_172 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_171);
x_173 = lean_mk_array(x_171, x_172);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_sub(x_171, x_174);
lean_dec(x_171);
x_176 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_161, x_173, x_175);
x_177 = l_List_lengthAux___main___rarg(x_5, x_170);
x_178 = lean_ctor_get(x_4, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = l_List_lengthAux___main___rarg(x_179, x_170);
x_181 = lean_nat_dec_eq(x_177, x_180);
lean_dec(x_180);
lean_dec(x_177);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = l_String_Iterator_extract___closed__1;
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_1);
x_183 = lean_ctor_get(x_169, 2);
lean_inc(x_183);
x_184 = lean_instantiate_lparams(x_183, x_179, x_5);
x_185 = lean_ctor_get(x_4, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_4, 4);
lean_inc(x_186);
x_187 = lean_nat_add(x_185, x_186);
lean_dec(x_186);
lean_dec(x_185);
x_188 = lean_ctor_get(x_4, 5);
lean_inc(x_188);
lean_dec(x_4);
x_189 = lean_nat_add(x_187, x_188);
lean_dec(x_188);
lean_dec(x_187);
x_190 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_189, x_6, x_170, x_184);
lean_dec(x_189);
x_191 = lean_array_get_size(x_176);
x_192 = lean_ctor_get(x_169, 1);
lean_inc(x_192);
lean_dec(x_169);
x_193 = lean_nat_sub(x_191, x_192);
lean_dec(x_192);
x_194 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_191, x_176, x_193, x_190);
lean_dec(x_176);
lean_dec(x_191);
x_195 = lean_nat_add(x_9, x_174);
lean_dec(x_9);
x_196 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_10, x_6, x_195, x_194);
lean_dec(x_10);
x_197 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_196, x_7, x_21);
return x_197;
}
else
{
uint8_t x_198; uint8_t x_199; uint8_t x_200; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_169);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_198 = lean_expr_eqv(x_2, x_3);
x_199 = 1;
x_200 = l_Bool_DecidableEq(x_198, x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_21);
return x_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_21);
return x_203;
}
}
}
else
{
uint8_t x_204; uint8_t x_205; uint8_t x_206; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_169);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_204 = lean_expr_eqv(x_2, x_3);
x_205 = 1;
x_206 = l_Bool_DecidableEq(x_204, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_21);
return x_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_1);
lean_ctor_set(x_209, 1, x_21);
return x_209;
}
}
}
}
}
block_90:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_23);
lean_dec(x_23);
lean_inc(x_4);
x_26 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_4, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; uint8_t x_28; uint8_t x_29; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_27 = lean_expr_eqv(x_2, x_3);
x_28 = 1;
x_29 = l_Bool_DecidableEq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_22)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_22;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
else
{
lean_object* x_32; 
if (lean_is_scalar(x_22)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_22;
}
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Expr_getAppNumArgsAux___main(x_25, x_34);
x_36 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_35);
x_37 = lean_mk_array(x_35, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_35, x_38);
lean_dec(x_35);
x_40 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_25, x_37, x_39);
x_41 = l_List_lengthAux___main___rarg(x_5, x_34);
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_List_lengthAux___main___rarg(x_43, x_34);
x_45 = lean_nat_dec_eq(x_41, x_44);
lean_dec(x_44);
lean_dec(x_41);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_String_Iterator_extract___closed__1;
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_22);
lean_dec(x_1);
x_47 = lean_ctor_get(x_33, 2);
lean_inc(x_47);
x_48 = lean_instantiate_lparams(x_47, x_43, x_5);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 4);
lean_inc(x_50);
x_51 = lean_nat_add(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
x_52 = lean_ctor_get(x_4, 5);
lean_inc(x_52);
lean_dec(x_4);
x_53 = lean_nat_add(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
x_54 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_53, x_6, x_34, x_48);
lean_dec(x_53);
x_55 = lean_array_get_size(x_40);
x_56 = lean_ctor_get(x_33, 1);
lean_inc(x_56);
lean_dec(x_33);
x_57 = lean_nat_sub(x_55, x_56);
lean_dec(x_56);
x_58 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_55, x_40, x_57, x_54);
lean_dec(x_40);
lean_dec(x_55);
x_59 = lean_nat_add(x_9, x_38);
lean_dec(x_9);
x_60 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_10, x_6, x_59, x_58);
lean_dec(x_10);
x_61 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_60, x_7, x_24);
return x_61;
}
else
{
uint8_t x_62; uint8_t x_63; uint8_t x_64; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_62 = lean_expr_eqv(x_2, x_3);
x_63 = 1;
x_64 = l_Bool_DecidableEq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_22)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_22;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_24);
return x_66;
}
else
{
lean_object* x_67; 
if (lean_is_scalar(x_22)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_22;
}
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_24);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_22);
lean_dec(x_1);
x_69 = lean_ctor_get(x_33, 2);
lean_inc(x_69);
x_70 = lean_instantiate_lparams(x_69, x_43, x_5);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 4);
lean_inc(x_72);
x_73 = lean_nat_add(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
x_74 = lean_ctor_get(x_4, 5);
lean_inc(x_74);
lean_dec(x_4);
x_75 = lean_nat_add(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
x_76 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_75, x_6, x_34, x_70);
lean_dec(x_75);
x_77 = lean_array_get_size(x_40);
x_78 = lean_ctor_get(x_33, 1);
lean_inc(x_78);
lean_dec(x_33);
x_79 = lean_nat_sub(x_77, x_78);
lean_dec(x_78);
x_80 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_77, x_40, x_79, x_76);
lean_dec(x_40);
lean_dec(x_77);
x_81 = lean_nat_add(x_9, x_38);
lean_dec(x_9);
x_82 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_10, x_6, x_81, x_80);
lean_dec(x_10);
x_83 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_82, x_7, x_24);
return x_83;
}
else
{
uint8_t x_84; uint8_t x_85; uint8_t x_86; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_84 = lean_expr_eqv(x_2, x_3);
x_85 = 1;
x_86 = l_Bool_DecidableEq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_22)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_22;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_24);
return x_88;
}
else
{
lean_object* x_89; 
if (lean_is_scalar(x_22)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_22;
}
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_24);
return x_89;
}
}
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_19);
if (x_210 == 0)
{
return x_19;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_19, 0);
x_212 = lean_ctor_get(x_19, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_19);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_LocalDecl_value_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_4(x_8, lean_box(0), x_2, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14(x_1, x_10, x_4, x_5);
return x_11;
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_4(x_7, lean_box(0), x_2, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14(x_1, x_9, x_4, x_5);
return x_10;
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_10 = l_Lean_Expr_Inhabited;
x_11 = l_monadInhabited___rarg(x_1, x_10);
x_12 = l_unreachable_x21___rarg(x_11);
x_13 = lean_apply_2(x_12, x_3, x_4);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__1___boxed), 5, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
x_18 = lean_apply_6(x_15, lean_box(0), lean_box(0), x_16, x_17, x_3, x_4);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment___boxed), 3, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__2), 5, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
x_23 = lean_apply_6(x_20, lean_box(0), lean_box(0), x_21, x_22, x_3, x_4);
return x_23;
}
case 4:
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = l_Lean_Expr_getAppFn___main(x_25);
lean_dec(x_25);
lean_inc(x_3);
lean_inc(x_26);
x_27 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_26, x_3, x_4);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Expr_isLambda(x_29);
x_32 = 1;
x_33 = l_Bool_DecidableEq(x_31, x_32);
if (x_33 == 0)
{
if (lean_obj_tag(x_29) == 4)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_free_object(x_27);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
x_36 = 0;
x_37 = l_Lean_Meta_getConstAux(x_34, x_36, x_3, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_35);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_42 = l_Bool_DecidableEq(x_41, x_32);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_dec(x_29);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
}
else
{
lean_object* x_44; uint8_t x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_46 = l_Bool_DecidableEq(x_45, x_32);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_29);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
lean_dec(x_38);
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_dec(x_37);
x_52 = l_Lean_ConstantInfo_name(x_50);
x_53 = l_Lean_Meta_isAuxDef_x3f(x_52, x_3, x_51);
lean_dec(x_52);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_unbox(x_55);
lean_dec(x_55);
x_58 = l_Bool_DecidableEq(x_57, x_32);
if (x_58 == 0)
{
uint8_t x_59; uint8_t x_60; 
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_3);
x_59 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_60 = l_Bool_DecidableEq(x_59, x_32);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
lean_ctor_set(x_53, 0, x_61);
return x_53;
}
else
{
lean_dec(x_29);
lean_ctor_set(x_53, 0, x_2);
return x_53;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_53);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_62);
x_64 = lean_mk_empty_array_with_capacity(x_63);
lean_dec(x_63);
lean_inc(x_2);
x_65 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_64);
x_66 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__6(x_2, x_26, x_29, x_50, x_35, x_65, x_3, x_56);
lean_dec(x_29);
lean_dec(x_26);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_70 = l_Bool_DecidableEq(x_69, x_32);
if (x_70 == 0)
{
uint8_t x_71; uint8_t x_72; 
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_3);
x_71 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_72 = l_Bool_DecidableEq(x_71, x_32);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_29);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_76);
x_78 = lean_mk_empty_array_with_capacity(x_77);
lean_dec(x_77);
lean_inc(x_2);
x_79 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_78);
x_80 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__6(x_2, x_26, x_29, x_50, x_35, x_79, x_3, x_68);
lean_dec(x_29);
lean_dec(x_26);
return x_80;
}
}
}
case 4:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_37, 1);
lean_inc(x_81);
lean_dec(x_37);
x_82 = lean_ctor_get(x_50, 0);
lean_inc(x_82);
lean_dec(x_50);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_83);
x_85 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_84);
x_86 = lean_mk_array(x_84, x_85);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_84, x_87);
lean_dec(x_84);
lean_inc(x_2);
x_89 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_86, x_88);
x_90 = l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_unfoldDefinition___spec__7(x_2, x_26, x_29, x_82, x_35, x_89, x_3, x_81);
lean_dec(x_89);
lean_dec(x_35);
lean_dec(x_82);
lean_dec(x_29);
lean_dec(x_26);
return x_90;
}
case 7:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_91 = lean_ctor_get(x_37, 1);
lean_inc(x_91);
lean_dec(x_37);
x_92 = lean_ctor_get(x_50, 0);
lean_inc(x_92);
lean_dec(x_50);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_93);
x_95 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_94);
x_96 = lean_mk_array(x_94, x_95);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_sub(x_94, x_97);
lean_dec(x_94);
lean_inc(x_2);
x_99 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_96, x_98);
x_100 = l_Lean_WHNF_reduceRec___at_Lean_Meta_unfoldDefinition___spec__8(x_2, x_26, x_29, x_92, x_35, x_99, x_3, x_91);
lean_dec(x_99);
lean_dec(x_29);
lean_dec(x_26);
return x_100;
}
default: 
{
uint8_t x_101; 
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_37);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_37, 0);
lean_dec(x_102);
x_103 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_104 = l_Bool_DecidableEq(x_103, x_32);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
lean_ctor_set(x_37, 0, x_105);
return x_37;
}
else
{
lean_dec(x_29);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
}
else
{
lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_37, 1);
lean_inc(x_106);
lean_dec(x_37);
x_107 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_108 = l_Bool_DecidableEq(x_107, x_32);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
return x_110;
}
else
{
lean_object* x_111; 
lean_dec(x_29);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_37);
if (x_112 == 0)
{
return x_37;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_37, 0);
x_114 = lean_ctor_get(x_37, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_37);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; uint8_t x_117; 
lean_dec(x_3);
x_116 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_117 = l_Bool_DecidableEq(x_116, x_32);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_118);
return x_27;
}
else
{
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_free_object(x_27);
lean_dec(x_29);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_119);
x_121 = lean_mk_empty_array_with_capacity(x_120);
lean_dec(x_120);
x_122 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_121);
x_123 = l_Lean_Expr_betaRev(x_26, x_122);
lean_dec(x_26);
x_124 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_123, x_3, x_30);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_27, 0);
x_126 = lean_ctor_get(x_27, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_27);
x_127 = l_Lean_Expr_isLambda(x_125);
x_128 = 1;
x_129 = l_Bool_DecidableEq(x_127, x_128);
if (x_129 == 0)
{
if (lean_obj_tag(x_125) == 4)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
x_132 = 0;
x_133 = l_Lean_Meta_getConstAux(x_130, x_132, x_3, x_126);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
lean_dec(x_131);
lean_dec(x_3);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_expr_eqv(x_26, x_125);
lean_dec(x_26);
x_138 = l_Bool_DecidableEq(x_137, x_128);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Lean_Expr_updateFn___main(x_2, x_125);
lean_dec(x_125);
if (lean_is_scalar(x_136)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_136;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_135);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_125);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_2);
lean_ctor_set(x_141, 1, x_135);
return x_141;
}
}
else
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_134, 0);
lean_inc(x_142);
lean_dec(x_134);
switch (lean_obj_tag(x_142)) {
case 1:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; 
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
lean_dec(x_133);
x_144 = l_Lean_ConstantInfo_name(x_142);
x_145 = l_Lean_Meta_isAuxDef_x3f(x_144, x_3, x_143);
lean_dec(x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_unbox(x_146);
lean_dec(x_146);
x_150 = l_Bool_DecidableEq(x_149, x_128);
if (x_150 == 0)
{
uint8_t x_151; uint8_t x_152; 
lean_dec(x_142);
lean_dec(x_131);
lean_dec(x_3);
x_151 = lean_expr_eqv(x_26, x_125);
lean_dec(x_26);
x_152 = l_Bool_DecidableEq(x_151, x_128);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Lean_Expr_updateFn___main(x_2, x_125);
lean_dec(x_125);
if (lean_is_scalar(x_148)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_148;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_147);
return x_154;
}
else
{
lean_object* x_155; 
lean_dec(x_125);
if (lean_is_scalar(x_148)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_148;
}
lean_ctor_set(x_155, 0, x_2);
lean_ctor_set(x_155, 1, x_147);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_148);
x_156 = lean_unsigned_to_nat(0u);
x_157 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_156);
x_158 = lean_mk_empty_array_with_capacity(x_157);
lean_dec(x_157);
lean_inc(x_2);
x_159 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_158);
x_160 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__6(x_2, x_26, x_125, x_142, x_131, x_159, x_3, x_147);
lean_dec(x_125);
lean_dec(x_26);
return x_160;
}
}
case 4:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_133, 1);
lean_inc(x_161);
lean_dec(x_133);
x_162 = lean_ctor_get(x_142, 0);
lean_inc(x_162);
lean_dec(x_142);
x_163 = lean_unsigned_to_nat(0u);
x_164 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_163);
x_165 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_164);
x_166 = lean_mk_array(x_164, x_165);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_sub(x_164, x_167);
lean_dec(x_164);
lean_inc(x_2);
x_169 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_166, x_168);
x_170 = l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_unfoldDefinition___spec__7(x_2, x_26, x_125, x_162, x_131, x_169, x_3, x_161);
lean_dec(x_169);
lean_dec(x_131);
lean_dec(x_162);
lean_dec(x_125);
lean_dec(x_26);
return x_170;
}
case 7:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_133, 1);
lean_inc(x_171);
lean_dec(x_133);
x_172 = lean_ctor_get(x_142, 0);
lean_inc(x_172);
lean_dec(x_142);
x_173 = lean_unsigned_to_nat(0u);
x_174 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_173);
x_175 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_174);
x_176 = lean_mk_array(x_174, x_175);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_sub(x_174, x_177);
lean_dec(x_174);
lean_inc(x_2);
x_179 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_176, x_178);
x_180 = l_Lean_WHNF_reduceRec___at_Lean_Meta_unfoldDefinition___spec__8(x_2, x_26, x_125, x_172, x_131, x_179, x_3, x_171);
lean_dec(x_179);
lean_dec(x_125);
lean_dec(x_26);
return x_180;
}
default: 
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_184; 
lean_dec(x_142);
lean_dec(x_131);
lean_dec(x_3);
x_181 = lean_ctor_get(x_133, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_182 = x_133;
} else {
 lean_dec_ref(x_133);
 x_182 = lean_box(0);
}
x_183 = lean_expr_eqv(x_26, x_125);
lean_dec(x_26);
x_184 = l_Bool_DecidableEq(x_183, x_128);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_Expr_updateFn___main(x_2, x_125);
lean_dec(x_125);
if (lean_is_scalar(x_182)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_182;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_181);
return x_186;
}
else
{
lean_object* x_187; 
lean_dec(x_125);
if (lean_is_scalar(x_182)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_182;
}
lean_ctor_set(x_187, 0, x_2);
lean_ctor_set(x_187, 1, x_181);
return x_187;
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_131);
lean_dec(x_125);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_188 = lean_ctor_get(x_133, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_133, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_190 = x_133;
} else {
 lean_dec_ref(x_133);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
uint8_t x_192; uint8_t x_193; 
lean_dec(x_3);
x_192 = lean_expr_eqv(x_26, x_125);
lean_dec(x_26);
x_193 = l_Bool_DecidableEq(x_192, x_128);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = l_Lean_Expr_updateFn___main(x_2, x_125);
lean_dec(x_125);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_126);
return x_195;
}
else
{
lean_object* x_196; 
lean_dec(x_125);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_126);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_125);
x_197 = lean_unsigned_to_nat(0u);
x_198 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_197);
x_199 = lean_mk_empty_array_with_capacity(x_198);
lean_dec(x_198);
x_200 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_199);
x_201 = l_Lean_Expr_betaRev(x_26, x_200);
lean_dec(x_26);
x_202 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_201, x_3, x_126);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_27);
if (x_203 == 0)
{
return x_27;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_27, 0);
x_205 = lean_ctor_get(x_27, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_27);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
case 8:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_1);
x_207 = lean_ctor_get(x_2, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_2, 3);
lean_inc(x_208);
lean_dec(x_2);
x_209 = lean_expr_instantiate1(x_208, x_207);
lean_dec(x_207);
lean_dec(x_208);
x_210 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_209, x_3, x_4);
return x_210;
}
case 10:
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_2, 1);
lean_inc(x_211);
lean_dec(x_2);
x_2 = x_211;
goto _start;
}
case 11:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_1);
x_213 = lean_ctor_get(x_2, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_2, 2);
lean_inc(x_214);
lean_inc(x_3);
x_215 = l_Lean_Meta_whnf(x_214, x_3, x_4);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = lean_ctor_get(x_215, 1);
x_219 = l_Lean_Expr_getAppFn___main(x_217);
if (lean_obj_tag(x_219) == 4)
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; 
lean_free_object(x_215);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec(x_219);
x_221 = 0;
x_222 = l_Lean_Meta_getConstAux(x_220, x_221, x_3, x_218);
lean_dec(x_3);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
lean_dec(x_217);
lean_dec(x_213);
x_224 = !lean_is_exclusive(x_222);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_222, 0);
lean_dec(x_225);
lean_ctor_set(x_222, 0, x_2);
return x_222;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_2);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
else
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_223, 0);
lean_inc(x_228);
lean_dec(x_223);
if (lean_obj_tag(x_228) == 6)
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_222);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_230 = lean_ctor_get(x_222, 0);
lean_dec(x_230);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_ctor_get(x_231, 3);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_nat_add(x_232, x_213);
lean_dec(x_213);
lean_dec(x_232);
x_234 = lean_unsigned_to_nat(0u);
x_235 = l_Lean_Expr_getAppNumArgsAux___main(x_217, x_234);
x_236 = lean_nat_sub(x_235, x_233);
lean_dec(x_233);
lean_dec(x_235);
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_nat_sub(x_236, x_237);
lean_dec(x_236);
x_239 = l_Lean_Expr_getRevArgD___main(x_217, x_238, x_2);
lean_dec(x_2);
lean_dec(x_217);
lean_ctor_set(x_222, 0, x_239);
return x_222;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_240 = lean_ctor_get(x_222, 1);
lean_inc(x_240);
lean_dec(x_222);
x_241 = lean_ctor_get(x_228, 0);
lean_inc(x_241);
lean_dec(x_228);
x_242 = lean_ctor_get(x_241, 3);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_nat_add(x_242, x_213);
lean_dec(x_213);
lean_dec(x_242);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_Lean_Expr_getAppNumArgsAux___main(x_217, x_244);
x_246 = lean_nat_sub(x_245, x_243);
lean_dec(x_243);
lean_dec(x_245);
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_nat_sub(x_246, x_247);
lean_dec(x_246);
x_249 = l_Lean_Expr_getRevArgD___main(x_217, x_248, x_2);
lean_dec(x_2);
lean_dec(x_217);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_240);
return x_250;
}
}
else
{
uint8_t x_251; 
lean_dec(x_228);
lean_dec(x_217);
lean_dec(x_213);
x_251 = !lean_is_exclusive(x_222);
if (x_251 == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_222, 0);
lean_dec(x_252);
lean_ctor_set(x_222, 0, x_2);
return x_222;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_222, 1);
lean_inc(x_253);
lean_dec(x_222);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_2);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_217);
lean_dec(x_213);
lean_dec(x_2);
x_255 = !lean_is_exclusive(x_222);
if (x_255 == 0)
{
return x_222;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_222, 0);
x_257 = lean_ctor_get(x_222, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_222);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_213);
lean_dec(x_3);
lean_ctor_set(x_215, 0, x_2);
return x_215;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_215, 0);
x_260 = lean_ctor_get(x_215, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_215);
x_261 = l_Lean_Expr_getAppFn___main(x_259);
if (lean_obj_tag(x_261) == 4)
{
lean_object* x_262; uint8_t x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec(x_261);
x_263 = 0;
x_264 = l_Lean_Meta_getConstAux(x_262, x_263, x_3, x_260);
lean_dec(x_3);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_259);
lean_dec(x_213);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_2);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
else
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
lean_dec(x_265);
if (lean_obj_tag(x_269) == 6)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_270 = lean_ctor_get(x_264, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_271 = x_264;
} else {
 lean_dec_ref(x_264);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_269, 0);
lean_inc(x_272);
lean_dec(x_269);
x_273 = lean_ctor_get(x_272, 3);
lean_inc(x_273);
lean_dec(x_272);
x_274 = lean_nat_add(x_273, x_213);
lean_dec(x_213);
lean_dec(x_273);
x_275 = lean_unsigned_to_nat(0u);
x_276 = l_Lean_Expr_getAppNumArgsAux___main(x_259, x_275);
x_277 = lean_nat_sub(x_276, x_274);
lean_dec(x_274);
lean_dec(x_276);
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_nat_sub(x_277, x_278);
lean_dec(x_277);
x_280 = l_Lean_Expr_getRevArgD___main(x_259, x_279, x_2);
lean_dec(x_2);
lean_dec(x_259);
if (lean_is_scalar(x_271)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_271;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_270);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_269);
lean_dec(x_259);
lean_dec(x_213);
x_282 = lean_ctor_get(x_264, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_283 = x_264;
} else {
 lean_dec_ref(x_264);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_2);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_259);
lean_dec(x_213);
lean_dec(x_2);
x_285 = lean_ctor_get(x_264, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_264, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_287 = x_264;
} else {
 lean_dec_ref(x_264);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
lean_object* x_289; 
lean_dec(x_261);
lean_dec(x_259);
lean_dec(x_213);
lean_dec(x_3);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_2);
lean_ctor_set(x_289, 1, x_260);
return x_289;
}
}
}
else
{
uint8_t x_290; 
lean_dec(x_213);
lean_dec(x_3);
lean_dec(x_2);
x_290 = !lean_is_exclusive(x_215);
if (x_290 == 0)
{
return x_215;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_215, 0);
x_292 = lean_ctor_get(x_215, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_215);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
case 12:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_2);
x_294 = l_Lean_Expr_Inhabited;
x_295 = l_monadInhabited___rarg(x_1, x_294);
x_296 = l_unreachable_x21___rarg(x_295);
x_297 = lean_apply_2(x_296, x_3, x_4);
return x_297;
}
default: 
{
lean_object* x_298; 
x_298 = lean_box(0);
x_5 = x_298;
goto block_9;
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_4(x_7, lean_box(0), x_2, x_3, x_4);
return x_8;
}
}
}
lean_object* _init_l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EIO_Monad___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5___closed__1;
x_5 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_WHNF_isQuotRecStuck___at_Lean_Meta_unfoldDefinition___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_21; lean_object* x_22; 
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_22 = lean_box(x_21);
switch (lean_obj_tag(x_22)) {
case 2:
{
lean_object* x_23; 
x_23 = lean_unsigned_to_nat(5u);
x_6 = x_23;
goto block_20;
}
case 3:
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(4u);
x_6 = x_24;
goto block_20;
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_4);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
block_20:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_3, x_6);
lean_inc(x_4);
x_12 = l_Lean_Meta_whnf(x_11, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_WHNF_getStuckMVar___main___at_Lean_Meta_unfoldDefinition___spec__15(x_13, x_4, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
lean_object* l_Lean_WHNF_isRecStuck___at_Lean_Meta_unfoldDefinition___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_RecursorVal_getMajorIdx(x_1);
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_3, x_9);
lean_dec(x_9);
lean_inc(x_4);
x_15 = l_Lean_Meta_whnf(x_14, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_WHNF_getStuckMVar___main___at_Lean_Meta_unfoldDefinition___spec__15(x_16, x_4, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
lean_object* l_Lean_WHNF_getStuckMVar___main___at_Lean_Meta_unfoldDefinition___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 5:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_Expr_getAppFn___main(x_6);
lean_dec(x_6);
switch (lean_obj_tag(x_7)) {
case 2:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = 0;
x_13 = l_Lean_Meta_getConstAux(x_10, x_12, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
switch (lean_obj_tag(x_21)) {
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_24);
x_26 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_25);
x_27 = lean_mk_array(x_25, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_27, x_29);
x_31 = l_Lean_WHNF_isQuotRecStuck___at_Lean_Meta_unfoldDefinition___spec__16(x_23, x_11, x_30, x_2, x_22);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_23);
return x_31;
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_34);
x_36 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_35);
x_37 = lean_mk_array(x_35, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_35, x_38);
lean_dec(x_35);
x_40 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_1, x_37, x_39);
x_41 = l_Lean_WHNF_isRecStuck___at_Lean_Meta_unfoldDefinition___spec__17(x_33, x_11, x_40, x_2, x_32);
lean_dec(x_40);
lean_dec(x_11);
lean_dec(x_33);
return x_41;
}
default: 
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_13, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_13, 0, x_44);
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_dec(x_13);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
}
case 10:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec(x_1);
x_1 = x_54;
goto _start;
}
case 11:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
lean_dec(x_1);
lean_inc(x_2);
x_57 = l_Lean_Meta_whnf(x_56, x_2, x_3);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_1 = x_58;
x_3 = x_59;
goto _start;
}
else
{
uint8_t x_61; 
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at_Lean_Meta_unfoldDefinition___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_7 = l_Lean_WHNF_getStuckMVar___main___at_Lean_Meta_unfoldDefinition___spec__15(x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
lean_inc(x_2);
x_15 = l_Lean_Meta_synthPending(x_14, x_2, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = 1;
x_20 = lean_unbox(x_17);
lean_dec(x_17);
x_21 = l_Bool_DecidableEq(x_20, x_19);
if (x_21 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
else
{
lean_free_object(x_15);
x_1 = x_5;
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = 1;
x_26 = lean_unbox(x_23);
lean_dec(x_23);
x_27 = l_Bool_DecidableEq(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
x_1 = x_5;
x_3 = x_24;
goto _start;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_4);
if (x_38 == 0)
{
return x_4;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_ConstantInfo_lparams(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_List_lengthAux___main___rarg(x_6, x_7);
lean_dec(x_6);
x_9 = l_List_lengthAux___main___rarg(x_2, x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_String_Iterator_extract___closed__1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_instantiate_value_lparams(x_1, x_2);
x_13 = l_Lean_Expr_betaRev(x_12, x_3);
lean_dec(x_12);
x_14 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_13);
x_15 = l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at_Lean_Meta_unfoldDefinition___spec__4(x_14, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l___private_Init_Lean_WHNF_6__isIdRhsApp(x_17);
x_19 = 1;
x_20 = l_Bool_DecidableEq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
x_21 = lean_box(0);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = l___private_Init_Lean_WHNF_6__isIdRhsApp(x_24);
x_27 = 1;
x_28 = l_Bool_DecidableEq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_24);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_instantiate_value_lparams(x_1, x_2);
x_42 = l_Lean_Expr_betaRev(x_41, x_3);
lean_dec(x_41);
x_43 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_42);
x_44 = l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at_Lean_Meta_unfoldDefinition___spec__4(x_43, x_4, x_5);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = l___private_Init_Lean_WHNF_6__isIdRhsApp(x_46);
x_48 = 1;
x_49 = l_Bool_DecidableEq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_46);
x_50 = lean_box(0);
lean_ctor_set(x_44, 0, x_50);
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_46);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = l___private_Init_Lean_WHNF_6__isIdRhsApp(x_53);
x_56 = 1;
x_57 = l_Bool_DecidableEq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_53);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_44);
if (x_63 == 0)
{
return x_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_44, 0);
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_44);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_5);
return x_68;
}
}
}
}
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 0;
x_7 = l_Lean_Meta_getConstAux(x_4, x_6, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l___private_Init_Lean_WHNF_8__deltaDefinition___at_Lean_Meta_unfoldDefinition___spec__2(x_15, x_5, x_2, x_16);
lean_dec(x_2);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
case 5:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = l_Lean_Expr_getAppFn___main(x_28);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 4)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 0;
x_33 = l_Lean_Meta_getConstAux(x_30, x_32, x_2, x_3);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_42 = x_33;
} else {
 lean_dec_ref(x_33);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_108 = l_Lean_ConstantInfo_lparams(x_43);
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_List_lengthAux___main___rarg(x_108, x_109);
lean_dec(x_108);
x_111 = l_List_lengthAux___main___rarg(x_31, x_109);
x_112 = lean_nat_dec_eq(x_110, x_111);
lean_dec(x_111);
lean_dec(x_110);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = 1;
x_44 = x_113;
goto block_107;
}
else
{
x_44 = x_32;
goto block_107;
}
block_107:
{
uint8_t x_45; uint8_t x_46; 
x_45 = 1;
x_46 = l_Bool_DecidableEq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
x_47 = l_Lean_ConstantInfo_name(x_43);
x_48 = l_Lean_WHNF_smartUnfoldingSuffix;
x_49 = lean_name_mk_string(x_47, x_48);
x_50 = l_Lean_Meta_getConstAux(x_49, x_32, x_2, x_41);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_50, 0);
lean_dec(x_54);
x_55 = l_Lean_ConstantInfo_hasValue(x_43);
x_56 = l_Bool_DecidableEq(x_55, x_45);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_43);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_50, 0, x_57);
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_50);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_58);
x_60 = lean_mk_empty_array_with_capacity(x_59);
lean_dec(x_59);
x_61 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_60);
x_62 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3(x_43, x_31, x_61, x_2, x_53);
lean_dec(x_2);
return x_62;
}
}
else
{
lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_dec(x_50);
x_64 = l_Lean_ConstantInfo_hasValue(x_43);
x_65 = l_Bool_DecidableEq(x_64, x_45);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_43);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_68);
x_70 = lean_mk_empty_array_with_capacity(x_69);
lean_dec(x_69);
x_71 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_70);
x_72 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3(x_43, x_31, x_71, x_2, x_63);
lean_dec(x_2);
return x_72;
}
}
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_51, 0);
lean_inc(x_73);
lean_dec(x_51);
if (lean_obj_tag(x_73) == 1)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_43);
x_74 = lean_ctor_get(x_50, 1);
lean_inc(x_74);
lean_dec(x_50);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_75);
x_77 = lean_mk_empty_array_with_capacity(x_76);
lean_dec(x_76);
x_78 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_77);
x_79 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__18(x_73, x_31, x_78, x_2, x_74);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_73);
x_80 = !lean_is_exclusive(x_50);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_50, 1);
x_82 = lean_ctor_get(x_50, 0);
lean_dec(x_82);
x_83 = l_Lean_ConstantInfo_hasValue(x_43);
x_84 = l_Bool_DecidableEq(x_83, x_45);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_43);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_box(0);
lean_ctor_set(x_50, 0, x_85);
return x_50;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_free_object(x_50);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_86);
x_88 = lean_mk_empty_array_with_capacity(x_87);
lean_dec(x_87);
x_89 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_88);
x_90 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3(x_43, x_31, x_89, x_2, x_81);
lean_dec(x_2);
return x_90;
}
}
else
{
lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_50, 1);
lean_inc(x_91);
lean_dec(x_50);
x_92 = l_Lean_ConstantInfo_hasValue(x_43);
x_93 = l_Bool_DecidableEq(x_92, x_45);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_43);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_96);
x_98 = lean_mk_empty_array_with_capacity(x_97);
lean_dec(x_97);
x_99 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_1, x_98);
x_100 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3(x_43, x_31, x_99, x_2, x_91);
lean_dec(x_2);
return x_100;
}
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_43);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_50);
if (x_101 == 0)
{
return x_50;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_50, 0);
x_103 = lean_ctor_get(x_50, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_50);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_43);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_42;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_41);
return x_106;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_33);
if (x_114 == 0)
{
return x_33;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_33, 0);
x_116 = lean_ctor_get(x_33, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_33);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_3);
return x_119;
}
}
default: 
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_3);
return x_121;
}
}
}
}
lean_object* l_Lean_Meta_unfoldDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_WHNF_8__deltaDefinition___at_Lean_Meta_unfoldDefinition___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_WHNF_8__deltaDefinition___at_Lean_Meta_unfoldDefinition___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_unfoldDefinition___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_unfoldDefinition___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_unfoldDefinition___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at_Lean_Meta_unfoldDefinition___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at_Lean_Meta_unfoldDefinition___spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_unfoldDefinition___spec__13(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_WHNF_reduceRec___at_Lean_Meta_unfoldDefinition___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_reduceRec___at_Lean_Meta_unfoldDefinition___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_unfoldDefinition___spec__14___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_WHNF_isQuotRecStuck___at_Lean_Meta_unfoldDefinition___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_WHNF_isQuotRecStuck___at_Lean_Meta_unfoldDefinition___spec__16(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_WHNF_isRecStuck___at_Lean_Meta_unfoldDefinition___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_WHNF_isRecStuck___at_Lean_Meta_unfoldDefinition___spec__17(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_ConstantInfo_lparams(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___main___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthAux___main___rarg(x_5, x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_String_Iterator_extract___closed__1;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_15 = lean_instantiate_value_lparams(x_4, x_5);
x_16 = l_Lean_Expr_betaRev(x_15, x_6);
lean_dec(x_15);
x_17 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_16);
x_18 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_17, x_7, x_8);
return x_18;
}
else
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_expr_eqv(x_2, x_3);
x_20 = 1;
x_21 = l_Bool_DecidableEq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_26 = lean_instantiate_value_lparams(x_4, x_5);
x_27 = l_Lean_Expr_betaRev(x_26, x_6);
lean_dec(x_26);
x_28 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_27);
x_29 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_28, x_7, x_8);
return x_29;
}
else
{
uint8_t x_30; uint8_t x_31; uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_expr_eqv(x_2, x_3);
x_31 = 1;
x_32 = l_Bool_DecidableEq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
}
}
}
lean_object* l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_whnfCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_143; lean_object* x_144; 
x_143 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_144 = lean_box(x_143);
switch (lean_obj_tag(x_144)) {
case 2:
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_unsigned_to_nat(5u);
x_146 = lean_unsigned_to_nat(3u);
x_9 = x_145;
x_10 = x_146;
goto block_142;
}
case 3:
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_unsigned_to_nat(4u);
x_148 = lean_unsigned_to_nat(3u);
x_9 = x_147;
x_10 = x_148;
goto block_142;
}
default: 
{
uint8_t x_149; uint8_t x_150; uint8_t x_151; 
lean_dec(x_144);
lean_dec(x_7);
x_149 = lean_expr_eqv(x_2, x_3);
x_150 = 1;
x_151 = l_Bool_DecidableEq(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_8);
return x_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_1);
lean_ctor_set(x_154, 1, x_8);
return x_154;
}
}
}
block_142:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_lt(x_9, x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_7);
x_13 = lean_expr_eqv(x_2, x_3);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_6, x_9);
lean_inc(x_7);
x_20 = l_Lean_Meta_whnf(x_19, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 5)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = 0;
x_29 = l_Lean_Meta_getConstAux(x_27, x_28, x_7, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_expr_eqv(x_2, x_3);
x_34 = 1;
x_35 = l_Bool_DecidableEq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_36);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_expr_eqv(x_2, x_3);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
lean_dec(x_30);
if (lean_obj_tag(x_44) == 4)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
x_47 = lean_box(x_46);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = l_Lean_Expr_Inhabited;
x_50 = lean_array_get(x_49, x_6, x_10);
x_51 = l_Lean_mkApp(x_50, x_26);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_9, x_52);
x_54 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_11, x_6, x_53, x_51);
lean_dec(x_11);
x_55 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_54, x_7, x_48);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_47);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_29);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_29, 0);
lean_dec(x_57);
x_58 = lean_expr_eqv(x_2, x_3);
x_59 = 1;
x_60 = l_Bool_DecidableEq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_61);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_dec(x_29);
x_63 = lean_expr_eqv(x_2, x_3);
x_64 = 1;
x_65 = l_Bool_DecidableEq(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_44);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
x_69 = !lean_is_exclusive(x_29);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_29, 0);
lean_dec(x_70);
x_71 = lean_expr_eqv(x_2, x_3);
x_72 = 1;
x_73 = l_Bool_DecidableEq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_29, 0, x_74);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
}
else
{
lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_29, 1);
lean_inc(x_75);
lean_dec(x_29);
x_76 = lean_expr_eqv(x_2, x_3);
x_77 = 1;
x_78 = l_Bool_DecidableEq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_29);
if (x_82 == 0)
{
return x_29;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_29, 0);
x_84 = lean_ctor_get(x_29, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_29);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_7);
x_86 = !lean_is_exclusive(x_20);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_20, 0);
lean_dec(x_87);
x_88 = lean_expr_eqv(x_2, x_3);
x_89 = 1;
x_90 = l_Bool_DecidableEq(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_20, 0, x_91);
return x_20;
}
else
{
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
}
else
{
lean_object* x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_20, 1);
lean_inc(x_92);
lean_dec(x_20);
x_93 = lean_expr_eqv(x_2, x_3);
x_94 = 1;
x_95 = l_Bool_DecidableEq(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
return x_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_92);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_7);
x_99 = !lean_is_exclusive(x_20);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_20, 0);
lean_dec(x_100);
x_101 = lean_expr_eqv(x_2, x_3);
x_102 = 1;
x_103 = l_Bool_DecidableEq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_20, 0, x_104);
return x_20;
}
else
{
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
}
else
{
lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_20, 1);
lean_inc(x_105);
lean_dec(x_20);
x_106 = lean_expr_eqv(x_2, x_3);
x_107 = 1;
x_108 = l_Bool_DecidableEq(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_105);
return x_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_105);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_7);
x_112 = !lean_is_exclusive(x_20);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_20, 0);
lean_dec(x_113);
x_114 = lean_expr_eqv(x_2, x_3);
x_115 = 1;
x_116 = l_Bool_DecidableEq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_20, 0, x_117);
return x_20;
}
else
{
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
}
else
{
lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_20, 1);
lean_inc(x_118);
lean_dec(x_20);
x_119 = lean_expr_eqv(x_2, x_3);
x_120 = 1;
x_121 = l_Bool_DecidableEq(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_118);
return x_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_118);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_7);
x_125 = !lean_is_exclusive(x_20);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_20, 0);
lean_dec(x_126);
x_127 = lean_expr_eqv(x_2, x_3);
x_128 = 1;
x_129 = l_Bool_DecidableEq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = l_Lean_Expr_updateFn___main(x_1, x_3);
lean_ctor_set(x_20, 0, x_130);
return x_20;
}
else
{
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
}
else
{
lean_object* x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_20, 1);
lean_inc(x_131);
lean_dec(x_20);
x_132 = lean_expr_eqv(x_2, x_3);
x_133 = 1;
x_134 = l_Bool_DecidableEq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_131);
return x_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_131);
return x_137;
}
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_20);
if (x_138 == 0)
{
return x_20;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_20, 0);
x_140 = lean_ctor_get(x_20, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_20);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_Expr_hasExprMVar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_hasExprMVar(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_2 = lean_box(0);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_whnfCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_inferType(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
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
lean_inc(x_3);
x_9 = l_Lean_Meta_whnf(x_6, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_80; uint8_t x_81; lean_object* x_101; uint8_t x_102; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_80 = l_Lean_Expr_getAppFn___main(x_10);
x_101 = l_Lean_RecursorVal_getInduct(x_1);
x_102 = l_Lean_Expr_isConstOf(x_80, x_101);
lean_dec(x_101);
lean_dec(x_80);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = 1;
x_81 = x_103;
goto block_100;
}
else
{
uint8_t x_104; 
x_104 = 0;
x_81 = x_104;
goto block_100;
}
block_79:
{
uint8_t x_14; uint8_t x_15; 
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9___closed__1;
lean_inc(x_3);
lean_inc(x_10);
x_18 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at_Lean_Meta_unfoldDefinition___spec__10(x_17, x_10, x_16, x_3, x_11);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_3);
lean_inc(x_26);
x_27 = l_Lean_Meta_inferType(x_26, x_3, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_isExprDefEqAux(x_10, x_28, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = l_Bool_DecidableEq(x_33, x_14);
if (x_34 == 0)
{
lean_object* x_35; 
lean_free_object(x_19);
lean_dec(x_26);
x_35 = lean_box(0);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_39 = l_Bool_DecidableEq(x_38, x_14);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_19);
lean_dec(x_26);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_free_object(x_19);
lean_dec(x_26);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_19);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_19, 0);
lean_inc(x_51);
lean_dec(x_19);
lean_inc(x_3);
lean_inc(x_51);
x_52 = l_Lean_Meta_inferType(x_51, x_3, x_24);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Meta_isExprDefEqAux(x_10, x_53, x_3, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_unbox(x_56);
lean_dec(x_56);
x_60 = l_Bool_DecidableEq(x_59, x_14);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
x_61 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_51);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_51);
x_65 = lean_ctor_get(x_55, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_67 = x_55;
} else {
 lean_dec_ref(x_55);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec(x_3);
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_71 = x_52;
} else {
 lean_dec_ref(x_52);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_10);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_18);
if (x_73 == 0)
{
return x_18;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_18, 0);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_18);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_77 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_12;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_11);
return x_78;
}
}
block_100:
{
uint8_t x_82; uint8_t x_83; 
x_82 = 1;
x_83 = l_Bool_DecidableEq(x_81, x_82);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_8);
x_84 = l_Lean_Expr_hasExprMVar(x_10);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = 0;
x_13 = x_85;
goto block_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_86);
x_88 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_87);
x_89 = lean_mk_array(x_87, x_88);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_sub(x_87, x_90);
lean_dec(x_87);
lean_inc(x_10);
x_92 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_10, x_89, x_91);
x_93 = lean_ctor_get(x_1, 2);
lean_inc(x_93);
x_94 = lean_array_get_size(x_92);
x_95 = lean_nat_dec_le(x_94, x_94);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__6(x_10, x_92, x_94, x_93);
lean_dec(x_94);
lean_dec(x_92);
x_13 = x_96;
goto block_79;
}
else
{
uint8_t x_97; 
x_97 = l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__7(x_10, lean_box(0), x_92, x_94, x_93);
lean_dec(x_94);
lean_dec(x_92);
x_13 = x_97;
goto block_79;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_8;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_11);
return x_99;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_9);
if (x_105 == 0)
{
return x_9;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_9, 0);
x_107 = lean_ctor_get(x_9, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_9);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_5);
if (x_109 == 0)
{
return x_5;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_5, 0);
x_111 = lean_ctor_get(x_5, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_5);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
lean_object* l_Lean_WHNF_reduceRec___at_Lean_Meta_whnfCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_RecursorVal_getMajorIdx(x_4);
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_expr_eqv(x_2, x_3);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_6, x_9);
lean_inc(x_7);
x_19 = l_Lean_Meta_whnf(x_18, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_91; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_91 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = l_String_Iterator_extract___closed__1;
if (x_92 == 0)
{
lean_object* x_93; 
lean_inc(x_7);
lean_inc(x_20);
lean_inc(x_4);
x_93 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_whnfCore___spec__5(x_4, x_20, x_7, x_21);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_23 = x_20;
x_24 = x_95;
goto block_90;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_20);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_dec(x_94);
x_23 = x_97;
x_24 = x_96;
goto block_90;
}
}
else
{
uint8_t x_98; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_93);
if (x_98 == 0)
{
return x_93;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_93, 0);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_93);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_22);
x_102 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_20);
lean_dec(x_20);
lean_inc(x_4);
x_103 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_4, x_102);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; uint8_t x_105; uint8_t x_106; 
lean_dec(x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_104 = lean_expr_eqv(x_2, x_3);
x_105 = 1;
x_106 = l_Bool_DecidableEq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_21);
return x_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_21);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Lean_Expr_getAppNumArgsAux___main(x_102, x_111);
x_113 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_112);
x_114 = lean_mk_array(x_112, x_113);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_sub(x_112, x_115);
lean_dec(x_112);
x_117 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_102, x_114, x_116);
x_118 = l_List_lengthAux___main___rarg(x_5, x_111);
x_119 = lean_ctor_get(x_4, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_List_lengthAux___main___rarg(x_120, x_111);
x_122 = lean_nat_dec_eq(x_118, x_121);
lean_dec(x_121);
lean_dec(x_118);
if (x_122 == 0)
{
uint8_t x_123; uint8_t x_124; uint8_t x_125; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_110);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_123 = lean_expr_eqv(x_2, x_3);
x_124 = 1;
x_125 = l_Bool_DecidableEq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_21);
return x_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_21);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_1);
x_130 = lean_ctor_get(x_110, 2);
lean_inc(x_130);
x_131 = lean_instantiate_lparams(x_130, x_120, x_5);
x_132 = lean_ctor_get(x_4, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_4, 4);
lean_inc(x_133);
x_134 = lean_nat_add(x_132, x_133);
lean_dec(x_133);
lean_dec(x_132);
x_135 = lean_ctor_get(x_4, 5);
lean_inc(x_135);
lean_dec(x_4);
x_136 = lean_nat_add(x_134, x_135);
lean_dec(x_135);
lean_dec(x_134);
x_137 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_136, x_6, x_111, x_131);
lean_dec(x_136);
x_138 = lean_array_get_size(x_117);
x_139 = lean_ctor_get(x_110, 1);
lean_inc(x_139);
lean_dec(x_110);
x_140 = lean_nat_sub(x_138, x_139);
lean_dec(x_139);
x_141 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_138, x_117, x_140, x_137);
lean_dec(x_117);
lean_dec(x_138);
x_142 = lean_nat_add(x_9, x_115);
lean_dec(x_9);
x_143 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_10, x_6, x_142, x_141);
lean_dec(x_10);
x_144 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_143, x_7, x_21);
return x_144;
}
else
{
uint8_t x_145; uint8_t x_146; uint8_t x_147; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_110);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_145 = lean_expr_eqv(x_2, x_3);
x_146 = 1;
x_147 = l_Bool_DecidableEq(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_21);
return x_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_1);
lean_ctor_set(x_150, 1, x_21);
return x_150;
}
}
}
}
}
}
else
{
uint8_t x_151; 
x_151 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_151 == 0)
{
lean_object* x_152; 
lean_inc(x_7);
lean_inc(x_20);
lean_inc(x_4);
x_152 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_whnfCore___spec__5(x_4, x_20, x_7, x_21);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_23 = x_20;
x_24 = x_154;
goto block_90;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_20);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
lean_dec(x_153);
x_23 = x_156;
x_24 = x_155;
goto block_90;
}
}
else
{
uint8_t x_157; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_152);
if (x_157 == 0)
{
return x_152;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_152, 0);
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_152);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_22);
x_161 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_20);
lean_dec(x_20);
lean_inc(x_4);
x_162 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_4, x_161);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; uint8_t x_164; uint8_t x_165; 
lean_dec(x_161);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_163 = lean_expr_eqv(x_2, x_3);
x_164 = 1;
x_165 = l_Bool_DecidableEq(x_163, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_21);
return x_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_21);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_169 = lean_ctor_get(x_162, 0);
lean_inc(x_169);
lean_dec(x_162);
x_170 = lean_unsigned_to_nat(0u);
x_171 = l_Lean_Expr_getAppNumArgsAux___main(x_161, x_170);
x_172 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_171);
x_173 = lean_mk_array(x_171, x_172);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_sub(x_171, x_174);
lean_dec(x_171);
x_176 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_161, x_173, x_175);
x_177 = l_List_lengthAux___main___rarg(x_5, x_170);
x_178 = lean_ctor_get(x_4, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = l_List_lengthAux___main___rarg(x_179, x_170);
x_181 = lean_nat_dec_eq(x_177, x_180);
lean_dec(x_180);
lean_dec(x_177);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = l_String_Iterator_extract___closed__1;
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_1);
x_183 = lean_ctor_get(x_169, 2);
lean_inc(x_183);
x_184 = lean_instantiate_lparams(x_183, x_179, x_5);
x_185 = lean_ctor_get(x_4, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_4, 4);
lean_inc(x_186);
x_187 = lean_nat_add(x_185, x_186);
lean_dec(x_186);
lean_dec(x_185);
x_188 = lean_ctor_get(x_4, 5);
lean_inc(x_188);
lean_dec(x_4);
x_189 = lean_nat_add(x_187, x_188);
lean_dec(x_188);
lean_dec(x_187);
x_190 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_189, x_6, x_170, x_184);
lean_dec(x_189);
x_191 = lean_array_get_size(x_176);
x_192 = lean_ctor_get(x_169, 1);
lean_inc(x_192);
lean_dec(x_169);
x_193 = lean_nat_sub(x_191, x_192);
lean_dec(x_192);
x_194 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_191, x_176, x_193, x_190);
lean_dec(x_176);
lean_dec(x_191);
x_195 = lean_nat_add(x_9, x_174);
lean_dec(x_9);
x_196 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_10, x_6, x_195, x_194);
lean_dec(x_10);
x_197 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_196, x_7, x_21);
return x_197;
}
else
{
uint8_t x_198; uint8_t x_199; uint8_t x_200; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_169);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_198 = lean_expr_eqv(x_2, x_3);
x_199 = 1;
x_200 = l_Bool_DecidableEq(x_198, x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_21);
return x_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_21);
return x_203;
}
}
}
else
{
uint8_t x_204; uint8_t x_205; uint8_t x_206; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_169);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_204 = lean_expr_eqv(x_2, x_3);
x_205 = 1;
x_206 = l_Bool_DecidableEq(x_204, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = l_Lean_Expr_updateFn___main(x_1, x_3);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_21);
return x_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_1);
lean_ctor_set(x_209, 1, x_21);
return x_209;
}
}
}
}
}
block_90:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_23);
lean_dec(x_23);
lean_inc(x_4);
x_26 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_4, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; uint8_t x_28; uint8_t x_29; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_27 = lean_expr_eqv(x_2, x_3);
x_28 = 1;
x_29 = l_Bool_DecidableEq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_22)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_22;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
else
{
lean_object* x_32; 
if (lean_is_scalar(x_22)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_22;
}
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Expr_getAppNumArgsAux___main(x_25, x_34);
x_36 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_35);
x_37 = lean_mk_array(x_35, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_35, x_38);
lean_dec(x_35);
x_40 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_25, x_37, x_39);
x_41 = l_List_lengthAux___main___rarg(x_5, x_34);
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_List_lengthAux___main___rarg(x_43, x_34);
x_45 = lean_nat_dec_eq(x_41, x_44);
lean_dec(x_44);
lean_dec(x_41);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_String_Iterator_extract___closed__1;
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_22);
lean_dec(x_1);
x_47 = lean_ctor_get(x_33, 2);
lean_inc(x_47);
x_48 = lean_instantiate_lparams(x_47, x_43, x_5);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 4);
lean_inc(x_50);
x_51 = lean_nat_add(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
x_52 = lean_ctor_get(x_4, 5);
lean_inc(x_52);
lean_dec(x_4);
x_53 = lean_nat_add(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
x_54 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_53, x_6, x_34, x_48);
lean_dec(x_53);
x_55 = lean_array_get_size(x_40);
x_56 = lean_ctor_get(x_33, 1);
lean_inc(x_56);
lean_dec(x_33);
x_57 = lean_nat_sub(x_55, x_56);
lean_dec(x_56);
x_58 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_55, x_40, x_57, x_54);
lean_dec(x_40);
lean_dec(x_55);
x_59 = lean_nat_add(x_9, x_38);
lean_dec(x_9);
x_60 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_10, x_6, x_59, x_58);
lean_dec(x_10);
x_61 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_60, x_7, x_24);
return x_61;
}
else
{
uint8_t x_62; uint8_t x_63; uint8_t x_64; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_62 = lean_expr_eqv(x_2, x_3);
x_63 = 1;
x_64 = l_Bool_DecidableEq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_22)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_22;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_24);
return x_66;
}
else
{
lean_object* x_67; 
if (lean_is_scalar(x_22)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_22;
}
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_24);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_22);
lean_dec(x_1);
x_69 = lean_ctor_get(x_33, 2);
lean_inc(x_69);
x_70 = lean_instantiate_lparams(x_69, x_43, x_5);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 4);
lean_inc(x_72);
x_73 = lean_nat_add(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
x_74 = lean_ctor_get(x_4, 5);
lean_inc(x_74);
lean_dec(x_4);
x_75 = lean_nat_add(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
x_76 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_75, x_6, x_34, x_70);
lean_dec(x_75);
x_77 = lean_array_get_size(x_40);
x_78 = lean_ctor_get(x_33, 1);
lean_inc(x_78);
lean_dec(x_33);
x_79 = lean_nat_sub(x_77, x_78);
lean_dec(x_78);
x_80 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_77, x_40, x_79, x_76);
lean_dec(x_40);
lean_dec(x_77);
x_81 = lean_nat_add(x_9, x_38);
lean_dec(x_9);
x_82 = l___private_Init_Lean_Expr_2__mkAppRangeAux___main(x_10, x_6, x_81, x_80);
lean_dec(x_10);
x_83 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_82, x_7, x_24);
return x_83;
}
else
{
uint8_t x_84; uint8_t x_85; uint8_t x_86; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_84 = lean_expr_eqv(x_2, x_3);
x_85 = 1;
x_86 = l_Bool_DecidableEq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = l_Lean_Expr_updateFn___main(x_1, x_3);
if (lean_is_scalar(x_22)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_22;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_24);
return x_88;
}
else
{
lean_object* x_89; 
if (lean_is_scalar(x_22)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_22;
}
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_24);
return x_89;
}
}
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_19);
if (x_210 == 0)
{
return x_19;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_19, 0);
x_212 = lean_ctor_get(x_19, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_19);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_LocalDecl_value_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_4(x_8, lean_box(0), x_2, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8(x_1, x_10, x_4, x_5);
return x_11;
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_4(x_7, lean_box(0), x_2, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8(x_1, x_9, x_4, x_5);
return x_10;
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_10 = l_Lean_Expr_Inhabited;
x_11 = l_monadInhabited___rarg(x_1, x_10);
x_12 = l_unreachable_x21___rarg(x_11);
x_13 = lean_apply_2(x_12, x_3, x_4);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__1___boxed), 5, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
x_18 = lean_apply_6(x_15, lean_box(0), lean_box(0), x_16, x_17, x_3, x_4);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment___boxed), 3, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__2), 5, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
x_23 = lean_apply_6(x_20, lean_box(0), lean_box(0), x_21, x_22, x_3, x_4);
return x_23;
}
case 4:
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = l_Lean_Expr_getAppFn___main(x_25);
lean_dec(x_25);
lean_inc(x_3);
lean_inc(x_26);
x_27 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_26, x_3, x_4);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Expr_isLambda(x_29);
x_32 = 1;
x_33 = l_Bool_DecidableEq(x_31, x_32);
if (x_33 == 0)
{
if (lean_obj_tag(x_29) == 4)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_free_object(x_27);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
x_36 = 0;
x_37 = l_Lean_Meta_getConstAux(x_34, x_36, x_3, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_35);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_42 = l_Bool_DecidableEq(x_41, x_32);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_dec(x_29);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
}
else
{
lean_object* x_44; uint8_t x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_46 = l_Bool_DecidableEq(x_45, x_32);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_29);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
lean_dec(x_38);
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_dec(x_37);
x_52 = l_Lean_ConstantInfo_name(x_50);
x_53 = l_Lean_Meta_isAuxDef_x3f(x_52, x_3, x_51);
lean_dec(x_52);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_unbox(x_55);
lean_dec(x_55);
x_58 = l_Bool_DecidableEq(x_57, x_32);
if (x_58 == 0)
{
uint8_t x_59; uint8_t x_60; 
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_3);
x_59 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_60 = l_Bool_DecidableEq(x_59, x_32);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
lean_ctor_set(x_53, 0, x_61);
return x_53;
}
else
{
lean_dec(x_29);
lean_ctor_set(x_53, 0, x_2);
return x_53;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_53);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_62);
x_64 = lean_mk_empty_array_with_capacity(x_63);
lean_dec(x_63);
lean_inc(x_2);
x_65 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_64);
x_66 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__2(x_2, x_26, x_29, x_50, x_35, x_65, x_3, x_56);
lean_dec(x_29);
lean_dec(x_26);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_70 = l_Bool_DecidableEq(x_69, x_32);
if (x_70 == 0)
{
uint8_t x_71; uint8_t x_72; 
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_3);
x_71 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_72 = l_Bool_DecidableEq(x_71, x_32);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_29);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_76);
x_78 = lean_mk_empty_array_with_capacity(x_77);
lean_dec(x_77);
lean_inc(x_2);
x_79 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_78);
x_80 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__2(x_2, x_26, x_29, x_50, x_35, x_79, x_3, x_68);
lean_dec(x_29);
lean_dec(x_26);
return x_80;
}
}
}
case 4:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_37, 1);
lean_inc(x_81);
lean_dec(x_37);
x_82 = lean_ctor_get(x_50, 0);
lean_inc(x_82);
lean_dec(x_50);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_83);
x_85 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_84);
x_86 = lean_mk_array(x_84, x_85);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_84, x_87);
lean_dec(x_84);
lean_inc(x_2);
x_89 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_86, x_88);
x_90 = l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_whnfCore___spec__3(x_2, x_26, x_29, x_82, x_35, x_89, x_3, x_81);
lean_dec(x_89);
lean_dec(x_35);
lean_dec(x_82);
lean_dec(x_29);
lean_dec(x_26);
return x_90;
}
case 7:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_91 = lean_ctor_get(x_37, 1);
lean_inc(x_91);
lean_dec(x_37);
x_92 = lean_ctor_get(x_50, 0);
lean_inc(x_92);
lean_dec(x_50);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_93);
x_95 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_94);
x_96 = lean_mk_array(x_94, x_95);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_sub(x_94, x_97);
lean_dec(x_94);
lean_inc(x_2);
x_99 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_96, x_98);
x_100 = l_Lean_WHNF_reduceRec___at_Lean_Meta_whnfCore___spec__4(x_2, x_26, x_29, x_92, x_35, x_99, x_3, x_91);
lean_dec(x_99);
lean_dec(x_29);
lean_dec(x_26);
return x_100;
}
default: 
{
uint8_t x_101; 
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_37);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_37, 0);
lean_dec(x_102);
x_103 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_104 = l_Bool_DecidableEq(x_103, x_32);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
lean_ctor_set(x_37, 0, x_105);
return x_37;
}
else
{
lean_dec(x_29);
lean_ctor_set(x_37, 0, x_2);
return x_37;
}
}
else
{
lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_37, 1);
lean_inc(x_106);
lean_dec(x_37);
x_107 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_108 = l_Bool_DecidableEq(x_107, x_32);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
return x_110;
}
else
{
lean_object* x_111; 
lean_dec(x_29);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_37);
if (x_112 == 0)
{
return x_37;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_37, 0);
x_114 = lean_ctor_get(x_37, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_37);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; uint8_t x_117; 
lean_dec(x_3);
x_116 = lean_expr_eqv(x_26, x_29);
lean_dec(x_26);
x_117 = l_Bool_DecidableEq(x_116, x_32);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = l_Lean_Expr_updateFn___main(x_2, x_29);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_118);
return x_27;
}
else
{
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_free_object(x_27);
lean_dec(x_29);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_119);
x_121 = lean_mk_empty_array_with_capacity(x_120);
lean_dec(x_120);
x_122 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_121);
x_123 = l_Lean_Expr_betaRev(x_26, x_122);
lean_dec(x_26);
x_124 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_123, x_3, x_30);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_27, 0);
x_126 = lean_ctor_get(x_27, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_27);
x_127 = l_Lean_Expr_isLambda(x_125);
x_128 = 1;
x_129 = l_Bool_DecidableEq(x_127, x_128);
if (x_129 == 0)
{
if (lean_obj_tag(x_125) == 4)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
x_132 = 0;
x_133 = l_Lean_Meta_getConstAux(x_130, x_132, x_3, x_126);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
lean_dec(x_131);
lean_dec(x_3);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_expr_eqv(x_26, x_125);
lean_dec(x_26);
x_138 = l_Bool_DecidableEq(x_137, x_128);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Lean_Expr_updateFn___main(x_2, x_125);
lean_dec(x_125);
if (lean_is_scalar(x_136)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_136;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_135);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_125);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_2);
lean_ctor_set(x_141, 1, x_135);
return x_141;
}
}
else
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_134, 0);
lean_inc(x_142);
lean_dec(x_134);
switch (lean_obj_tag(x_142)) {
case 1:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; 
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
lean_dec(x_133);
x_144 = l_Lean_ConstantInfo_name(x_142);
x_145 = l_Lean_Meta_isAuxDef_x3f(x_144, x_3, x_143);
lean_dec(x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_unbox(x_146);
lean_dec(x_146);
x_150 = l_Bool_DecidableEq(x_149, x_128);
if (x_150 == 0)
{
uint8_t x_151; uint8_t x_152; 
lean_dec(x_142);
lean_dec(x_131);
lean_dec(x_3);
x_151 = lean_expr_eqv(x_26, x_125);
lean_dec(x_26);
x_152 = l_Bool_DecidableEq(x_151, x_128);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Lean_Expr_updateFn___main(x_2, x_125);
lean_dec(x_125);
if (lean_is_scalar(x_148)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_148;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_147);
return x_154;
}
else
{
lean_object* x_155; 
lean_dec(x_125);
if (lean_is_scalar(x_148)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_148;
}
lean_ctor_set(x_155, 0, x_2);
lean_ctor_set(x_155, 1, x_147);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_148);
x_156 = lean_unsigned_to_nat(0u);
x_157 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_156);
x_158 = lean_mk_empty_array_with_capacity(x_157);
lean_dec(x_157);
lean_inc(x_2);
x_159 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_158);
x_160 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__2(x_2, x_26, x_125, x_142, x_131, x_159, x_3, x_147);
lean_dec(x_125);
lean_dec(x_26);
return x_160;
}
}
case 4:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_133, 1);
lean_inc(x_161);
lean_dec(x_133);
x_162 = lean_ctor_get(x_142, 0);
lean_inc(x_162);
lean_dec(x_142);
x_163 = lean_unsigned_to_nat(0u);
x_164 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_163);
x_165 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_164);
x_166 = lean_mk_array(x_164, x_165);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_sub(x_164, x_167);
lean_dec(x_164);
lean_inc(x_2);
x_169 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_166, x_168);
x_170 = l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_whnfCore___spec__3(x_2, x_26, x_125, x_162, x_131, x_169, x_3, x_161);
lean_dec(x_169);
lean_dec(x_131);
lean_dec(x_162);
lean_dec(x_125);
lean_dec(x_26);
return x_170;
}
case 7:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_133, 1);
lean_inc(x_171);
lean_dec(x_133);
x_172 = lean_ctor_get(x_142, 0);
lean_inc(x_172);
lean_dec(x_142);
x_173 = lean_unsigned_to_nat(0u);
x_174 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_173);
x_175 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_174);
x_176 = lean_mk_array(x_174, x_175);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_sub(x_174, x_177);
lean_dec(x_174);
lean_inc(x_2);
x_179 = l___private_Init_Lean_Expr_3__getAppArgsAux___main(x_2, x_176, x_178);
x_180 = l_Lean_WHNF_reduceRec___at_Lean_Meta_whnfCore___spec__4(x_2, x_26, x_125, x_172, x_131, x_179, x_3, x_171);
lean_dec(x_179);
lean_dec(x_125);
lean_dec(x_26);
return x_180;
}
default: 
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_184; 
lean_dec(x_142);
lean_dec(x_131);
lean_dec(x_3);
x_181 = lean_ctor_get(x_133, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_182 = x_133;
} else {
 lean_dec_ref(x_133);
 x_182 = lean_box(0);
}
x_183 = lean_expr_eqv(x_26, x_125);
lean_dec(x_26);
x_184 = l_Bool_DecidableEq(x_183, x_128);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_Expr_updateFn___main(x_2, x_125);
lean_dec(x_125);
if (lean_is_scalar(x_182)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_182;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_181);
return x_186;
}
else
{
lean_object* x_187; 
lean_dec(x_125);
if (lean_is_scalar(x_182)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_182;
}
lean_ctor_set(x_187, 0, x_2);
lean_ctor_set(x_187, 1, x_181);
return x_187;
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_131);
lean_dec(x_125);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_188 = lean_ctor_get(x_133, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_133, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_190 = x_133;
} else {
 lean_dec_ref(x_133);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
uint8_t x_192; uint8_t x_193; 
lean_dec(x_3);
x_192 = lean_expr_eqv(x_26, x_125);
lean_dec(x_26);
x_193 = l_Bool_DecidableEq(x_192, x_128);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = l_Lean_Expr_updateFn___main(x_2, x_125);
lean_dec(x_125);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_126);
return x_195;
}
else
{
lean_object* x_196; 
lean_dec(x_125);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_126);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_125);
x_197 = lean_unsigned_to_nat(0u);
x_198 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_197);
x_199 = lean_mk_empty_array_with_capacity(x_198);
lean_dec(x_198);
x_200 = l___private_Init_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_199);
x_201 = l_Lean_Expr_betaRev(x_26, x_200);
lean_dec(x_26);
x_202 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_201, x_3, x_126);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_27);
if (x_203 == 0)
{
return x_27;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_27, 0);
x_205 = lean_ctor_get(x_27, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_27);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
case 8:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_1);
x_207 = lean_ctor_get(x_2, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_2, 3);
lean_inc(x_208);
lean_dec(x_2);
x_209 = lean_expr_instantiate1(x_208, x_207);
lean_dec(x_207);
lean_dec(x_208);
x_210 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_209, x_3, x_4);
return x_210;
}
case 10:
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_2, 1);
lean_inc(x_211);
lean_dec(x_2);
x_2 = x_211;
goto _start;
}
case 11:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_1);
x_213 = lean_ctor_get(x_2, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_2, 2);
lean_inc(x_214);
lean_inc(x_3);
x_215 = l_Lean_Meta_whnf(x_214, x_3, x_4);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = lean_ctor_get(x_215, 1);
x_219 = l_Lean_Expr_getAppFn___main(x_217);
if (lean_obj_tag(x_219) == 4)
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; 
lean_free_object(x_215);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec(x_219);
x_221 = 0;
x_222 = l_Lean_Meta_getConstAux(x_220, x_221, x_3, x_218);
lean_dec(x_3);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
lean_dec(x_217);
lean_dec(x_213);
x_224 = !lean_is_exclusive(x_222);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_222, 0);
lean_dec(x_225);
lean_ctor_set(x_222, 0, x_2);
return x_222;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_2);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
else
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_223, 0);
lean_inc(x_228);
lean_dec(x_223);
if (lean_obj_tag(x_228) == 6)
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_222);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_230 = lean_ctor_get(x_222, 0);
lean_dec(x_230);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_ctor_get(x_231, 3);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_nat_add(x_232, x_213);
lean_dec(x_213);
lean_dec(x_232);
x_234 = lean_unsigned_to_nat(0u);
x_235 = l_Lean_Expr_getAppNumArgsAux___main(x_217, x_234);
x_236 = lean_nat_sub(x_235, x_233);
lean_dec(x_233);
lean_dec(x_235);
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_nat_sub(x_236, x_237);
lean_dec(x_236);
x_239 = l_Lean_Expr_getRevArgD___main(x_217, x_238, x_2);
lean_dec(x_2);
lean_dec(x_217);
lean_ctor_set(x_222, 0, x_239);
return x_222;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_240 = lean_ctor_get(x_222, 1);
lean_inc(x_240);
lean_dec(x_222);
x_241 = lean_ctor_get(x_228, 0);
lean_inc(x_241);
lean_dec(x_228);
x_242 = lean_ctor_get(x_241, 3);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_nat_add(x_242, x_213);
lean_dec(x_213);
lean_dec(x_242);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_Lean_Expr_getAppNumArgsAux___main(x_217, x_244);
x_246 = lean_nat_sub(x_245, x_243);
lean_dec(x_243);
lean_dec(x_245);
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_nat_sub(x_246, x_247);
lean_dec(x_246);
x_249 = l_Lean_Expr_getRevArgD___main(x_217, x_248, x_2);
lean_dec(x_2);
lean_dec(x_217);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_240);
return x_250;
}
}
else
{
uint8_t x_251; 
lean_dec(x_228);
lean_dec(x_217);
lean_dec(x_213);
x_251 = !lean_is_exclusive(x_222);
if (x_251 == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_222, 0);
lean_dec(x_252);
lean_ctor_set(x_222, 0, x_2);
return x_222;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_222, 1);
lean_inc(x_253);
lean_dec(x_222);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_2);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_217);
lean_dec(x_213);
lean_dec(x_2);
x_255 = !lean_is_exclusive(x_222);
if (x_255 == 0)
{
return x_222;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_222, 0);
x_257 = lean_ctor_get(x_222, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_222);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_213);
lean_dec(x_3);
lean_ctor_set(x_215, 0, x_2);
return x_215;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_215, 0);
x_260 = lean_ctor_get(x_215, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_215);
x_261 = l_Lean_Expr_getAppFn___main(x_259);
if (lean_obj_tag(x_261) == 4)
{
lean_object* x_262; uint8_t x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec(x_261);
x_263 = 0;
x_264 = l_Lean_Meta_getConstAux(x_262, x_263, x_3, x_260);
lean_dec(x_3);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_259);
lean_dec(x_213);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_2);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
else
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
lean_dec(x_265);
if (lean_obj_tag(x_269) == 6)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_270 = lean_ctor_get(x_264, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_271 = x_264;
} else {
 lean_dec_ref(x_264);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_269, 0);
lean_inc(x_272);
lean_dec(x_269);
x_273 = lean_ctor_get(x_272, 3);
lean_inc(x_273);
lean_dec(x_272);
x_274 = lean_nat_add(x_273, x_213);
lean_dec(x_213);
lean_dec(x_273);
x_275 = lean_unsigned_to_nat(0u);
x_276 = l_Lean_Expr_getAppNumArgsAux___main(x_259, x_275);
x_277 = lean_nat_sub(x_276, x_274);
lean_dec(x_274);
lean_dec(x_276);
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_nat_sub(x_277, x_278);
lean_dec(x_277);
x_280 = l_Lean_Expr_getRevArgD___main(x_259, x_279, x_2);
lean_dec(x_2);
lean_dec(x_259);
if (lean_is_scalar(x_271)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_271;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_270);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_269);
lean_dec(x_259);
lean_dec(x_213);
x_282 = lean_ctor_get(x_264, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_283 = x_264;
} else {
 lean_dec_ref(x_264);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_2);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_259);
lean_dec(x_213);
lean_dec(x_2);
x_285 = lean_ctor_get(x_264, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_264, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_287 = x_264;
} else {
 lean_dec_ref(x_264);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
lean_object* x_289; 
lean_dec(x_261);
lean_dec(x_259);
lean_dec(x_213);
lean_dec(x_3);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_2);
lean_ctor_set(x_289, 1, x_260);
return x_289;
}
}
}
else
{
uint8_t x_290; 
lean_dec(x_213);
lean_dec(x_3);
lean_dec(x_2);
x_290 = !lean_is_exclusive(x_215);
if (x_290 == 0)
{
return x_215;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_215, 0);
x_292 = lean_ctor_get(x_215, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_215);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
case 12:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_2);
x_294 = l_Lean_Expr_Inhabited;
x_295 = l_monadInhabited___rarg(x_1, x_294);
x_296 = l_unreachable_x21___rarg(x_295);
x_297 = lean_apply_2(x_296, x_3, x_4);
return x_297;
}
default: 
{
lean_object* x_298; 
x_298 = lean_box(0);
x_5 = x_298;
goto block_9;
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_4(x_7, lean_box(0), x_2, x_3, x_4);
return x_8;
}
}
}
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5___closed__1;
x_5 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_whnfCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at_Lean_Meta_whnfCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_whnfCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_reduceQuotRec___at_Lean_Meta_whnfCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_whnfCore___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_WHNF_reduceRec___at_Lean_Meta_whnfCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_WHNF_reduceRec___at_Lean_Meta_whnfCore___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfCore___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5___closed__1;
x_2 = l_Lean_Expr_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_4 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_5 = l_unreachable_x21___rarg(x_4);
x_6 = lean_apply_2(x_5, x_2, x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Lean_Meta_getLocalDecl(x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_LocalDecl_value_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_13; 
lean_free_object(x_8);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_13;
x_3 = x_11;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Lean_LocalDecl_value_x3f(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_1 = x_19;
x_3 = x_16;
goto _start;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_metavar_ctx_get_expr_assignment(x_26, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_1 = x_29;
goto _start;
}
}
case 4:
{
lean_object* x_31; 
lean_inc(x_2);
x_31 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_2, x_3);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_2);
lean_inc(x_32);
x_34 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_32, x_2, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
x_1 = x_41;
x_3 = x_40;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_32);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
case 5:
{
lean_object* x_51; 
lean_inc(x_2);
x_51 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_2, x_3);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_2);
lean_inc(x_52);
x_54 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_52, x_2, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_52);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
lean_dec(x_55);
x_1 = x_61;
x_3 = x_60;
goto _start;
}
}
else
{
uint8_t x_63; 
lean_dec(x_52);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
return x_54;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_ctor_get(x_54, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_54);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_51);
if (x_67 == 0)
{
return x_51;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_51, 0);
x_69 = lean_ctor_get(x_51, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_51);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
case 8:
{
lean_object* x_71; 
lean_inc(x_2);
x_71 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_2, x_3);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_2);
lean_inc(x_72);
x_74 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_72, x_2, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_72);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
lean_dec(x_75);
x_1 = x_81;
x_3 = x_80;
goto _start;
}
}
else
{
uint8_t x_83; 
lean_dec(x_72);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_74);
if (x_83 == 0)
{
return x_74;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_74, 0);
x_85 = lean_ctor_get(x_74, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_74);
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
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_71);
if (x_87 == 0)
{
return x_71;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_71, 0);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_71);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
case 10:
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_1, 1);
lean_inc(x_91);
lean_dec(x_1);
x_1 = x_91;
goto _start;
}
case 11:
{
lean_object* x_93; 
lean_inc(x_2);
x_93 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_2, x_3);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_2);
lean_inc(x_94);
x_96 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition___spec__1(x_94, x_2, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_94);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_dec(x_96);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
lean_dec(x_97);
x_1 = x_103;
x_3 = x_102;
goto _start;
}
}
else
{
uint8_t x_105; 
lean_dec(x_94);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_96);
if (x_105 == 0)
{
return x_96;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_96, 0);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_96);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_93);
if (x_109 == 0)
{
return x_93;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_93, 0);
x_111 = lean_ctor_get(x_93, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_93);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
case 12:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_1);
x_113 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_114 = l_unreachable_x21___rarg(x_113);
x_115 = lean_apply_2(x_114, x_2, x_3);
return x_115;
}
default: 
{
lean_object* x_116; 
lean_dec(x_2);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_3);
return x_116;
}
}
}
}
lean_object* l_Lean_Meta_whnfImpl___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_whnfImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_setWHNFRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_whnfImpl), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_setWHNFRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_whnfRef;
x_3 = l_Lean_Meta_setWHNFRef___closed__1;
x_4 = lean_io_ref_set(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Init_Lean_WHNF(lean_object*);
lean_object* initialize_Init_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Init_Lean_Meta_LevelDefEq(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_WHNF(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9___closed__1 = _init_l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9___closed__1();
lean_mark_persistent(l___private_Init_Lean_WHNF_5__toCtorWhenK___at_Lean_Meta_unfoldDefinition___spec__9___closed__1);
l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5___closed__1 = _init_l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5___closed__1();
lean_mark_persistent(l_Lean_WHNF_whnfCore___main___at_Lean_Meta_unfoldDefinition___spec__5___closed__1);
l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1 = _init_l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1();
lean_mark_persistent(l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1);
l_Lean_Meta_setWHNFRef___closed__1 = _init_l_Lean_Meta_setWHNFRef___closed__1();
lean_mark_persistent(l_Lean_Meta_setWHNFRef___closed__1);
res = l_Lean_Meta_setWHNFRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
