// Lean compiler output
// Module: Lean.Meta.Tactic.Subst
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.Message Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__17;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__4;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__1;
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__8;
lean_object* l_Lean_Meta_subst___lambda__1___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__6;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__13;
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Meta_substCore___lambda__2___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__11;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__12;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___closed__2;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__9;
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__6;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__19;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__10;
lean_object* l_Lean_Meta_subst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__7;
lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__16;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_FVarSubst_empty;
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__5;
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__5;
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__14;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object*);
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__18;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__15;
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_Name_inhabited;
x_15 = lean_array_get(x_14, x_1, x_13);
x_16 = lean_array_get(x_14, x_2, x_13);
lean_dec(x_13);
x_17 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_15, x_16);
x_4 = x_11;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_Name_inhabited;
x_15 = lean_array_get(x_14, x_1, x_13);
x_16 = lean_array_get(x_14, x_2, x_13);
lean_dec(x_13);
x_17 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_15, x_16);
x_4 = x_11;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_Name_inhabited;
x_15 = lean_array_get(x_14, x_1, x_13);
x_16 = lean_array_get(x_14, x_2, x_13);
lean_dec(x_13);
x_17 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_15, x_16);
x_4 = x_11;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Meta_mkEqSymm(x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_replaceFVar(x_1, x_2, x_9);
lean_dec(x_9);
x_12 = lean_array_push(x_3, x_4);
x_13 = lean_array_push(x_12, x_5);
x_14 = l_Lean_Meta_mkLambda(x_13, x_11, x_6, x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_h");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_13);
lean_inc(x_1);
x_16 = l_Lean_Meta_getLocalDecl(x_1, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_275 = l_Lean_LocalDecl_type(x_17);
lean_dec(x_17);
x_276 = lean_unsigned_to_nat(3u);
x_277 = l_Lean_Expr_isAppOfArity___main(x_275, x_11, x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_275);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_278 = l_Lean_Meta_isClassQuick___main___closed__1;
x_279 = l_unreachable_x21___rarg(x_278);
x_280 = lean_apply_2(x_279, x_13, x_18);
return x_280;
}
else
{
if (x_8 == 0)
{
lean_object* x_281; 
x_281 = l_Lean_Expr_appArg_x21(x_275);
lean_dec(x_275);
x_19 = x_281;
goto block_274;
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = l_Lean_Expr_appFn_x21(x_275);
lean_dec(x_275);
x_283 = l_Lean_Expr_appArg_x21(x_282);
lean_dec(x_282);
x_19 = x_283;
goto block_274;
}
}
block_274:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_inc(x_15);
x_21 = l_Lean_MetavarContext_exprDependsOn(x_20, x_15, x_1);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
x_23 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_24 = lean_array_push(x_23, x_2);
lean_inc(x_13);
lean_inc(x_15);
x_25 = l_Lean_Meta_mkLambda(x_24, x_15, x_13, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_replaceFVar(x_15, x_2, x_19);
lean_dec(x_19);
lean_dec(x_15);
if (x_8 == 0)
{
lean_object* x_95; 
lean_inc(x_13);
x_95 = l_Lean_Meta_mkEqSymm(x_9, x_13, x_27);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_29 = x_96;
x_30 = x_97;
goto block_94;
}
else
{
uint8_t x_98; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_95);
if (x_98 == 0)
{
return x_95;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_95);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
x_29 = x_9;
x_30 = x_27;
goto block_94;
}
block_94:
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = 2;
lean_inc(x_13);
x_32 = l_Lean_Meta_mkFreshExprMVar(x_28, x_3, x_31, x_13, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_13);
lean_inc(x_33);
x_35 = l_Lean_Meta_mkEqNDRec(x_26, x_33, x_29, x_13, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
x_39 = l_Lean_Meta_assignExprMVar(x_4, x_36, x_13, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Meta_clear(x_38, x_1, x_13, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_clear(x_42, x_5, x_13, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_get_size(x_6);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_sub(x_47, x_48);
lean_dec(x_47);
x_50 = 0;
x_51 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_50, x_45, x_49, x_7, x_13, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_array_get_size(x_55);
x_57 = l_Lean_Meta_FVarSubst_empty;
lean_inc(x_56);
x_58 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_6, x_55, x_56, x_56, x_57, x_13, x_53);
lean_dec(x_13);
lean_dec(x_56);
lean_dec(x_55);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_ctor_set(x_52, 0, x_60);
lean_ctor_set(x_58, 0, x_52);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_58);
lean_ctor_set(x_52, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_52, 0);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_52);
x_66 = lean_array_get_size(x_64);
x_67 = l_Lean_Meta_FVarSubst_empty;
lean_inc(x_66);
x_68 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_6, x_64, x_66, x_66, x_67, x_13, x_53);
lean_dec(x_13);
lean_dec(x_66);
lean_dec(x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_65);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_13);
x_74 = !lean_is_exclusive(x_51);
if (x_74 == 0)
{
return x_51;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_51, 0);
x_76 = lean_ctor_get(x_51, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_51);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_13);
lean_dec(x_7);
x_78 = !lean_is_exclusive(x_44);
if (x_78 == 0)
{
return x_44;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_44, 0);
x_80 = lean_ctor_get(x_44, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_44);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_82 = !lean_is_exclusive(x_41);
if (x_82 == 0)
{
return x_41;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_41, 0);
x_84 = lean_ctor_get(x_41, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_41);
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
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_39);
if (x_86 == 0)
{
return x_39;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_39, 0);
x_88 = lean_ctor_get(x_39, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_39);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_33);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_35);
if (x_90 == 0)
{
return x_35;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_35, 0);
x_92 = lean_ctor_get(x_35, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_35);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_25);
if (x_102 == 0)
{
return x_25;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_25, 0);
x_104 = lean_ctor_get(x_25, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_25);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_inc(x_2);
x_106 = l_Lean_Expr_replaceFVar(x_15, x_2, x_19);
lean_inc(x_13);
lean_inc(x_19);
x_107 = l_Lean_Meta_mkEqRefl(x_19, x_13, x_18);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc(x_9);
x_110 = l_Lean_Expr_replaceFVar(x_106, x_9, x_108);
lean_dec(x_108);
lean_dec(x_106);
if (x_8 == 0)
{
lean_object* x_111; 
lean_inc(x_13);
lean_inc(x_2);
x_111 = l_Lean_Meta_mkEq(x_19, x_2, x_13, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_9);
x_114 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_114, 0, x_15);
lean_closure_set(x_114, 1, x_9);
lean_closure_set(x_114, 2, x_10);
lean_closure_set(x_114, 3, x_2);
x_115 = l_Lean_Meta_substCore___lambda__2___closed__2;
x_116 = 0;
lean_inc(x_13);
x_117 = l_Lean_Meta_withLocalDecl___rarg(x_115, x_112, x_116, x_114, x_13, x_113);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_13);
x_120 = l_Lean_Meta_mkEqSymm(x_9, x_13, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = 2;
lean_inc(x_13);
x_124 = l_Lean_Meta_mkFreshExprMVar(x_110, x_3, x_123, x_13, x_122);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_13);
lean_inc(x_125);
x_127 = l_Lean_Meta_mkEqRec(x_118, x_125, x_121, x_13, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_Expr_mvarId_x21(x_125);
lean_dec(x_125);
x_131 = l_Lean_Meta_assignExprMVar(x_4, x_128, x_13, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Meta_clear(x_130, x_1, x_13, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Meta_clear(x_134, x_5, x_13, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_array_get_size(x_6);
x_140 = lean_unsigned_to_nat(2u);
x_141 = lean_nat_sub(x_139, x_140);
lean_dec(x_139);
x_142 = 0;
x_143 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_142, x_137, x_141, x_7, x_13, x_138);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = !lean_is_exclusive(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_144, 0);
x_148 = lean_array_get_size(x_147);
x_149 = l_Lean_Meta_FVarSubst_empty;
lean_inc(x_148);
x_150 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(x_6, x_147, x_148, x_148, x_149, x_13, x_145);
lean_dec(x_13);
lean_dec(x_148);
lean_dec(x_147);
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_150, 0);
lean_ctor_set(x_144, 0, x_152);
lean_ctor_set(x_150, 0, x_144);
return x_150;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_150, 0);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_150);
lean_ctor_set(x_144, 0, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_156 = lean_ctor_get(x_144, 0);
x_157 = lean_ctor_get(x_144, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_144);
x_158 = lean_array_get_size(x_156);
x_159 = l_Lean_Meta_FVarSubst_empty;
lean_inc(x_158);
x_160 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(x_6, x_156, x_158, x_158, x_159, x_13, x_145);
lean_dec(x_13);
lean_dec(x_158);
lean_dec(x_156);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_157);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
}
else
{
uint8_t x_166; 
lean_dec(x_13);
x_166 = !lean_is_exclusive(x_143);
if (x_166 == 0)
{
return x_143;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_143, 0);
x_168 = lean_ctor_get(x_143, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_143);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_13);
lean_dec(x_7);
x_170 = !lean_is_exclusive(x_136);
if (x_170 == 0)
{
return x_136;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_136, 0);
x_172 = lean_ctor_get(x_136, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_136);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_174 = !lean_is_exclusive(x_133);
if (x_174 == 0)
{
return x_133;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_133, 0);
x_176 = lean_ctor_get(x_133, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_133);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_130);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_131);
if (x_178 == 0)
{
return x_131;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_131, 0);
x_180 = lean_ctor_get(x_131, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_131);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_125);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_127);
if (x_182 == 0)
{
return x_127;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_127, 0);
x_184 = lean_ctor_get(x_127, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_127);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_118);
lean_dec(x_110);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_120);
if (x_186 == 0)
{
return x_120;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_120, 0);
x_188 = lean_ctor_get(x_120, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_120);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_110);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_117);
if (x_190 == 0)
{
return x_117;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_117, 0);
x_192 = lean_ctor_get(x_117, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_117);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_110);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_111);
if (x_194 == 0)
{
return x_111;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_111, 0);
x_196 = lean_ctor_get(x_111, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_111);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_19);
x_198 = lean_array_push(x_10, x_2);
lean_inc(x_9);
x_199 = lean_array_push(x_198, x_9);
lean_inc(x_13);
x_200 = l_Lean_Meta_mkLambda(x_199, x_15, x_13, x_109);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = 2;
lean_inc(x_13);
x_204 = l_Lean_Meta_mkFreshExprMVar(x_110, x_3, x_203, x_13, x_202);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_13);
lean_inc(x_205);
x_207 = l_Lean_Meta_mkEqRec(x_201, x_205, x_9, x_13, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l_Lean_Expr_mvarId_x21(x_205);
lean_dec(x_205);
x_211 = l_Lean_Meta_assignExprMVar(x_4, x_208, x_13, x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l_Lean_Meta_clear(x_210, x_1, x_13, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = l_Lean_Meta_clear(x_214, x_5, x_13, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_array_get_size(x_6);
x_220 = lean_unsigned_to_nat(2u);
x_221 = lean_nat_sub(x_219, x_220);
lean_dec(x_219);
x_222 = 0;
x_223 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_222, x_217, x_221, x_7, x_13, x_218);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = !lean_is_exclusive(x_224);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_224, 0);
x_228 = lean_array_get_size(x_227);
x_229 = l_Lean_Meta_FVarSubst_empty;
lean_inc(x_228);
x_230 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_6, x_227, x_228, x_228, x_229, x_13, x_225);
lean_dec(x_13);
lean_dec(x_228);
lean_dec(x_227);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_230, 0);
lean_ctor_set(x_224, 0, x_232);
lean_ctor_set(x_230, 0, x_224);
return x_230;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_230, 0);
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_230);
lean_ctor_set(x_224, 0, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_224);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_236 = lean_ctor_get(x_224, 0);
x_237 = lean_ctor_get(x_224, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_224);
x_238 = lean_array_get_size(x_236);
x_239 = l_Lean_Meta_FVarSubst_empty;
lean_inc(x_238);
x_240 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_6, x_236, x_238, x_238, x_239, x_13, x_225);
lean_dec(x_13);
lean_dec(x_238);
lean_dec(x_236);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_237);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
}
else
{
uint8_t x_246; 
lean_dec(x_13);
x_246 = !lean_is_exclusive(x_223);
if (x_246 == 0)
{
return x_223;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_223, 0);
x_248 = lean_ctor_get(x_223, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_223);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_13);
lean_dec(x_7);
x_250 = !lean_is_exclusive(x_216);
if (x_250 == 0)
{
return x_216;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_216, 0);
x_252 = lean_ctor_get(x_216, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_216);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_254 = !lean_is_exclusive(x_213);
if (x_254 == 0)
{
return x_213;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_213, 0);
x_256 = lean_ctor_get(x_213, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_213);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_210);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_211);
if (x_258 == 0)
{
return x_211;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_211, 0);
x_260 = lean_ctor_get(x_211, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_211);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_205);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_207);
if (x_262 == 0)
{
return x_207;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_207, 0);
x_264 = lean_ctor_get(x_207, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_207);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_110);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_200);
if (x_266 == 0)
{
return x_200;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_200, 0);
x_268 = lean_ctor_get(x_200, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_200);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_106);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_107);
if (x_270 == 0)
{
return x_107;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_107, 0);
x_272 = lean_ctor_get(x_107, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_107);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_16);
if (x_284 == 0)
{
return x_16;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_16, 0);
x_286 = lean_ctor_get(x_16, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_16);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument must be an equality proof");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(x = t)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__11;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(t = x)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__15;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurs at");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_substCore___lambda__3___closed__2;
lean_inc(x_1);
x_8 = l_Lean_Meta_checkNotAssigned(x_1, x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_2);
x_10 = l_Lean_Meta_getLocalDecl(x_2, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_LocalDecl_type(x_11);
lean_dec(x_11);
x_14 = l_Lean_Expr_eq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity___main(x_13, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_17 = l_Lean_Meta_substCore___lambda__3___closed__5;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_17, x_5, x_12);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lean_Expr_appFn_x21(x_13);
x_20 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_21 = l_Lean_Expr_appArg_x21(x_13);
if (x_3 == 0)
{
uint8_t x_117; 
x_117 = 0;
x_22 = x_117;
goto block_116;
}
else
{
uint8_t x_118; 
x_118 = 1;
x_22 = x_118;
goto block_116;
}
block_116:
{
lean_object* x_23; 
if (x_22 == 0)
{
lean_inc(x_20);
x_23 = x_20;
goto block_115;
}
else
{
lean_inc(x_21);
x_23 = x_21;
goto block_115;
}
block_115:
{
lean_object* x_24; 
if (x_22 == 0)
{
lean_dec(x_20);
x_24 = x_21;
goto block_114;
}
else
{
lean_dec(x_21);
x_24 = x_20;
goto block_114;
}
block_114:
{
lean_object* x_25; 
lean_inc(x_5);
x_25 = l_Lean_Meta_whnf(x_23, x_5, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_13);
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_24);
x_40 = l_Lean_MetavarContext_exprDependsOn(x_39, x_24, x_38);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_dec(x_26);
lean_dec(x_24);
x_42 = x_27;
goto block_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_38);
lean_dec(x_4);
lean_dec(x_2);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_26);
x_97 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_98 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Meta_substCore___lambda__3___closed__19;
x_100 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_24);
x_102 = l_Lean_indentExpr(x_101);
x_103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_103, x_5, x_27);
lean_dec(x_5);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
return x_104;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_104);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
block_95:
{
lean_object* x_43; 
lean_inc(x_5);
lean_inc(x_38);
x_43 = l_Lean_Meta_getLocalDecl(x_38, x_5, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_mkAppStx___closed__9;
x_46 = lean_array_push(x_45, x_38);
x_47 = lean_array_push(x_46, x_2);
x_48 = 1;
x_49 = l_Lean_Meta_revert(x_1, x_47, x_48, x_5, x_44);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_box(0);
x_55 = 0;
x_56 = lean_unsigned_to_nat(2u);
x_57 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_55, x_53, x_56, x_54, x_5, x_51);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l_Lean_Name_inhabited;
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_array_get(x_62, x_60, x_63);
lean_inc(x_64);
x_65 = l_Lean_mkFVar(x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_array_get(x_62, x_60, x_66);
lean_dec(x_60);
lean_inc(x_67);
x_68 = l_Lean_mkFVar(x_67);
lean_inc(x_61);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_69, 0, x_61);
x_70 = lean_box(x_22);
lean_inc(x_61);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__2___boxed), 14, 11);
lean_closure_set(x_71, 0, x_67);
lean_closure_set(x_71, 1, x_65);
lean_closure_set(x_71, 2, x_4);
lean_closure_set(x_71, 3, x_61);
lean_closure_set(x_71, 4, x_64);
lean_closure_set(x_71, 5, x_52);
lean_closure_set(x_71, 6, x_54);
lean_closure_set(x_71, 7, x_70);
lean_closure_set(x_71, 8, x_68);
lean_closure_set(x_71, 9, x_45);
lean_closure_set(x_71, 10, x_14);
x_72 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_72, 0, x_69);
lean_closure_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_getMVarDecl(x_61, x_5, x_59);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 4);
lean_inc(x_77);
lean_dec(x_74);
x_78 = l_Lean_Meta_withLocalContext___rarg(x_76, x_77, x_72, x_5, x_75);
lean_dec(x_5);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_72);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_73);
if (x_79 == 0)
{
return x_73;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_73, 0);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_73);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_52);
lean_dec(x_5);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_57);
if (x_83 == 0)
{
return x_57;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_57, 0);
x_85 = lean_ctor_get(x_57, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_57);
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
lean_dec(x_5);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_49);
if (x_87 == 0)
{
return x_49;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_49, 0);
x_89 = lean_ctor_get(x_49, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_49);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_43);
if (x_91 == 0)
{
return x_43;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_43, 0);
x_93 = lean_ctor_get(x_43, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_43);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_2);
x_109 = lean_box(0);
x_28 = x_109;
goto block_37;
}
block_37:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_28);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_13);
x_30 = l_Lean_indentExpr(x_29);
if (x_22 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_Meta_substCore___lambda__3___closed__12;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_32, x_5, x_27);
lean_dec(x_5);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_Meta_substCore___lambda__3___closed__16;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_36 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_35, x_5, x_27);
lean_dec(x_5);
return x_36;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_25);
if (x_110 == 0)
{
return x_25;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_25, 0);
x_112 = lean_ctor_get(x_25, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_25);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_10);
if (x_119 == 0)
{
return x_10;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_10, 0);
x_121 = lean_ctor_get(x_10, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_10);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_8);
if (x_123 == 0)
{
return x_8;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_8, 0);
x_125 = lean_ctor_get(x_8, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_8);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
lean_object* l_Lean_Meta_substCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_box(x_3);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__3___boxed), 6, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 4);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Meta_withLocalContext___rarg(x_14, x_15, x_10, x_5, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lean_Meta_substCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_6);
return x_16;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_substCore___lambda__3(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_substCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_substCore(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_4, x_5);
lean_inc(x_3);
x_13 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_12, x_6, x_7);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_isAppOfArity___main(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_49; 
x_24 = l_Lean_Expr_appFn_x21(x_18);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_49 = l_Lean_Expr_isFVar(x_26);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_27 = x_50;
goto block_48;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Expr_fvarId_x21(x_26);
x_52 = lean_name_eq(x_51, x_1);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_27 = x_53;
goto block_48;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_inc(x_25);
lean_inc(x_3);
x_54 = l_Lean_MetavarContext_exprDependsOn(x_3, x_25, x_1);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_56 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_57 = 1;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_27 = x_62;
goto block_48;
}
}
}
block_48:
{
uint8_t x_28; 
lean_dec(x_27);
x_28 = l_Lean_Expr_isFVar(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_5 = x_30;
goto _start;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
x_33 = lean_name_eq(x_32, x_1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_5, x_34);
lean_dec(x_5);
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_inc(x_3);
x_37 = l_Lean_MetavarContext_exprDependsOn(x_3, x_26, x_1);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_3);
x_39 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_17)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_17;
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_17);
lean_dec(x_16);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_5, x_45);
lean_dec(x_5);
x_5 = x_46;
goto _start;
}
}
}
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_7, x_8, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_10, x_11, x_5, x_6);
return x_12;
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_isAppOfArity___main(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_49; 
x_24 = l_Lean_Expr_appFn_x21(x_18);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_49 = l_Lean_Expr_isFVar(x_26);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_27 = x_50;
goto block_48;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Expr_fvarId_x21(x_26);
x_52 = lean_name_eq(x_51, x_1);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_27 = x_53;
goto block_48;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_inc(x_25);
lean_inc(x_3);
x_54 = l_Lean_MetavarContext_exprDependsOn(x_3, x_25, x_1);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_56 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_57 = 1;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_27 = x_62;
goto block_48;
}
}
}
block_48:
{
uint8_t x_28; 
lean_dec(x_27);
x_28 = l_Lean_Expr_isFVar(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_5 = x_30;
goto _start;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
x_33 = lean_name_eq(x_32, x_1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_5, x_34);
lean_dec(x_5);
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_inc(x_3);
x_37 = l_Lean_MetavarContext_exprDependsOn(x_3, x_26, x_1);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_3);
x_39 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_17)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_17;
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_17);
lean_dec(x_16);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_5, x_45);
lean_dec(x_5);
x_5 = x_46;
goto _start;
}
}
}
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_8 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_7, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_11, x_12, x_5, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find equation for eliminating '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form (x = t) or (t = x)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_subst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_LocalDecl_type(x_3);
x_7 = l_Lean_Expr_eq_x3f___closed__2;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity___main(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
x_12 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_7, x_10, x_11, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkFVar(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_subst___lambda__1___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_substCore___lambda__3___closed__2;
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_21, x_2, x_20, x_4, x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = 0;
x_28 = lean_unbox(x_26);
lean_dec(x_26);
x_29 = l_Lean_Meta_substCore(x_2, x_25, x_28, x_27, x_4, x_24);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = l_Lean_Expr_appFn_x21(x_6);
x_42 = l_Lean_Expr_appArg_x21(x_41);
lean_dec(x_41);
x_43 = l_Lean_Expr_appArg_x21(x_6);
x_44 = l_Lean_Expr_isFVar(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Expr_isFVar(x_42);
lean_dec(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_6);
x_47 = l_Lean_indentExpr(x_46);
x_48 = l_Lean_Meta_subst___lambda__1___closed__6;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_substCore___lambda__3___closed__2;
x_51 = l_Lean_Meta_throwTacticEx___rarg(x_50, x_2, x_49, x_4, x_5);
return x_51;
}
else
{
uint8_t x_52; lean_object* x_53; 
lean_dec(x_6);
x_52 = 0;
x_53 = l_Lean_Meta_substCore(x_2, x_1, x_52, x_52, x_4, x_5);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_6);
x_65 = 1;
x_66 = 0;
x_67 = l_Lean_Meta_substCore(x_2, x_1, x_65, x_66, x_4, x_5);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_67);
if (x_75 == 0)
{
return x_67;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
}
lean_object* l_Lean_Meta_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_subst___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Meta_withLocalContext___rarg(x_11, x_12, x_7, x_3, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_subst___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_subst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_subst(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_Message(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_substCore___lambda__2___closed__1 = _init_l_Lean_Meta_substCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__1);
l_Lean_Meta_substCore___lambda__2___closed__2 = _init_l_Lean_Meta_substCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__2);
l_Lean_Meta_substCore___lambda__3___closed__1 = _init_l_Lean_Meta_substCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__1);
l_Lean_Meta_substCore___lambda__3___closed__2 = _init_l_Lean_Meta_substCore___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__2);
l_Lean_Meta_substCore___lambda__3___closed__3 = _init_l_Lean_Meta_substCore___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__3);
l_Lean_Meta_substCore___lambda__3___closed__4 = _init_l_Lean_Meta_substCore___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__4);
l_Lean_Meta_substCore___lambda__3___closed__5 = _init_l_Lean_Meta_substCore___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__5);
l_Lean_Meta_substCore___lambda__3___closed__6 = _init_l_Lean_Meta_substCore___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__6);
l_Lean_Meta_substCore___lambda__3___closed__7 = _init_l_Lean_Meta_substCore___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__7);
l_Lean_Meta_substCore___lambda__3___closed__8 = _init_l_Lean_Meta_substCore___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__8);
l_Lean_Meta_substCore___lambda__3___closed__9 = _init_l_Lean_Meta_substCore___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__9);
l_Lean_Meta_substCore___lambda__3___closed__10 = _init_l_Lean_Meta_substCore___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__10);
l_Lean_Meta_substCore___lambda__3___closed__11 = _init_l_Lean_Meta_substCore___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__11);
l_Lean_Meta_substCore___lambda__3___closed__12 = _init_l_Lean_Meta_substCore___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__12);
l_Lean_Meta_substCore___lambda__3___closed__13 = _init_l_Lean_Meta_substCore___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__13);
l_Lean_Meta_substCore___lambda__3___closed__14 = _init_l_Lean_Meta_substCore___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__14);
l_Lean_Meta_substCore___lambda__3___closed__15 = _init_l_Lean_Meta_substCore___lambda__3___closed__15();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__15);
l_Lean_Meta_substCore___lambda__3___closed__16 = _init_l_Lean_Meta_substCore___lambda__3___closed__16();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__16);
l_Lean_Meta_substCore___lambda__3___closed__17 = _init_l_Lean_Meta_substCore___lambda__3___closed__17();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__17);
l_Lean_Meta_substCore___lambda__3___closed__18 = _init_l_Lean_Meta_substCore___lambda__3___closed__18();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__18);
l_Lean_Meta_substCore___lambda__3___closed__19 = _init_l_Lean_Meta_substCore___lambda__3___closed__19();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__19);
l_Lean_Meta_subst___lambda__1___closed__1 = _init_l_Lean_Meta_subst___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__1);
l_Lean_Meta_subst___lambda__1___closed__2 = _init_l_Lean_Meta_subst___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__2);
l_Lean_Meta_subst___lambda__1___closed__3 = _init_l_Lean_Meta_subst___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__3);
l_Lean_Meta_subst___lambda__1___closed__4 = _init_l_Lean_Meta_subst___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__4);
l_Lean_Meta_subst___lambda__1___closed__5 = _init_l_Lean_Meta_subst___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__5);
l_Lean_Meta_subst___lambda__1___closed__6 = _init_l_Lean_Meta_subst___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__6);
l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1 = _init_l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1);
res = l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
