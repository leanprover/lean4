// Lean compiler output
// Module: Lean.Meta.Tactic.Intro
// Imports: Init Lean.Meta.Tactic.Util
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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Id_monad;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
lean_object* l_Lean_Meta_introNCore(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Core_mkFreshId___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
lean_object* l_Lean_Meta_isClassExpensive_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main(lean_object*);
lean_object* l_Lean_Meta_introNCoreAux(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("introN");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("insufficient number of binders");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isForall(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_16 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Expr_headBeta(x_1);
x_11 = 2;
lean_inc(x_5);
x_12 = l_Lean_Meta_mkFreshExprMVar(x_10, x_4, x_11, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_13);
lean_inc(x_2);
x_15 = l_Lean_Meta_mkLambda(x_2, x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_assignExprMVar(x_3, x_16, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = l_Lean_Expr_mvarId_x21(x_13);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lean_Expr_mvarId_x21(x_13);
lean_dec(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isClassExpensive_x3f), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
switch (lean_obj_tag(x_8)) {
case 7:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_8, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_39 = lean_array_get_size(x_5);
x_40 = lean_expr_instantiate_rev_range(x_36, x_6, x_39, x_5);
lean_dec(x_39);
lean_dec(x_36);
x_41 = l_Lean_Expr_headBeta(x_40);
x_42 = l_Lean_Core_mkFreshId___rarg(x_12, x_13);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_2);
lean_inc(x_4);
x_45 = lean_apply_3(x_2, x_4, x_35, x_7);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = (uint8_t)((x_38 << 24) >> 61);
lean_inc(x_43);
x_49 = lean_local_ctx_mk_local_decl(x_4, x_43, x_46, x_41, x_48);
x_50 = l_Lean_mkFVar(x_43);
x_51 = lean_array_push(x_5, x_50);
x_3 = x_17;
x_4 = x_49;
x_5 = x_51;
x_7 = x_47;
x_8 = x_37;
x_13 = x_44;
goto _start;
}
case 8:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_8, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_8, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_8, 3);
lean_inc(x_56);
lean_dec(x_8);
x_57 = lean_array_get_size(x_5);
x_58 = lean_expr_instantiate_rev_range(x_54, x_6, x_57, x_5);
lean_dec(x_54);
x_59 = l_Lean_Expr_headBeta(x_58);
x_60 = lean_expr_instantiate_rev_range(x_55, x_6, x_57, x_5);
lean_dec(x_57);
lean_dec(x_55);
x_61 = l_Lean_Core_mkFreshId___rarg(x_12, x_13);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_2);
lean_inc(x_4);
x_64 = lean_apply_3(x_2, x_4, x_53, x_7);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_62);
x_67 = lean_local_ctx_mk_let_decl(x_4, x_62, x_65, x_59, x_60);
x_68 = l_Lean_mkFVar(x_62);
x_69 = lean_array_push(x_5, x_68);
x_3 = x_17;
x_4 = x_67;
x_5 = x_69;
x_7 = x_66;
x_8 = x_56;
x_13 = x_63;
goto _start;
}
default: 
{
lean_object* x_71; 
x_71 = lean_box(0);
x_18 = x_71;
goto block_34;
}
}
block_34:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
x_19 = lean_array_get_size(x_5);
x_20 = lean_expr_instantiate_rev_range(x_8, x_6, x_19, x_5);
lean_dec(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 6, 1);
lean_closure_set(x_21, 0, x_20);
lean_inc(x_5);
lean_inc(x_4);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__1), 13, 7);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_17);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_5);
lean_closure_set(x_22, 5, x_19);
lean_closure_set(x_22, 6, x_7);
x_23 = l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, lean_box(0));
lean_closure_set(x_24, 2, lean_box(0));
lean_closure_set(x_24, 3, x_21);
lean_closure_set(x_24, 4, x_22);
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 1);
lean_dec(x_26);
lean_ctor_set(x_9, 1, x_4);
x_27 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_28 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_27, x_5, x_6, x_24, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_4);
lean_ctor_set(x_31, 2, x_30);
x_32 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_33 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_32, x_5, x_6, x_24, x_31, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_33;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_array_get_size(x_5);
x_73 = lean_expr_instantiate_rev_range(x_8, x_6, x_72, x_5);
lean_dec(x_72);
lean_dec(x_8);
lean_inc(x_1);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_74, 0, x_1);
lean_inc(x_5);
x_75 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__2___boxed), 9, 3);
lean_closure_set(x_75, 0, x_73);
lean_closure_set(x_75, 1, x_5);
lean_closure_set(x_75, 2, x_1);
x_76 = l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_77 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_77, 0, x_76);
lean_closure_set(x_77, 1, lean_box(0));
lean_closure_set(x_77, 2, lean_box(0));
lean_closure_set(x_77, 3, x_74);
lean_closure_set(x_77, 4, x_75);
x_78 = !lean_is_exclusive(x_9);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_9, 1);
lean_dec(x_79);
lean_ctor_set(x_9, 1, x_4);
x_80 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_81 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_80, x_5, x_6, x_77, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_9, 0);
x_83 = lean_ctor_get(x_9, 2);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_9);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_4);
lean_ctor_set(x_84, 2, x_83);
x_85 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_86 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_85, x_5, x_6, x_77, x_84, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_86;
}
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg), 13, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Lean_Meta_introNCoreAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_introNCoreAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___rarg), 13, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_introNCore___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_introNCore___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = l_Array_empty___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_2, x_3, x_14, x_15, x_16, x_4, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = x_21;
x_23 = l_Id_monad;
x_24 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_25 = l_Array_umapMAux___main___rarg(x_23, lean_box(0), x_24, x_16, x_22);
x_26 = x_25;
lean_ctor_set(x_19, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = x_27;
x_30 = l_Id_monad;
x_31 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_32 = l_Array_umapMAux___main___rarg(x_30, lean_box(0), x_31, x_16, x_29);
x_33 = x_32;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_17, 0, x_34);
return x_17;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = x_37;
x_41 = l_Id_monad;
x_42 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_43 = l_Array_umapMAux___main___rarg(x_41, lean_box(0), x_42, x_16, x_40);
x_44 = x_43;
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_39;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_36);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
return x_17;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_17, 0);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_17);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
return x_11;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l_Lean_Meta_introNCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___rarg___lambda__2___boxed), 10, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_4);
x_13 = l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, lean_box(0));
lean_closure_set(x_14, 3, x_11);
lean_closure_set(x_14, 4, x_12);
x_15 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 4);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Meta_withLocalContext___rarg(x_18, x_19, x_14, x_5, x_6, x_7, x_8, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Meta_introNCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_introNCore___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_introNCore___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_introNCore___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_introNCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_introNCore___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
lean_object* l_Lean_Meta_mkAuxName(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (x_1 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_local_ctx_get_unused_name(x_2, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_mkThunk___closed__1;
x_11 = lean_name_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_dec(x_8);
if (x_1 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_local_ctx_get_unused_name(x_2, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
}
}
}
lean_object* l_Lean_Meta_mkAuxName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Meta_mkAuxName(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__2___boxed), 9, 3);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_1);
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_5, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg(x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_16 = lean_array_fget(x_4, x_5);
lean_inc(x_6);
x_17 = l_Lean_Meta_getFVarLocalDecl(x_16, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_type(x_18);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_20);
x_21 = l_Lean_Meta_isClassQuick_x3f___main(x_20, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_16);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_5 = x_25;
x_10 = x_23;
goto _start;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_31 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_7, x_8, x_9, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_6, 2);
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_16);
x_38 = lean_array_push(x_36, x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_30, x_39, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_restoreSynthInstanceCache(x_32, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_41);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
x_50 = l_Lean_Meta_restoreSynthInstanceCache(x_32, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
default: 
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_56 = l_Lean_Meta_isClassExpensive_x3f___main(x_20, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_16);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_5, x_59);
lean_dec(x_5);
x_5 = x_60;
x_10 = x_58;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_5, x_64);
lean_dec(x_5);
x_66 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_7, x_8, x_9, x_62);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_6, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_6, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_6, 2);
lean_inc(x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_16);
x_73 = lean_array_push(x_71, x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_73);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_75 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_65, x_74, x_7, x_8, x_9, x_68);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_restoreSynthInstanceCache(x_67, x_6, x_7, x_8, x_9, x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec(x_75);
x_85 = l_Lean_Meta_restoreSynthInstanceCache(x_67, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
lean_ctor_set_tag(x_85, 1);
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_56);
if (x_90 == 0)
{
return x_56;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_56, 0);
x_92 = lean_ctor_get(x_56, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_56);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_21);
if (x_94 == 0)
{
return x_21;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_21, 0);
x_96 = lean_ctor_get(x_21, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_21);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_17);
if (x_98 == 0)
{
return x_17;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_17, 0);
x_100 = lean_ctor_get(x_17, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_17);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isForall(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_16 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_expr_instantiate_rev_range(x_7, x_5, x_9, x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_box(x_1);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1___boxed), 13, 7);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_8);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_9);
lean_closure_set(x_20, 6, x_6);
x_21 = lean_array_get_size(x_10);
x_22 = lean_nat_dec_lt(x_11, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg(x_18, x_20, x_12, x_13, x_14, x_15, x_16);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_18);
x_24 = lean_array_fget(x_10, x_11);
lean_inc(x_12);
x_25 = l_Lean_Meta_getFVarLocalDecl(x_24, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_LocalDecl_type(x_26);
lean_dec(x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_28);
x_29 = l_Lean_Meta_isClassQuick_x3f___main(x_28, x_12, x_13, x_14, x_15, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
switch (lean_obj_tag(x_30)) {
case 0:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_24);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_11, x_32);
lean_dec(x_11);
x_11 = x_33;
x_16 = x_31;
goto _start;
}
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_11, x_37);
lean_dec(x_11);
x_39 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_13, x_14, x_15, x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_12, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_12, 2);
lean_inc(x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_24);
x_46 = lean_array_push(x_44, x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_46);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_48 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38, x_47, x_13, x_14, x_15, x_41);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_restoreSynthInstanceCache(x_40, x_12, x_13, x_14, x_15, x_50);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_dec(x_48);
x_58 = l_Lean_Meta_restoreSynthInstanceCache(x_40, x_12, x_13, x_14, x_15, x_57);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
default: 
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_29, 1);
lean_inc(x_63);
lean_dec(x_29);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_64 = l_Lean_Meta_isClassExpensive_x3f___main(x_28, x_12, x_13, x_14, x_15, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_24);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_11, x_67);
lean_dec(x_11);
x_11 = x_68;
x_16 = x_66;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_11, x_72);
lean_dec(x_11);
x_74 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_13, x_14, x_15, x_70);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_12, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_12, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_12, 2);
lean_inc(x_79);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_24);
x_81 = lean_array_push(x_79, x_80);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_81);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_83 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_73, x_82, x_13, x_14, x_15, x_76);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_restoreSynthInstanceCache(x_75, x_12, x_13, x_14, x_15, x_85);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_dec(x_83);
x_93 = l_Lean_Meta_restoreSynthInstanceCache(x_75, x_12, x_13, x_14, x_15, x_92);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
lean_ctor_set_tag(x_93, 1);
lean_ctor_set(x_93, 0, x_91);
return x_93;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_64);
if (x_98 == 0)
{
return x_64;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_64, 0);
x_100 = lean_ctor_get(x_64, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_64);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_29);
if (x_102 == 0)
{
return x_29;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_29, 0);
x_104 = lean_ctor_get(x_29, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_29);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_25);
if (x_106 == 0)
{
return x_25;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_25, 0);
x_108 = lean_ctor_get(x_25, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_25);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
switch (lean_obj_tag(x_8)) {
case 7:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 2);
lean_inc(x_30);
x_31 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_32 = lean_array_get_size(x_5);
x_33 = lean_expr_instantiate_rev_range(x_29, x_6, x_32, x_5);
lean_dec(x_32);
lean_dec(x_29);
x_34 = l_Lean_Expr_headBeta(x_33);
x_35 = l_Lean_Core_mkFreshId___rarg(x_12, x_13);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_4);
x_38 = l_Lean_Meta_mkAuxName(x_1, x_4, x_28, x_7);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = (uint8_t)((x_31 << 24) >> 61);
lean_inc(x_36);
x_42 = lean_local_ctx_mk_local_decl(x_4, x_36, x_39, x_34, x_41);
x_43 = l_Lean_mkFVar(x_36);
x_44 = lean_array_push(x_5, x_43);
x_3 = x_17;
x_4 = x_42;
x_5 = x_44;
x_7 = x_40;
x_8 = x_30;
x_13 = x_37;
goto _start;
}
case 8:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_46 = lean_ctor_get(x_8, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_8, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_8, 3);
lean_inc(x_49);
lean_dec(x_8);
x_50 = lean_array_get_size(x_5);
x_51 = lean_expr_instantiate_rev_range(x_47, x_6, x_50, x_5);
lean_dec(x_47);
x_52 = l_Lean_Expr_headBeta(x_51);
x_53 = lean_expr_instantiate_rev_range(x_48, x_6, x_50, x_5);
lean_dec(x_50);
lean_dec(x_48);
x_54 = l_Lean_Core_mkFreshId___rarg(x_12, x_13);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_4);
x_57 = l_Lean_Meta_mkAuxName(x_1, x_4, x_46, x_7);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_55);
x_60 = lean_local_ctx_mk_let_decl(x_4, x_55, x_58, x_52, x_53);
x_61 = l_Lean_mkFVar(x_55);
x_62 = lean_array_push(x_5, x_61);
x_3 = x_17;
x_4 = x_60;
x_5 = x_62;
x_7 = x_59;
x_8 = x_49;
x_13 = x_56;
goto _start;
}
default: 
{
lean_object* x_64; 
x_64 = lean_box(0);
x_18 = x_64;
goto block_27;
}
}
block_27:
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_18);
x_19 = lean_array_get_size(x_5);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_9, 1);
lean_dec(x_21);
lean_inc(x_4);
lean_ctor_set(x_9, 1, x_4);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_17, x_19, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
lean_inc(x_4);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_17, x_19, x_5, x_6, x_25, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_26;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_7);
lean_dec(x_3);
x_65 = lean_array_get_size(x_5);
x_66 = lean_expr_instantiate_rev_range(x_8, x_6, x_65, x_5);
lean_dec(x_65);
lean_dec(x_8);
x_67 = !lean_is_exclusive(x_9);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_9, 1);
lean_dec(x_68);
lean_ctor_set(x_9, 1, x_4);
lean_inc(x_5);
x_69 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_2, x_5, x_66, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_9, 0);
x_71 = lean_ctor_get(x_9, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_9);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_4);
lean_ctor_set(x_72, 2, x_71);
lean_inc(x_5);
x_73 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_2, x_5, x_66, x_5, x_6, x_72, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_73;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = l_Array_empty___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_2, x_1, x_3, x_14, x_15, x_16, x_4, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = x_21;
x_23 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_16, x_22);
x_24 = x_23;
lean_ctor_set(x_19, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = x_25;
x_28 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_16, x_27);
x_29 = x_28;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = x_33;
x_37 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_16, x_36);
x_38 = x_37;
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
return x_11;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_11, 0);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_11);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_box(x_1);
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1___boxed), 10, 4);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_getMVarDecl(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 4);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Meta_withLocalContext___rarg(x_18, x_19, x_14, x_5, x_6, x_7, x_8, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Meta_introN(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_4, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Array_empty___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
return x_18;
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_introN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_introN(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_intro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = 1;
x_12 = l_Lean_Meta_introN(x_1, x_10, x_9, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_Name_inhabited;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_16, x_18);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = l_Lean_Name_inhabited;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get(x_22, x_20, x_23);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Name_inhabited;
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get(x_31, x_28, x_32);
lean_dec(x_28);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Meta_intro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_intro(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_intro1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Meta_introN(x_1, x_9, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Name_inhabited;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_14, x_16);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = l_Lean_Name_inhabited;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_18, x_21);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
x_29 = l_Lean_Name_inhabited;
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get(x_29, x_26, x_30);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Meta_intro1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_intro1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1);
l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2);
l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3 = _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3);
l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4 = _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4);
l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5 = _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5);
l_Lean_Meta_introNCoreAux___main___rarg___closed__1 = _init_l_Lean_Meta_introNCoreAux___main___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_introNCoreAux___main___rarg___closed__1);
l_Lean_Meta_introNCore___rarg___lambda__2___closed__1 = _init_l_Lean_Meta_introNCore___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_introNCore___rarg___lambda__2___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
