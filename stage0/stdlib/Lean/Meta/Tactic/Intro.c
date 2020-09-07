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
lean_object* l___private_Lean_Meta_Basic_18__withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Meta_whnf___rarg(lean_object*, lean_object*);
extern lean_object* l_Id_monad;
extern lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAuxAux___main___rarg___closed__3;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__4;
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__2;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main(lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux(lean_object*);
lean_object* l_Lean_Meta_intro1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_5);
x_11 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_10, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__4;
lean_inc(x_12);
lean_inc(x_2);
x_15 = l_Lean_Meta_mkLambdaFVars___rarg(x_14, x_2, x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = lean_apply_5(x_15, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_assignExprMVar___rarg(x_14, x_3, x_17);
x_20 = lean_apply_5(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_8, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_8, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_44 = lean_array_get_size(x_5);
x_45 = lean_expr_instantiate_rev_range(x_41, x_6, x_44, x_5);
lean_dec(x_44);
lean_dec(x_41);
x_46 = l_Lean_Expr_headBeta(x_45);
x_47 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_48 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_49 = l_Lean_mkFreshId___rarg(x_47, x_48);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_50 = lean_apply_5(x_49, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_2);
lean_inc(x_4);
x_53 = lean_apply_3(x_2, x_4, x_40, x_7);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = (uint8_t)((x_43 << 24) >> 61);
lean_inc(x_51);
x_57 = lean_local_ctx_mk_local_decl(x_4, x_51, x_54, x_46, x_56);
x_58 = l_Lean_mkFVar(x_51);
x_59 = lean_array_push(x_5, x_58);
x_3 = x_17;
x_4 = x_57;
x_5 = x_59;
x_7 = x_55;
x_8 = x_42;
x_13 = x_52;
goto _start;
}
else
{
uint8_t x_61; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_50);
if (x_61 == 0)
{
return x_50;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_50, 0);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_50);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
case 8:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_8, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_8, 3);
lean_inc(x_68);
lean_dec(x_8);
x_69 = lean_array_get_size(x_5);
x_70 = lean_expr_instantiate_rev_range(x_66, x_6, x_69, x_5);
lean_dec(x_66);
x_71 = l_Lean_Expr_headBeta(x_70);
x_72 = lean_expr_instantiate_rev_range(x_67, x_6, x_69, x_5);
lean_dec(x_69);
lean_dec(x_67);
x_73 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_74 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_75 = l_Lean_mkFreshId___rarg(x_73, x_74);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_76 = lean_apply_5(x_75, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_2);
lean_inc(x_4);
x_79 = lean_apply_3(x_2, x_4, x_65, x_7);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = 0;
lean_inc(x_77);
x_83 = lean_local_ctx_mk_let_decl(x_4, x_77, x_80, x_71, x_72, x_82);
x_84 = l_Lean_mkFVar(x_77);
x_85 = lean_array_push(x_5, x_84);
x_3 = x_17;
x_4 = x_83;
x_5 = x_85;
x_7 = x_81;
x_8 = x_68;
x_13 = x_78;
goto _start;
}
else
{
uint8_t x_87; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_76);
if (x_87 == 0)
{
return x_76;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_76, 0);
x_89 = lean_ctor_get(x_76, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_76);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
default: 
{
lean_object* x_91; 
x_91 = lean_box(0);
x_18 = x_91;
goto block_39;
}
}
block_39:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_18);
x_19 = lean_array_get_size(x_5);
x_20 = lean_expr_instantiate_rev_range(x_8, x_6, x_19, x_5);
lean_dec(x_8);
x_21 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__4;
x_22 = l_Lean_Meta_whnf___rarg(x_21, x_20);
lean_inc(x_5);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_19);
lean_closure_set(x_23, 6, x_7);
x_24 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__2;
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, lean_box(0));
lean_closure_set(x_25, 2, lean_box(0));
lean_closure_set(x_25, 3, x_22);
lean_closure_set(x_25, 4, x_23);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_9, 1);
lean_dec(x_27);
lean_ctor_set(x_9, 1, x_4);
x_28 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_29 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_30 = l_Lean_Meta_withNewLocalInstances___rarg(x_28, x_29, lean_box(0), x_5, x_6, x_25);
x_31 = lean_apply_5(x_30, x_9, x_10, x_11, x_12, x_13);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_4);
lean_ctor_set(x_34, 2, x_33);
x_35 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_36 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_37 = l_Lean_Meta_withNewLocalInstances___rarg(x_35, x_36, lean_box(0), x_5, x_6, x_25);
x_38 = lean_apply_5(x_37, x_34, x_10, x_11, x_12, x_13);
return x_38;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_array_get_size(x_5);
x_93 = lean_expr_instantiate_rev_range(x_8, x_6, x_92, x_5);
lean_dec(x_92);
lean_dec(x_8);
lean_inc(x_1);
x_94 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_94, 0, x_1);
lean_inc(x_5);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__2), 9, 3);
lean_closure_set(x_95, 0, x_93);
lean_closure_set(x_95, 1, x_5);
lean_closure_set(x_95, 2, x_1);
x_96 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__2;
x_97 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_97, 0, x_96);
lean_closure_set(x_97, 1, lean_box(0));
lean_closure_set(x_97, 2, lean_box(0));
lean_closure_set(x_97, 3, x_94);
lean_closure_set(x_97, 4, x_95);
x_98 = !lean_is_exclusive(x_9);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_9, 1);
lean_dec(x_99);
lean_ctor_set(x_9, 1, x_4);
x_100 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_101 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_102 = l_Lean_Meta_withNewLocalInstances___rarg(x_100, x_101, lean_box(0), x_5, x_6, x_97);
x_103 = lean_apply_5(x_102, x_9, x_10, x_11, x_12, x_13);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_9, 0);
x_105 = lean_ctor_get(x_9, 2);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_9);
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_4);
lean_ctor_set(x_106, 2, x_105);
x_107 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_108 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_109 = l_Lean_Meta_withNewLocalInstances___rarg(x_107, x_108, lean_box(0), x_5, x_6, x_97);
x_110 = lean_apply_5(x_109, x_106, x_10, x_11, x_12, x_13);
return x_110;
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
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_13 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__2;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, lean_box(0));
lean_closure_set(x_14, 3, x_11);
lean_closure_set(x_14, 4, x_12);
x_15 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_16 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_17 = l_Lean_Meta_withMVarContext___rarg(x_15, x_16, lean_box(0), x_1, x_14);
x_18 = lean_apply_5(x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
lean_object* l_Lean_Meta_introNCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___rarg), 9, 0);
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
lean_object* l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_18__withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_3, x_1, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_5);
x_11 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_10, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_2);
x_14 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_2, x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_3, x_15, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_37 = lean_array_get_size(x_5);
x_38 = lean_expr_instantiate_rev_range(x_34, x_6, x_37, x_5);
lean_dec(x_37);
lean_dec(x_34);
x_39 = l_Lean_Expr_headBeta(x_38);
x_40 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_12, x_13);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_4);
x_43 = l_Lean_Meta_mkAuxName(x_1, x_4, x_33, x_7);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = (uint8_t)((x_36 << 24) >> 61);
lean_inc(x_41);
x_47 = lean_local_ctx_mk_local_decl(x_4, x_41, x_44, x_39, x_46);
x_48 = l_Lean_mkFVar(x_41);
x_49 = lean_array_push(x_5, x_48);
x_3 = x_17;
x_4 = x_47;
x_5 = x_49;
x_7 = x_45;
x_8 = x_35;
x_13 = x_42;
goto _start;
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_8, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_8, 3);
lean_inc(x_54);
lean_dec(x_8);
x_55 = lean_array_get_size(x_5);
x_56 = lean_expr_instantiate_rev_range(x_52, x_6, x_55, x_5);
lean_dec(x_52);
x_57 = l_Lean_Expr_headBeta(x_56);
x_58 = lean_expr_instantiate_rev_range(x_53, x_6, x_55, x_5);
lean_dec(x_55);
lean_dec(x_53);
x_59 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_12, x_13);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_4);
x_62 = l_Lean_Meta_mkAuxName(x_1, x_4, x_51, x_7);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = 0;
lean_inc(x_60);
x_66 = lean_local_ctx_mk_let_decl(x_4, x_60, x_63, x_57, x_58, x_65);
x_67 = l_Lean_mkFVar(x_60);
x_68 = lean_array_push(x_5, x_67);
x_3 = x_17;
x_4 = x_66;
x_5 = x_68;
x_7 = x_64;
x_8 = x_54;
x_13 = x_61;
goto _start;
}
default: 
{
lean_object* x_70; 
x_70 = lean_box(0);
x_18 = x_70;
goto block_32;
}
}
block_32:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
x_19 = lean_array_get_size(x_5);
x_20 = lean_expr_instantiate_rev_range(x_8, x_6, x_19, x_5);
lean_dec(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_box(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__1___boxed), 13, 7);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_22);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_19);
lean_closure_set(x_23, 6, x_7);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_9, 1);
lean_dec(x_26);
lean_ctor_set(x_9, 1, x_4);
x_27 = l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3___rarg(x_5, x_6, x_24, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3___rarg(x_5, x_6, x_24, x_30, x_10, x_11, x_12, x_13);
return x_31;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_7);
lean_dec(x_3);
x_71 = lean_array_get_size(x_5);
x_72 = lean_expr_instantiate_rev_range(x_8, x_6, x_71, x_5);
lean_dec(x_71);
lean_dec(x_8);
lean_inc(x_2);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_73, 0, x_2);
lean_inc(x_5);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__2___boxed), 9, 3);
lean_closure_set(x_74, 0, x_72);
lean_closure_set(x_74, 1, x_5);
lean_closure_set(x_74, 2, x_2);
x_75 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_75, 0, x_73);
lean_closure_set(x_75, 1, x_74);
x_76 = !lean_is_exclusive(x_9);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_9, 1);
lean_dec(x_77);
lean_ctor_set(x_9, 1, x_4);
x_78 = l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3___rarg(x_5, x_6, x_75, x_9, x_10, x_11, x_12, x_13);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_9, 0);
x_80 = lean_ctor_get(x_9, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_9);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_4);
lean_ctor_set(x_81, 2, x_80);
x_82 = l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introN___spec__3___rarg(x_5, x_6, x_75, x_81, x_10, x_11, x_12, x_13);
return x_82;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_23 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_16, x_22);
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
x_28 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_16, x_27);
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
x_37 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_16, x_36);
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
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_2, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
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
lean_dec(x_5);
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
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
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
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Lean_Meta_introNCore___rarg___lambda__2___closed__1 = _init_l_Lean_Meta_introNCore___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_introNCore___rarg___lambda__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
