// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Intro
// Imports: Init.Lean.Meta.Tactic.Util
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
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Id_monad;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
lean_object* l_Lean_Meta_introNCore(lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
lean_object* l_Lean_Meta_introNCoreAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main(lean_object*);
lean_object* l_Lean_Meta_introNCoreAux(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isForall(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_13 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
x_14 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_13, x_9, x_10);
lean_dec(x_9);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Expr_headBeta(x_1);
x_8 = 2;
lean_inc(x_5);
x_9 = l_Lean_Meta_mkFreshExprMVar(x_7, x_4, x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_10);
lean_inc(x_2);
x_12 = l_Lean_Meta_mkLambda(x_2, x_10, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_assignExprMVar(x_3, x_13, x_5, x_14);
lean_dec(x_5);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isClassExpensive), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
switch (lean_obj_tag(x_8)) {
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_38 = lean_array_get_size(x_5);
x_39 = lean_expr_instantiate_rev_range(x_35, x_6, x_38, x_5);
lean_dec(x_38);
lean_dec(x_35);
x_40 = l_Lean_Expr_headBeta(x_39);
x_41 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_2);
lean_inc(x_4);
x_44 = lean_apply_3(x_2, x_4, x_34, x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = (uint8_t)((x_37 << 24) >> 61);
lean_inc(x_42);
x_48 = lean_local_ctx_mk_local_decl(x_4, x_42, x_45, x_40, x_47);
x_49 = l_Lean_mkFVar(x_42);
x_50 = lean_array_push(x_5, x_49);
x_3 = x_14;
x_4 = x_48;
x_5 = x_50;
x_7 = x_46;
x_8 = x_36;
x_10 = x_43;
goto _start;
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_52 = lean_ctor_get(x_8, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_8, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_8, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_8, 3);
lean_inc(x_55);
lean_dec(x_8);
x_56 = lean_array_get_size(x_5);
x_57 = lean_expr_instantiate_rev_range(x_53, x_6, x_56, x_5);
lean_dec(x_53);
x_58 = l_Lean_Expr_headBeta(x_57);
x_59 = lean_expr_instantiate_rev_range(x_54, x_6, x_56, x_5);
lean_dec(x_56);
lean_dec(x_54);
x_60 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_2);
lean_inc(x_4);
x_63 = lean_apply_3(x_2, x_4, x_52, x_7);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_61);
x_66 = lean_local_ctx_mk_let_decl(x_4, x_61, x_64, x_58, x_59);
x_67 = l_Lean_mkFVar(x_61);
x_68 = lean_array_push(x_5, x_67);
x_3 = x_14;
x_4 = x_66;
x_5 = x_68;
x_7 = x_65;
x_8 = x_55;
x_10 = x_62;
goto _start;
}
default: 
{
lean_object* x_70; 
x_70 = lean_box(0);
x_15 = x_70;
goto block_33;
}
}
block_33:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_15);
x_16 = lean_array_get_size(x_5);
x_17 = lean_expr_instantiate_rev_range(x_8, x_6, x_16, x_5);
lean_dec(x_8);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 3, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_5);
lean_inc(x_4);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__1), 10, 7);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_16);
lean_closure_set(x_19, 6, x_7);
x_20 = l_EIO_Monad___closed__1;
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, lean_box(0));
lean_closure_set(x_21, 3, x_18);
lean_closure_set(x_21, 4, x_19);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 1);
lean_dec(x_23);
lean_ctor_set(x_9, 1, x_4);
x_24 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_25 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_24, x_5, x_6, x_21, x_9, x_10);
lean_dec(x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 2);
x_28 = lean_ctor_get(x_9, 3);
x_29 = lean_ctor_get(x_9, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_29);
x_31 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_32 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_31, x_5, x_6, x_21, x_30, x_10);
lean_dec(x_5);
return x_32;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_array_get_size(x_5);
x_72 = lean_expr_instantiate_rev_range(x_8, x_6, x_71, x_5);
lean_dec(x_71);
lean_dec(x_8);
lean_inc(x_1);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 3, 1);
lean_closure_set(x_73, 0, x_1);
lean_inc(x_5);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__2), 6, 3);
lean_closure_set(x_74, 0, x_72);
lean_closure_set(x_74, 1, x_5);
lean_closure_set(x_74, 2, x_1);
x_75 = l_EIO_Monad___closed__1;
x_76 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_76, 0, x_75);
lean_closure_set(x_76, 1, lean_box(0));
lean_closure_set(x_76, 2, lean_box(0));
lean_closure_set(x_76, 3, x_73);
lean_closure_set(x_76, 4, x_74);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_9, 1);
lean_dec(x_78);
lean_ctor_set(x_9, 1, x_4);
x_79 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_80 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_79, x_5, x_6, x_76, x_9, x_10);
lean_dec(x_5);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_9, 0);
x_82 = lean_ctor_get(x_9, 2);
x_83 = lean_ctor_get(x_9, 3);
x_84 = lean_ctor_get(x_9, 4);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_9);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_4);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_84);
x_86 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_87 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_86, x_5, x_6, x_76, x_85, x_10);
lean_dec(x_5);
return x_87;
}
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_introNCoreAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_introNCoreAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___rarg), 10, 0);
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
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getMVarType(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = l_Array_empty___closed__1;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_2, x_3, x_11, x_12, x_13, x_4, x_9, x_6, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = x_18;
x_20 = l_Id_monad;
x_21 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_22 = l_Array_umapMAux___main___rarg(x_20, lean_box(0), x_21, x_13, x_19);
x_23 = x_22;
lean_ctor_set(x_16, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = x_24;
x_27 = l_Id_monad;
x_28 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_29 = l_Array_umapMAux___main___rarg(x_27, lean_box(0), x_28, x_13, x_26);
x_30 = x_29;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_14, 0, x_31);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
 x_36 = lean_box(0);
}
x_37 = x_34;
x_38 = l_Id_monad;
x_39 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_40 = l_Array_umapMAux___main___rarg(x_38, lean_box(0), x_39, x_13, x_37);
x_41 = x_40;
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Meta_introNCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___rarg___lambda__2___boxed), 7, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_4);
x_10 = l_EIO_Monad___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, lean_box(0));
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_9);
x_12 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 4);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_withLocalContext___rarg(x_15, x_16, x_11, x_5, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_introNCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___rarg___boxed), 6, 0);
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
lean_object* l_Lean_Meta_introNCore___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_introNCore___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_Meta_introNCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_introNCore___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_mkAuxName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkHole___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
x_10 = l_Lean_Meta_mkAuxName___closed__1;
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
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 3, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__2), 6, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_1);
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_8, x_9, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_array_fget(x_4, x_5);
lean_inc(x_6);
x_14 = l_Lean_Meta_getFVarLocalDecl(x_13, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_LocalDecl_type(x_15);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_17);
x_18 = l_Lean_Meta_isClassQuick___main(x_17, x_6, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
x_7 = x_20;
goto _start;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_24, 2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 2);
x_32 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_29, 2, x_32);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_6, 2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_13);
x_36 = lean_array_push(x_34, x_35);
lean_ctor_set(x_6, 2, x_36);
x_37 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_27, x_6, x_24);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_38, 2);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_39, 2);
lean_dec(x_45);
lean_ctor_set(x_39, 2, x_31);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
x_48 = lean_ctor_get(x_39, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_31);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_38, 2, x_49);
return x_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_38, 1);
x_52 = lean_ctor_get(x_38, 3);
x_53 = lean_ctor_get(x_38, 4);
x_54 = lean_ctor_get(x_38, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_38);
x_55 = lean_ctor_get(x_39, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_39, 3);
lean_inc(x_57);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_58 = x_39;
} else {
 lean_dec_ref(x_39);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 4, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_31);
lean_ctor_set(x_59, 3, x_57);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_51);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_52);
lean_ctor_set(x_60, 4, x_53);
lean_ctor_set(x_60, 5, x_54);
lean_ctor_set(x_37, 1, x_60);
return x_37;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
lean_dec(x_37);
x_62 = lean_ctor_get(x_38, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_38, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_38, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_38, 5);
lean_inc(x_66);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_67 = x_38;
} else {
 lean_dec_ref(x_38);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_39, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_39, 3);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 4, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_31);
lean_ctor_set(x_72, 3, x_70);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 6, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_64);
lean_ctor_set(x_73, 4, x_65);
lean_ctor_set(x_73, 5, x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_37, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
x_77 = !lean_is_exclusive(x_37);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_37, 1);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_75);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_75, 2);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 2);
lean_dec(x_82);
lean_ctor_set(x_76, 2, x_31);
return x_37;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
x_85 = lean_ctor_get(x_76, 3);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_31);
lean_ctor_set(x_86, 3, x_85);
lean_ctor_set(x_75, 2, x_86);
return x_37;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = lean_ctor_get(x_75, 0);
x_88 = lean_ctor_get(x_75, 1);
x_89 = lean_ctor_get(x_75, 3);
x_90 = lean_ctor_get(x_75, 4);
x_91 = lean_ctor_get(x_75, 5);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_75);
x_92 = lean_ctor_get(x_76, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_76, 3);
lean_inc(x_94);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 x_95 = x_76;
} else {
 lean_dec_ref(x_76);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 4, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_93);
lean_ctor_set(x_96, 2, x_31);
lean_ctor_set(x_96, 3, x_94);
x_97 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_89);
lean_ctor_set(x_97, 4, x_90);
lean_ctor_set(x_97, 5, x_91);
lean_ctor_set(x_37, 1, x_97);
return x_37;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_98 = lean_ctor_get(x_37, 0);
lean_inc(x_98);
lean_dec(x_37);
x_99 = lean_ctor_get(x_75, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_75, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_75, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_75, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_75, 5);
lean_inc(x_103);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_104 = x_75;
} else {
 lean_dec_ref(x_75);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_76, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_76, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_76, 3);
lean_inc(x_107);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 x_108 = x_76;
} else {
 lean_dec_ref(x_76);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 4, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_106);
lean_ctor_set(x_109, 2, x_31);
lean_ctor_set(x_109, 3, x_107);
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_104;
}
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_101);
lean_ctor_set(x_110, 4, x_102);
lean_ctor_set(x_110, 5, x_103);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_98);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_6, 0);
x_113 = lean_ctor_get(x_6, 1);
x_114 = lean_ctor_get(x_6, 2);
x_115 = lean_ctor_get(x_6, 3);
x_116 = lean_ctor_get(x_6, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_6);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_25);
lean_ctor_set(x_117, 1, x_13);
x_118 = lean_array_push(x_114, x_117);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_115);
lean_ctor_set(x_119, 4, x_116);
x_120 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_27, x_119, x_24);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_121, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_121, 5);
lean_inc(x_129);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 lean_ctor_release(x_121, 5);
 x_130 = x_121;
} else {
 lean_dec_ref(x_121);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_122, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_122, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_122, 3);
lean_inc(x_133);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 x_134 = x_122;
} else {
 lean_dec_ref(x_122);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 4, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_132);
lean_ctor_set(x_135, 2, x_31);
lean_ctor_set(x_135, 3, x_133);
if (lean_is_scalar(x_130)) {
 x_136 = lean_alloc_ctor(0, 6, 0);
} else {
 x_136 = x_130;
}
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_126);
lean_ctor_set(x_136, 2, x_135);
lean_ctor_set(x_136, 3, x_127);
lean_ctor_set(x_136, 4, x_128);
lean_ctor_set(x_136, 5, x_129);
if (lean_is_scalar(x_124)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_124;
}
lean_ctor_set(x_137, 0, x_123);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_138 = lean_ctor_get(x_120, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_120, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_141 = x_120;
} else {
 lean_dec_ref(x_120);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_138, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_138, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 lean_ctor_release(x_138, 4);
 lean_ctor_release(x_138, 5);
 x_147 = x_138;
} else {
 lean_dec_ref(x_138);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_139, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_139, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_139, 3);
lean_inc(x_150);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 lean_ctor_release(x_139, 2);
 lean_ctor_release(x_139, 3);
 x_151 = x_139;
} else {
 lean_dec_ref(x_139);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 4, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set(x_152, 2, x_31);
lean_ctor_set(x_152, 3, x_150);
if (lean_is_scalar(x_147)) {
 x_153 = lean_alloc_ctor(0, 6, 0);
} else {
 x_153 = x_147;
}
lean_ctor_set(x_153, 0, x_142);
lean_ctor_set(x_153, 1, x_143);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_144);
lean_ctor_set(x_153, 4, x_145);
lean_ctor_set(x_153, 5, x_146);
if (lean_is_scalar(x_141)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_141;
}
lean_ctor_set(x_154, 0, x_140);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_155 = lean_ctor_get(x_29, 0);
x_156 = lean_ctor_get(x_29, 1);
x_157 = lean_ctor_get(x_29, 2);
x_158 = lean_ctor_get(x_29, 3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_29);
x_159 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_160 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set(x_160, 2, x_159);
lean_ctor_set(x_160, 3, x_158);
lean_ctor_set(x_24, 2, x_160);
x_161 = lean_ctor_get(x_6, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_6, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_6, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_6, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_6, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_166 = x_6;
} else {
 lean_dec_ref(x_6);
 x_166 = lean_box(0);
}
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_25);
lean_ctor_set(x_167, 1, x_13);
x_168 = lean_array_push(x_163, x_167);
if (lean_is_scalar(x_166)) {
 x_169 = lean_alloc_ctor(0, 5, 0);
} else {
 x_169 = x_166;
}
lean_ctor_set(x_169, 0, x_161);
lean_ctor_set(x_169, 1, x_162);
lean_ctor_set(x_169, 2, x_168);
lean_ctor_set(x_169, 3, x_164);
lean_ctor_set(x_169, 4, x_165);
x_170 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_27, x_169, x_24);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_174 = x_170;
} else {
 lean_dec_ref(x_170);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_171, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_171, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_171, 4);
lean_inc(x_178);
x_179 = lean_ctor_get(x_171, 5);
lean_inc(x_179);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 lean_ctor_release(x_171, 4);
 lean_ctor_release(x_171, 5);
 x_180 = x_171;
} else {
 lean_dec_ref(x_171);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_172, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_172, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_172, 3);
lean_inc(x_183);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 x_184 = x_172;
} else {
 lean_dec_ref(x_172);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 4, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_182);
lean_ctor_set(x_185, 2, x_157);
lean_ctor_set(x_185, 3, x_183);
if (lean_is_scalar(x_180)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_180;
}
lean_ctor_set(x_186, 0, x_175);
lean_ctor_set(x_186, 1, x_176);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_177);
lean_ctor_set(x_186, 4, x_178);
lean_ctor_set(x_186, 5, x_179);
if (lean_is_scalar(x_174)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_174;
}
lean_ctor_set(x_187, 0, x_173);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_188 = lean_ctor_get(x_170, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_170, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_191 = x_170;
} else {
 lean_dec_ref(x_170);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 5);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_189, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_189, 3);
lean_inc(x_200);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 x_201 = x_189;
} else {
 lean_dec_ref(x_189);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 4, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_198);
lean_ctor_set(x_202, 1, x_199);
lean_ctor_set(x_202, 2, x_157);
lean_ctor_set(x_202, 3, x_200);
if (lean_is_scalar(x_197)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_197;
}
lean_ctor_set(x_203, 0, x_192);
lean_ctor_set(x_203, 1, x_193);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_194);
lean_ctor_set(x_203, 4, x_195);
lean_ctor_set(x_203, 5, x_196);
if (lean_is_scalar(x_191)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_191;
}
lean_ctor_set(x_204, 0, x_190);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_205 = lean_ctor_get(x_24, 2);
x_206 = lean_ctor_get(x_24, 0);
x_207 = lean_ctor_get(x_24, 1);
x_208 = lean_ctor_get(x_24, 3);
x_209 = lean_ctor_get(x_24, 4);
x_210 = lean_ctor_get(x_24, 5);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_205);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_24);
x_211 = lean_ctor_get(x_205, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_205, 2);
lean_inc(x_213);
x_214 = lean_ctor_get(x_205, 3);
lean_inc(x_214);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_215 = x_205;
} else {
 lean_dec_ref(x_205);
 x_215 = lean_box(0);
}
x_216 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(0, 4, 0);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_211);
lean_ctor_set(x_217, 1, x_212);
lean_ctor_set(x_217, 2, x_216);
lean_ctor_set(x_217, 3, x_214);
x_218 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_218, 0, x_206);
lean_ctor_set(x_218, 1, x_207);
lean_ctor_set(x_218, 2, x_217);
lean_ctor_set(x_218, 3, x_208);
lean_ctor_set(x_218, 4, x_209);
lean_ctor_set(x_218, 5, x_210);
x_219 = lean_ctor_get(x_6, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_6, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_6, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_6, 3);
lean_inc(x_222);
x_223 = lean_ctor_get(x_6, 4);
lean_inc(x_223);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_224 = x_6;
} else {
 lean_dec_ref(x_6);
 x_224 = lean_box(0);
}
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_25);
lean_ctor_set(x_225, 1, x_13);
x_226 = lean_array_push(x_221, x_225);
if (lean_is_scalar(x_224)) {
 x_227 = lean_alloc_ctor(0, 5, 0);
} else {
 x_227 = x_224;
}
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_220);
lean_ctor_set(x_227, 2, x_226);
lean_ctor_set(x_227, 3, x_222);
lean_ctor_set(x_227, 4, x_223);
x_228 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_27, x_227, x_218);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_229, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_232 = x_228;
} else {
 lean_dec_ref(x_228);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_229, 3);
lean_inc(x_235);
x_236 = lean_ctor_get(x_229, 4);
lean_inc(x_236);
x_237 = lean_ctor_get(x_229, 5);
lean_inc(x_237);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 lean_ctor_release(x_229, 2);
 lean_ctor_release(x_229, 3);
 lean_ctor_release(x_229, 4);
 lean_ctor_release(x_229, 5);
 x_238 = x_229;
} else {
 lean_dec_ref(x_229);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_230, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_230, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_230, 3);
lean_inc(x_241);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 lean_ctor_release(x_230, 2);
 lean_ctor_release(x_230, 3);
 x_242 = x_230;
} else {
 lean_dec_ref(x_230);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(0, 4, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_239);
lean_ctor_set(x_243, 1, x_240);
lean_ctor_set(x_243, 2, x_213);
lean_ctor_set(x_243, 3, x_241);
if (lean_is_scalar(x_238)) {
 x_244 = lean_alloc_ctor(0, 6, 0);
} else {
 x_244 = x_238;
}
lean_ctor_set(x_244, 0, x_233);
lean_ctor_set(x_244, 1, x_234);
lean_ctor_set(x_244, 2, x_243);
lean_ctor_set(x_244, 3, x_235);
lean_ctor_set(x_244, 4, x_236);
lean_ctor_set(x_244, 5, x_237);
if (lean_is_scalar(x_232)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_232;
}
lean_ctor_set(x_245, 0, x_231);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_246 = lean_ctor_get(x_228, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 2);
lean_inc(x_247);
x_248 = lean_ctor_get(x_228, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_249 = x_228;
} else {
 lean_dec_ref(x_228);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_246, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_246, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_246, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_246, 4);
lean_inc(x_253);
x_254 = lean_ctor_get(x_246, 5);
lean_inc(x_254);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 lean_ctor_release(x_246, 3);
 lean_ctor_release(x_246, 4);
 lean_ctor_release(x_246, 5);
 x_255 = x_246;
} else {
 lean_dec_ref(x_246);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_247, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_247, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_247, 3);
lean_inc(x_258);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_259 = x_247;
} else {
 lean_dec_ref(x_247);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 4, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_257);
lean_ctor_set(x_260, 2, x_213);
lean_ctor_set(x_260, 3, x_258);
if (lean_is_scalar(x_255)) {
 x_261 = lean_alloc_ctor(0, 6, 0);
} else {
 x_261 = x_255;
}
lean_ctor_set(x_261, 0, x_250);
lean_ctor_set(x_261, 1, x_251);
lean_ctor_set(x_261, 2, x_260);
lean_ctor_set(x_261, 3, x_252);
lean_ctor_set(x_261, 4, x_253);
lean_ctor_set(x_261, 5, x_254);
if (lean_is_scalar(x_249)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_249;
}
lean_ctor_set(x_262, 0, x_248);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
default: 
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_18, 1);
lean_inc(x_263);
lean_dec(x_18);
lean_inc(x_6);
x_264 = l_Lean_Meta_isClassExpensive___main(x_17, x_6, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_13);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_unsigned_to_nat(1u);
x_268 = lean_nat_add(x_5, x_267);
lean_dec(x_5);
x_5 = x_268;
x_7 = x_266;
goto _start;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_270 = lean_ctor_get(x_264, 1);
lean_inc(x_270);
lean_dec(x_264);
x_271 = lean_ctor_get(x_265, 0);
lean_inc(x_271);
lean_dec(x_265);
x_272 = lean_unsigned_to_nat(1u);
x_273 = lean_nat_add(x_5, x_272);
lean_dec(x_5);
x_274 = !lean_is_exclusive(x_270);
if (x_274 == 0)
{
lean_object* x_275; uint8_t x_276; 
x_275 = lean_ctor_get(x_270, 2);
x_276 = !lean_is_exclusive(x_275);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_277 = lean_ctor_get(x_275, 2);
x_278 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_275, 2, x_278);
x_279 = !lean_is_exclusive(x_6);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = lean_ctor_get(x_6, 2);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_271);
lean_ctor_set(x_281, 1, x_13);
x_282 = lean_array_push(x_280, x_281);
lean_ctor_set(x_6, 2, x_282);
x_283 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_273, x_6, x_270);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_284, 2);
lean_inc(x_285);
x_286 = !lean_is_exclusive(x_283);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; 
x_287 = lean_ctor_get(x_283, 1);
lean_dec(x_287);
x_288 = !lean_is_exclusive(x_284);
if (x_288 == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_ctor_get(x_284, 2);
lean_dec(x_289);
x_290 = !lean_is_exclusive(x_285);
if (x_290 == 0)
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_285, 2);
lean_dec(x_291);
lean_ctor_set(x_285, 2, x_277);
return x_283;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_285, 0);
x_293 = lean_ctor_get(x_285, 1);
x_294 = lean_ctor_get(x_285, 3);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_285);
x_295 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
lean_ctor_set(x_295, 2, x_277);
lean_ctor_set(x_295, 3, x_294);
lean_ctor_set(x_284, 2, x_295);
return x_283;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_296 = lean_ctor_get(x_284, 0);
x_297 = lean_ctor_get(x_284, 1);
x_298 = lean_ctor_get(x_284, 3);
x_299 = lean_ctor_get(x_284, 4);
x_300 = lean_ctor_get(x_284, 5);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_284);
x_301 = lean_ctor_get(x_285, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_285, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_285, 3);
lean_inc(x_303);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 x_304 = x_285;
} else {
 lean_dec_ref(x_285);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(0, 4, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_301);
lean_ctor_set(x_305, 1, x_302);
lean_ctor_set(x_305, 2, x_277);
lean_ctor_set(x_305, 3, x_303);
x_306 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_306, 0, x_296);
lean_ctor_set(x_306, 1, x_297);
lean_ctor_set(x_306, 2, x_305);
lean_ctor_set(x_306, 3, x_298);
lean_ctor_set(x_306, 4, x_299);
lean_ctor_set(x_306, 5, x_300);
lean_ctor_set(x_283, 1, x_306);
return x_283;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_307 = lean_ctor_get(x_283, 0);
lean_inc(x_307);
lean_dec(x_283);
x_308 = lean_ctor_get(x_284, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_284, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_284, 3);
lean_inc(x_310);
x_311 = lean_ctor_get(x_284, 4);
lean_inc(x_311);
x_312 = lean_ctor_get(x_284, 5);
lean_inc(x_312);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 lean_ctor_release(x_284, 2);
 lean_ctor_release(x_284, 3);
 lean_ctor_release(x_284, 4);
 lean_ctor_release(x_284, 5);
 x_313 = x_284;
} else {
 lean_dec_ref(x_284);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_285, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_285, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_285, 3);
lean_inc(x_316);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 x_317 = x_285;
} else {
 lean_dec_ref(x_285);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 4, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_314);
lean_ctor_set(x_318, 1, x_315);
lean_ctor_set(x_318, 2, x_277);
lean_ctor_set(x_318, 3, x_316);
if (lean_is_scalar(x_313)) {
 x_319 = lean_alloc_ctor(0, 6, 0);
} else {
 x_319 = x_313;
}
lean_ctor_set(x_319, 0, x_308);
lean_ctor_set(x_319, 1, x_309);
lean_ctor_set(x_319, 2, x_318);
lean_ctor_set(x_319, 3, x_310);
lean_ctor_set(x_319, 4, x_311);
lean_ctor_set(x_319, 5, x_312);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_307);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_283, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_321, 2);
lean_inc(x_322);
x_323 = !lean_is_exclusive(x_283);
if (x_323 == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_283, 1);
lean_dec(x_324);
x_325 = !lean_is_exclusive(x_321);
if (x_325 == 0)
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_ctor_get(x_321, 2);
lean_dec(x_326);
x_327 = !lean_is_exclusive(x_322);
if (x_327 == 0)
{
lean_object* x_328; 
x_328 = lean_ctor_get(x_322, 2);
lean_dec(x_328);
lean_ctor_set(x_322, 2, x_277);
return x_283;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_329 = lean_ctor_get(x_322, 0);
x_330 = lean_ctor_get(x_322, 1);
x_331 = lean_ctor_get(x_322, 3);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_322);
x_332 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
lean_ctor_set(x_332, 2, x_277);
lean_ctor_set(x_332, 3, x_331);
lean_ctor_set(x_321, 2, x_332);
return x_283;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_333 = lean_ctor_get(x_321, 0);
x_334 = lean_ctor_get(x_321, 1);
x_335 = lean_ctor_get(x_321, 3);
x_336 = lean_ctor_get(x_321, 4);
x_337 = lean_ctor_get(x_321, 5);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_321);
x_338 = lean_ctor_get(x_322, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_322, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_322, 3);
lean_inc(x_340);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 x_341 = x_322;
} else {
 lean_dec_ref(x_322);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 4, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_338);
lean_ctor_set(x_342, 1, x_339);
lean_ctor_set(x_342, 2, x_277);
lean_ctor_set(x_342, 3, x_340);
x_343 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_343, 0, x_333);
lean_ctor_set(x_343, 1, x_334);
lean_ctor_set(x_343, 2, x_342);
lean_ctor_set(x_343, 3, x_335);
lean_ctor_set(x_343, 4, x_336);
lean_ctor_set(x_343, 5, x_337);
lean_ctor_set(x_283, 1, x_343);
return x_283;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_344 = lean_ctor_get(x_283, 0);
lean_inc(x_344);
lean_dec(x_283);
x_345 = lean_ctor_get(x_321, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_321, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_321, 3);
lean_inc(x_347);
x_348 = lean_ctor_get(x_321, 4);
lean_inc(x_348);
x_349 = lean_ctor_get(x_321, 5);
lean_inc(x_349);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 lean_ctor_release(x_321, 5);
 x_350 = x_321;
} else {
 lean_dec_ref(x_321);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_322, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_322, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_322, 3);
lean_inc(x_353);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 x_354 = x_322;
} else {
 lean_dec_ref(x_322);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 4, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_352);
lean_ctor_set(x_355, 2, x_277);
lean_ctor_set(x_355, 3, x_353);
if (lean_is_scalar(x_350)) {
 x_356 = lean_alloc_ctor(0, 6, 0);
} else {
 x_356 = x_350;
}
lean_ctor_set(x_356, 0, x_345);
lean_ctor_set(x_356, 1, x_346);
lean_ctor_set(x_356, 2, x_355);
lean_ctor_set(x_356, 3, x_347);
lean_ctor_set(x_356, 4, x_348);
lean_ctor_set(x_356, 5, x_349);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_344);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_358 = lean_ctor_get(x_6, 0);
x_359 = lean_ctor_get(x_6, 1);
x_360 = lean_ctor_get(x_6, 2);
x_361 = lean_ctor_get(x_6, 3);
x_362 = lean_ctor_get(x_6, 4);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_6);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_271);
lean_ctor_set(x_363, 1, x_13);
x_364 = lean_array_push(x_360, x_363);
x_365 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_365, 0, x_358);
lean_ctor_set(x_365, 1, x_359);
lean_ctor_set(x_365, 2, x_364);
lean_ctor_set(x_365, 3, x_361);
lean_ctor_set(x_365, 4, x_362);
x_366 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_273, x_365, x_270);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_367, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_366, 0);
lean_inc(x_369);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_370 = x_366;
} else {
 lean_dec_ref(x_366);
 x_370 = lean_box(0);
}
x_371 = lean_ctor_get(x_367, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_367, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_367, 3);
lean_inc(x_373);
x_374 = lean_ctor_get(x_367, 4);
lean_inc(x_374);
x_375 = lean_ctor_get(x_367, 5);
lean_inc(x_375);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 lean_ctor_release(x_367, 4);
 lean_ctor_release(x_367, 5);
 x_376 = x_367;
} else {
 lean_dec_ref(x_367);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_368, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_368, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_368, 3);
lean_inc(x_379);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_380 = x_368;
} else {
 lean_dec_ref(x_368);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(0, 4, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_378);
lean_ctor_set(x_381, 2, x_277);
lean_ctor_set(x_381, 3, x_379);
if (lean_is_scalar(x_376)) {
 x_382 = lean_alloc_ctor(0, 6, 0);
} else {
 x_382 = x_376;
}
lean_ctor_set(x_382, 0, x_371);
lean_ctor_set(x_382, 1, x_372);
lean_ctor_set(x_382, 2, x_381);
lean_ctor_set(x_382, 3, x_373);
lean_ctor_set(x_382, 4, x_374);
lean_ctor_set(x_382, 5, x_375);
if (lean_is_scalar(x_370)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_370;
}
lean_ctor_set(x_383, 0, x_369);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_384 = lean_ctor_get(x_366, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_384, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_366, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_387 = x_366;
} else {
 lean_dec_ref(x_366);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_384, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_384, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_384, 3);
lean_inc(x_390);
x_391 = lean_ctor_get(x_384, 4);
lean_inc(x_391);
x_392 = lean_ctor_get(x_384, 5);
lean_inc(x_392);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 lean_ctor_release(x_384, 2);
 lean_ctor_release(x_384, 3);
 lean_ctor_release(x_384, 4);
 lean_ctor_release(x_384, 5);
 x_393 = x_384;
} else {
 lean_dec_ref(x_384);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_385, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_385, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_385, 3);
lean_inc(x_396);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 lean_ctor_release(x_385, 2);
 lean_ctor_release(x_385, 3);
 x_397 = x_385;
} else {
 lean_dec_ref(x_385);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(0, 4, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_394);
lean_ctor_set(x_398, 1, x_395);
lean_ctor_set(x_398, 2, x_277);
lean_ctor_set(x_398, 3, x_396);
if (lean_is_scalar(x_393)) {
 x_399 = lean_alloc_ctor(0, 6, 0);
} else {
 x_399 = x_393;
}
lean_ctor_set(x_399, 0, x_388);
lean_ctor_set(x_399, 1, x_389);
lean_ctor_set(x_399, 2, x_398);
lean_ctor_set(x_399, 3, x_390);
lean_ctor_set(x_399, 4, x_391);
lean_ctor_set(x_399, 5, x_392);
if (lean_is_scalar(x_387)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_387;
}
lean_ctor_set(x_400, 0, x_386);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_401 = lean_ctor_get(x_275, 0);
x_402 = lean_ctor_get(x_275, 1);
x_403 = lean_ctor_get(x_275, 2);
x_404 = lean_ctor_get(x_275, 3);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_275);
x_405 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_406 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_406, 0, x_401);
lean_ctor_set(x_406, 1, x_402);
lean_ctor_set(x_406, 2, x_405);
lean_ctor_set(x_406, 3, x_404);
lean_ctor_set(x_270, 2, x_406);
x_407 = lean_ctor_get(x_6, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_6, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_6, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_6, 3);
lean_inc(x_410);
x_411 = lean_ctor_get(x_6, 4);
lean_inc(x_411);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_412 = x_6;
} else {
 lean_dec_ref(x_6);
 x_412 = lean_box(0);
}
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_271);
lean_ctor_set(x_413, 1, x_13);
x_414 = lean_array_push(x_409, x_413);
if (lean_is_scalar(x_412)) {
 x_415 = lean_alloc_ctor(0, 5, 0);
} else {
 x_415 = x_412;
}
lean_ctor_set(x_415, 0, x_407);
lean_ctor_set(x_415, 1, x_408);
lean_ctor_set(x_415, 2, x_414);
lean_ctor_set(x_415, 3, x_410);
lean_ctor_set(x_415, 4, x_411);
x_416 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_273, x_415, x_270);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
x_418 = lean_ctor_get(x_417, 2);
lean_inc(x_418);
x_419 = lean_ctor_get(x_416, 0);
lean_inc(x_419);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_420 = x_416;
} else {
 lean_dec_ref(x_416);
 x_420 = lean_box(0);
}
x_421 = lean_ctor_get(x_417, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_417, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_417, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_417, 4);
lean_inc(x_424);
x_425 = lean_ctor_get(x_417, 5);
lean_inc(x_425);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 lean_ctor_release(x_417, 4);
 lean_ctor_release(x_417, 5);
 x_426 = x_417;
} else {
 lean_dec_ref(x_417);
 x_426 = lean_box(0);
}
x_427 = lean_ctor_get(x_418, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_418, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_418, 3);
lean_inc(x_429);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 lean_ctor_release(x_418, 3);
 x_430 = x_418;
} else {
 lean_dec_ref(x_418);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(0, 4, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_403);
lean_ctor_set(x_431, 3, x_429);
if (lean_is_scalar(x_426)) {
 x_432 = lean_alloc_ctor(0, 6, 0);
} else {
 x_432 = x_426;
}
lean_ctor_set(x_432, 0, x_421);
lean_ctor_set(x_432, 1, x_422);
lean_ctor_set(x_432, 2, x_431);
lean_ctor_set(x_432, 3, x_423);
lean_ctor_set(x_432, 4, x_424);
lean_ctor_set(x_432, 5, x_425);
if (lean_is_scalar(x_420)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_420;
}
lean_ctor_set(x_433, 0, x_419);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_434 = lean_ctor_get(x_416, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_434, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_416, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_437 = x_416;
} else {
 lean_dec_ref(x_416);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_434, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_434, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_434, 3);
lean_inc(x_440);
x_441 = lean_ctor_get(x_434, 4);
lean_inc(x_441);
x_442 = lean_ctor_get(x_434, 5);
lean_inc(x_442);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 lean_ctor_release(x_434, 2);
 lean_ctor_release(x_434, 3);
 lean_ctor_release(x_434, 4);
 lean_ctor_release(x_434, 5);
 x_443 = x_434;
} else {
 lean_dec_ref(x_434);
 x_443 = lean_box(0);
}
x_444 = lean_ctor_get(x_435, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_435, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_435, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 lean_ctor_release(x_435, 2);
 lean_ctor_release(x_435, 3);
 x_447 = x_435;
} else {
 lean_dec_ref(x_435);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(0, 4, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_444);
lean_ctor_set(x_448, 1, x_445);
lean_ctor_set(x_448, 2, x_403);
lean_ctor_set(x_448, 3, x_446);
if (lean_is_scalar(x_443)) {
 x_449 = lean_alloc_ctor(0, 6, 0);
} else {
 x_449 = x_443;
}
lean_ctor_set(x_449, 0, x_438);
lean_ctor_set(x_449, 1, x_439);
lean_ctor_set(x_449, 2, x_448);
lean_ctor_set(x_449, 3, x_440);
lean_ctor_set(x_449, 4, x_441);
lean_ctor_set(x_449, 5, x_442);
if (lean_is_scalar(x_437)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_437;
}
lean_ctor_set(x_450, 0, x_436);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_451 = lean_ctor_get(x_270, 2);
x_452 = lean_ctor_get(x_270, 0);
x_453 = lean_ctor_get(x_270, 1);
x_454 = lean_ctor_get(x_270, 3);
x_455 = lean_ctor_get(x_270, 4);
x_456 = lean_ctor_get(x_270, 5);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_451);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_270);
x_457 = lean_ctor_get(x_451, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_451, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_451, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_451, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 lean_ctor_release(x_451, 2);
 lean_ctor_release(x_451, 3);
 x_461 = x_451;
} else {
 lean_dec_ref(x_451);
 x_461 = lean_box(0);
}
x_462 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(0, 4, 0);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_457);
lean_ctor_set(x_463, 1, x_458);
lean_ctor_set(x_463, 2, x_462);
lean_ctor_set(x_463, 3, x_460);
x_464 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_464, 0, x_452);
lean_ctor_set(x_464, 1, x_453);
lean_ctor_set(x_464, 2, x_463);
lean_ctor_set(x_464, 3, x_454);
lean_ctor_set(x_464, 4, x_455);
lean_ctor_set(x_464, 5, x_456);
x_465 = lean_ctor_get(x_6, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_6, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_6, 2);
lean_inc(x_467);
x_468 = lean_ctor_get(x_6, 3);
lean_inc(x_468);
x_469 = lean_ctor_get(x_6, 4);
lean_inc(x_469);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_470 = x_6;
} else {
 lean_dec_ref(x_6);
 x_470 = lean_box(0);
}
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_271);
lean_ctor_set(x_471, 1, x_13);
x_472 = lean_array_push(x_467, x_471);
if (lean_is_scalar(x_470)) {
 x_473 = lean_alloc_ctor(0, 5, 0);
} else {
 x_473 = x_470;
}
lean_ctor_set(x_473, 0, x_465);
lean_ctor_set(x_473, 1, x_466);
lean_ctor_set(x_473, 2, x_472);
lean_ctor_set(x_473, 3, x_468);
lean_ctor_set(x_473, 4, x_469);
x_474 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_273, x_473, x_464);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_475, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_474, 0);
lean_inc(x_477);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_478 = x_474;
} else {
 lean_dec_ref(x_474);
 x_478 = lean_box(0);
}
x_479 = lean_ctor_get(x_475, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_475, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_475, 3);
lean_inc(x_481);
x_482 = lean_ctor_get(x_475, 4);
lean_inc(x_482);
x_483 = lean_ctor_get(x_475, 5);
lean_inc(x_483);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 lean_ctor_release(x_475, 4);
 lean_ctor_release(x_475, 5);
 x_484 = x_475;
} else {
 lean_dec_ref(x_475);
 x_484 = lean_box(0);
}
x_485 = lean_ctor_get(x_476, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_476, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_476, 3);
lean_inc(x_487);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_488 = x_476;
} else {
 lean_dec_ref(x_476);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 4, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_485);
lean_ctor_set(x_489, 1, x_486);
lean_ctor_set(x_489, 2, x_459);
lean_ctor_set(x_489, 3, x_487);
if (lean_is_scalar(x_484)) {
 x_490 = lean_alloc_ctor(0, 6, 0);
} else {
 x_490 = x_484;
}
lean_ctor_set(x_490, 0, x_479);
lean_ctor_set(x_490, 1, x_480);
lean_ctor_set(x_490, 2, x_489);
lean_ctor_set(x_490, 3, x_481);
lean_ctor_set(x_490, 4, x_482);
lean_ctor_set(x_490, 5, x_483);
if (lean_is_scalar(x_478)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_478;
}
lean_ctor_set(x_491, 0, x_477);
lean_ctor_set(x_491, 1, x_490);
return x_491;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_492 = lean_ctor_get(x_474, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_492, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_474, 0);
lean_inc(x_494);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_495 = x_474;
} else {
 lean_dec_ref(x_474);
 x_495 = lean_box(0);
}
x_496 = lean_ctor_get(x_492, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_492, 1);
lean_inc(x_497);
x_498 = lean_ctor_get(x_492, 3);
lean_inc(x_498);
x_499 = lean_ctor_get(x_492, 4);
lean_inc(x_499);
x_500 = lean_ctor_get(x_492, 5);
lean_inc(x_500);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 lean_ctor_release(x_492, 2);
 lean_ctor_release(x_492, 3);
 lean_ctor_release(x_492, 4);
 lean_ctor_release(x_492, 5);
 x_501 = x_492;
} else {
 lean_dec_ref(x_492);
 x_501 = lean_box(0);
}
x_502 = lean_ctor_get(x_493, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_493, 1);
lean_inc(x_503);
x_504 = lean_ctor_get(x_493, 3);
lean_inc(x_504);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 lean_ctor_release(x_493, 2);
 lean_ctor_release(x_493, 3);
 x_505 = x_493;
} else {
 lean_dec_ref(x_493);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(0, 4, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_502);
lean_ctor_set(x_506, 1, x_503);
lean_ctor_set(x_506, 2, x_459);
lean_ctor_set(x_506, 3, x_504);
if (lean_is_scalar(x_501)) {
 x_507 = lean_alloc_ctor(0, 6, 0);
} else {
 x_507 = x_501;
}
lean_ctor_set(x_507, 0, x_496);
lean_ctor_set(x_507, 1, x_497);
lean_ctor_set(x_507, 2, x_506);
lean_ctor_set(x_507, 3, x_498);
lean_ctor_set(x_507, 4, x_499);
lean_ctor_set(x_507, 5, x_500);
if (lean_is_scalar(x_495)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_495;
}
lean_ctor_set(x_508, 0, x_494);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
}
else
{
uint8_t x_509; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_509 = !lean_is_exclusive(x_264);
if (x_509 == 0)
{
return x_264;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_264, 0);
x_511 = lean_ctor_get(x_264, 1);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_264);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
return x_512;
}
}
}
}
}
else
{
uint8_t x_513; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_513 = !lean_is_exclusive(x_18);
if (x_513 == 0)
{
return x_18;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_18, 0);
x_515 = lean_ctor_get(x_18, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_18);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_517 = !lean_is_exclusive(x_14);
if (x_517 == 0)
{
return x_14;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_14, 0);
x_519 = lean_ctor_get(x_14, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_14);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isForall(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_13 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
x_14 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_13, x_9, x_10);
lean_dec(x_9);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_expr_instantiate_rev_range(x_7, x_5, x_9, x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 3, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_box(x_1);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1___boxed), 10, 7);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_8);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_9);
lean_closure_set(x_17, 6, x_6);
x_18 = lean_array_get_size(x_10);
x_19 = lean_nat_dec_lt(x_11, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_15, x_17, x_12, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
x_21 = lean_array_fget(x_10, x_11);
lean_inc(x_12);
x_22 = l_Lean_Meta_getFVarLocalDecl(x_21, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_LocalDecl_type(x_23);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_25);
x_26 = l_Lean_Meta_isClassQuick___main(x_25, x_12, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_21);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_11, x_29);
lean_dec(x_11);
x_11 = x_30;
x_13 = x_28;
goto _start;
}
case 1:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_11, x_34);
lean_dec(x_11);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_32, 2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 2);
x_40 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_37, 2, x_40);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_12, 2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_21);
x_44 = lean_array_push(x_42, x_43);
lean_ctor_set(x_12, 2, x_44);
x_45 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35, x_12, x_32);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 2);
lean_inc(x_47);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_46, 2);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_47, 2);
lean_dec(x_53);
lean_ctor_set(x_47, 2, x_39);
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
x_56 = lean_ctor_get(x_47, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_39);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_46, 2, x_57);
return x_45;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
x_60 = lean_ctor_get(x_46, 3);
x_61 = lean_ctor_get(x_46, 4);
x_62 = lean_ctor_get(x_46, 5);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_47, 3);
lean_inc(x_65);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_66 = x_47;
} else {
 lean_dec_ref(x_47);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 4, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_39);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_60);
lean_ctor_set(x_68, 4, x_61);
lean_ctor_set(x_68, 5, x_62);
lean_ctor_set(x_45, 1, x_68);
return x_45;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_45, 0);
lean_inc(x_69);
lean_dec(x_45);
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_46, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_46, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_46, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_46, 5);
lean_inc(x_74);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 lean_ctor_release(x_46, 5);
 x_75 = x_46;
} else {
 lean_dec_ref(x_46);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_47, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_47, 3);
lean_inc(x_78);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_79 = x_47;
} else {
 lean_dec_ref(x_47);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 4, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_77);
lean_ctor_set(x_80, 2, x_39);
lean_ctor_set(x_80, 3, x_78);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 6, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_70);
lean_ctor_set(x_81, 1, x_71);
lean_ctor_set(x_81, 2, x_80);
lean_ctor_set(x_81, 3, x_72);
lean_ctor_set(x_81, 4, x_73);
lean_ctor_set(x_81, 5, x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_45, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 2);
lean_inc(x_84);
x_85 = !lean_is_exclusive(x_45);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_45, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_83, 2);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_84, 2);
lean_dec(x_90);
lean_ctor_set(x_84, 2, x_39);
return x_45;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_84, 0);
x_92 = lean_ctor_get(x_84, 1);
x_93 = lean_ctor_get(x_84, 3);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_84);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_39);
lean_ctor_set(x_94, 3, x_93);
lean_ctor_set(x_83, 2, x_94);
return x_45;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_83, 0);
x_96 = lean_ctor_get(x_83, 1);
x_97 = lean_ctor_get(x_83, 3);
x_98 = lean_ctor_get(x_83, 4);
x_99 = lean_ctor_get(x_83, 5);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_83);
x_100 = lean_ctor_get(x_84, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_84, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_84, 3);
lean_inc(x_102);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 x_103 = x_84;
} else {
 lean_dec_ref(x_84);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 4, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_39);
lean_ctor_set(x_104, 3, x_102);
x_105 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_96);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_97);
lean_ctor_set(x_105, 4, x_98);
lean_ctor_set(x_105, 5, x_99);
lean_ctor_set(x_45, 1, x_105);
return x_45;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_106 = lean_ctor_get(x_45, 0);
lean_inc(x_106);
lean_dec(x_45);
x_107 = lean_ctor_get(x_83, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_83, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_83, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_83, 4);
lean_inc(x_110);
x_111 = lean_ctor_get(x_83, 5);
lean_inc(x_111);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 x_112 = x_83;
} else {
 lean_dec_ref(x_83);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_84, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_84, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_84, 3);
lean_inc(x_115);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 x_116 = x_84;
} else {
 lean_dec_ref(x_84);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 4, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_117, 2, x_39);
lean_ctor_set(x_117, 3, x_115);
if (lean_is_scalar(x_112)) {
 x_118 = lean_alloc_ctor(0, 6, 0);
} else {
 x_118 = x_112;
}
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_109);
lean_ctor_set(x_118, 4, x_110);
lean_ctor_set(x_118, 5, x_111);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_106);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_12, 0);
x_121 = lean_ctor_get(x_12, 1);
x_122 = lean_ctor_get(x_12, 2);
x_123 = lean_ctor_get(x_12, 3);
x_124 = lean_ctor_get(x_12, 4);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_12);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_33);
lean_ctor_set(x_125, 1, x_21);
x_126 = lean_array_push(x_122, x_125);
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_120);
lean_ctor_set(x_127, 1, x_121);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_123);
lean_ctor_set(x_127, 4, x_124);
x_128 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35, x_127, x_32);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_132 = x_128;
} else {
 lean_dec_ref(x_128);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 5);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_130, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_130, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_130, 3);
lean_inc(x_141);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 x_142 = x_130;
} else {
 lean_dec_ref(x_130);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 4, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_39);
lean_ctor_set(x_143, 3, x_141);
if (lean_is_scalar(x_138)) {
 x_144 = lean_alloc_ctor(0, 6, 0);
} else {
 x_144 = x_138;
}
lean_ctor_set(x_144, 0, x_133);
lean_ctor_set(x_144, 1, x_134);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_135);
lean_ctor_set(x_144, 4, x_136);
lean_ctor_set(x_144, 5, x_137);
if (lean_is_scalar(x_132)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_132;
}
lean_ctor_set(x_145, 0, x_131);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_146 = lean_ctor_get(x_128, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_146, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_128, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_149 = x_128;
} else {
 lean_dec_ref(x_128);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_146, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_146, 4);
lean_inc(x_153);
x_154 = lean_ctor_get(x_146, 5);
lean_inc(x_154);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 lean_ctor_release(x_146, 5);
 x_155 = x_146;
} else {
 lean_dec_ref(x_146);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_147, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_147, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_147, 3);
lean_inc(x_158);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 x_159 = x_147;
} else {
 lean_dec_ref(x_147);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 4, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_157);
lean_ctor_set(x_160, 2, x_39);
lean_ctor_set(x_160, 3, x_158);
if (lean_is_scalar(x_155)) {
 x_161 = lean_alloc_ctor(0, 6, 0);
} else {
 x_161 = x_155;
}
lean_ctor_set(x_161, 0, x_150);
lean_ctor_set(x_161, 1, x_151);
lean_ctor_set(x_161, 2, x_160);
lean_ctor_set(x_161, 3, x_152);
lean_ctor_set(x_161, 4, x_153);
lean_ctor_set(x_161, 5, x_154);
if (lean_is_scalar(x_149)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_149;
}
lean_ctor_set(x_162, 0, x_148);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_163 = lean_ctor_get(x_37, 0);
x_164 = lean_ctor_get(x_37, 1);
x_165 = lean_ctor_get(x_37, 2);
x_166 = lean_ctor_get(x_37, 3);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_37);
x_167 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_168 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_164);
lean_ctor_set(x_168, 2, x_167);
lean_ctor_set(x_168, 3, x_166);
lean_ctor_set(x_32, 2, x_168);
x_169 = lean_ctor_get(x_12, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_12, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_12, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_12, 3);
lean_inc(x_172);
x_173 = lean_ctor_get(x_12, 4);
lean_inc(x_173);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_174 = x_12;
} else {
 lean_dec_ref(x_12);
 x_174 = lean_box(0);
}
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_33);
lean_ctor_set(x_175, 1, x_21);
x_176 = lean_array_push(x_171, x_175);
if (lean_is_scalar(x_174)) {
 x_177 = lean_alloc_ctor(0, 5, 0);
} else {
 x_177 = x_174;
}
lean_ctor_set(x_177, 0, x_169);
lean_ctor_set(x_177, 1, x_170);
lean_ctor_set(x_177, 2, x_176);
lean_ctor_set(x_177, 3, x_172);
lean_ctor_set(x_177, 4, x_173);
x_178 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35, x_177, x_32);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_182 = x_178;
} else {
 lean_dec_ref(x_178);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_179, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_179, 4);
lean_inc(x_186);
x_187 = lean_ctor_get(x_179, 5);
lean_inc(x_187);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 lean_ctor_release(x_179, 5);
 x_188 = x_179;
} else {
 lean_dec_ref(x_179);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_180, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_180, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_180, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 x_192 = x_180;
} else {
 lean_dec_ref(x_180);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 4, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_189);
lean_ctor_set(x_193, 1, x_190);
lean_ctor_set(x_193, 2, x_165);
lean_ctor_set(x_193, 3, x_191);
if (lean_is_scalar(x_188)) {
 x_194 = lean_alloc_ctor(0, 6, 0);
} else {
 x_194 = x_188;
}
lean_ctor_set(x_194, 0, x_183);
lean_ctor_set(x_194, 1, x_184);
lean_ctor_set(x_194, 2, x_193);
lean_ctor_set(x_194, 3, x_185);
lean_ctor_set(x_194, 4, x_186);
lean_ctor_set(x_194, 5, x_187);
if (lean_is_scalar(x_182)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_182;
}
lean_ctor_set(x_195, 0, x_181);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_196 = lean_ctor_get(x_178, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_196, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_178, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_199 = x_178;
} else {
 lean_dec_ref(x_178);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_196, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_196, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_196, 4);
lean_inc(x_203);
x_204 = lean_ctor_get(x_196, 5);
lean_inc(x_204);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 lean_ctor_release(x_196, 5);
 x_205 = x_196;
} else {
 lean_dec_ref(x_196);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_197, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_197, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_197, 3);
lean_inc(x_208);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 x_209 = x_197;
} else {
 lean_dec_ref(x_197);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 4, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_206);
lean_ctor_set(x_210, 1, x_207);
lean_ctor_set(x_210, 2, x_165);
lean_ctor_set(x_210, 3, x_208);
if (lean_is_scalar(x_205)) {
 x_211 = lean_alloc_ctor(0, 6, 0);
} else {
 x_211 = x_205;
}
lean_ctor_set(x_211, 0, x_200);
lean_ctor_set(x_211, 1, x_201);
lean_ctor_set(x_211, 2, x_210);
lean_ctor_set(x_211, 3, x_202);
lean_ctor_set(x_211, 4, x_203);
lean_ctor_set(x_211, 5, x_204);
if (lean_is_scalar(x_199)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_199;
}
lean_ctor_set(x_212, 0, x_198);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_213 = lean_ctor_get(x_32, 2);
x_214 = lean_ctor_get(x_32, 0);
x_215 = lean_ctor_get(x_32, 1);
x_216 = lean_ctor_get(x_32, 3);
x_217 = lean_ctor_get(x_32, 4);
x_218 = lean_ctor_get(x_32, 5);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_213);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_32);
x_219 = lean_ctor_get(x_213, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_213, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_213, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_213, 3);
lean_inc(x_222);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 x_223 = x_213;
} else {
 lean_dec_ref(x_213);
 x_223 = lean_box(0);
}
x_224 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 4, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_219);
lean_ctor_set(x_225, 1, x_220);
lean_ctor_set(x_225, 2, x_224);
lean_ctor_set(x_225, 3, x_222);
x_226 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_226, 0, x_214);
lean_ctor_set(x_226, 1, x_215);
lean_ctor_set(x_226, 2, x_225);
lean_ctor_set(x_226, 3, x_216);
lean_ctor_set(x_226, 4, x_217);
lean_ctor_set(x_226, 5, x_218);
x_227 = lean_ctor_get(x_12, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_12, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_12, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_12, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_12, 4);
lean_inc(x_231);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_232 = x_12;
} else {
 lean_dec_ref(x_12);
 x_232 = lean_box(0);
}
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_33);
lean_ctor_set(x_233, 1, x_21);
x_234 = lean_array_push(x_229, x_233);
if (lean_is_scalar(x_232)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_232;
}
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_228);
lean_ctor_set(x_235, 2, x_234);
lean_ctor_set(x_235, 3, x_230);
lean_ctor_set(x_235, 4, x_231);
x_236 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35, x_235, x_226);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_240 = x_236;
} else {
 lean_dec_ref(x_236);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_237, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_237, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_237, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_237, 4);
lean_inc(x_244);
x_245 = lean_ctor_get(x_237, 5);
lean_inc(x_245);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 lean_ctor_release(x_237, 2);
 lean_ctor_release(x_237, 3);
 lean_ctor_release(x_237, 4);
 lean_ctor_release(x_237, 5);
 x_246 = x_237;
} else {
 lean_dec_ref(x_237);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_238, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_238, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_238, 3);
lean_inc(x_249);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 lean_ctor_release(x_238, 3);
 x_250 = x_238;
} else {
 lean_dec_ref(x_238);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 4, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_247);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set(x_251, 2, x_221);
lean_ctor_set(x_251, 3, x_249);
if (lean_is_scalar(x_246)) {
 x_252 = lean_alloc_ctor(0, 6, 0);
} else {
 x_252 = x_246;
}
lean_ctor_set(x_252, 0, x_241);
lean_ctor_set(x_252, 1, x_242);
lean_ctor_set(x_252, 2, x_251);
lean_ctor_set(x_252, 3, x_243);
lean_ctor_set(x_252, 4, x_244);
lean_ctor_set(x_252, 5, x_245);
if (lean_is_scalar(x_240)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_240;
}
lean_ctor_set(x_253, 0, x_239);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_254 = lean_ctor_get(x_236, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_254, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_236, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_257 = x_236;
} else {
 lean_dec_ref(x_236);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_254, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_254, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_254, 3);
lean_inc(x_260);
x_261 = lean_ctor_get(x_254, 4);
lean_inc(x_261);
x_262 = lean_ctor_get(x_254, 5);
lean_inc(x_262);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 lean_ctor_release(x_254, 2);
 lean_ctor_release(x_254, 3);
 lean_ctor_release(x_254, 4);
 lean_ctor_release(x_254, 5);
 x_263 = x_254;
} else {
 lean_dec_ref(x_254);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_255, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_255, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_255, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 lean_ctor_release(x_255, 3);
 x_267 = x_255;
} else {
 lean_dec_ref(x_255);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 4, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_265);
lean_ctor_set(x_268, 2, x_221);
lean_ctor_set(x_268, 3, x_266);
if (lean_is_scalar(x_263)) {
 x_269 = lean_alloc_ctor(0, 6, 0);
} else {
 x_269 = x_263;
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_268);
lean_ctor_set(x_269, 3, x_260);
lean_ctor_set(x_269, 4, x_261);
lean_ctor_set(x_269, 5, x_262);
if (lean_is_scalar(x_257)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_257;
}
lean_ctor_set(x_270, 0, x_256);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
default: 
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_26, 1);
lean_inc(x_271);
lean_dec(x_26);
lean_inc(x_12);
x_272 = l_Lean_Meta_isClassExpensive___main(x_25, x_12, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_21);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_nat_add(x_11, x_275);
lean_dec(x_11);
x_11 = x_276;
x_13 = x_274;
goto _start;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_278 = lean_ctor_get(x_272, 1);
lean_inc(x_278);
lean_dec(x_272);
x_279 = lean_ctor_get(x_273, 0);
lean_inc(x_279);
lean_dec(x_273);
x_280 = lean_unsigned_to_nat(1u);
x_281 = lean_nat_add(x_11, x_280);
lean_dec(x_11);
x_282 = !lean_is_exclusive(x_278);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_278, 2);
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_283, 2);
x_286 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_283, 2, x_286);
x_287 = !lean_is_exclusive(x_12);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_12, 2);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_279);
lean_ctor_set(x_289, 1, x_21);
x_290 = lean_array_push(x_288, x_289);
lean_ctor_set(x_12, 2, x_290);
x_291 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_281, x_12, x_278);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
x_293 = lean_ctor_get(x_292, 2);
lean_inc(x_293);
x_294 = !lean_is_exclusive(x_291);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_291, 1);
lean_dec(x_295);
x_296 = !lean_is_exclusive(x_292);
if (x_296 == 0)
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_ctor_get(x_292, 2);
lean_dec(x_297);
x_298 = !lean_is_exclusive(x_293);
if (x_298 == 0)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_293, 2);
lean_dec(x_299);
lean_ctor_set(x_293, 2, x_285);
return x_291;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_300 = lean_ctor_get(x_293, 0);
x_301 = lean_ctor_get(x_293, 1);
x_302 = lean_ctor_get(x_293, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_293);
x_303 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
lean_ctor_set(x_303, 2, x_285);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set(x_292, 2, x_303);
return x_291;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_304 = lean_ctor_get(x_292, 0);
x_305 = lean_ctor_get(x_292, 1);
x_306 = lean_ctor_get(x_292, 3);
x_307 = lean_ctor_get(x_292, 4);
x_308 = lean_ctor_get(x_292, 5);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_292);
x_309 = lean_ctor_get(x_293, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_293, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_293, 3);
lean_inc(x_311);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 lean_ctor_release(x_293, 2);
 lean_ctor_release(x_293, 3);
 x_312 = x_293;
} else {
 lean_dec_ref(x_293);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 4, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_310);
lean_ctor_set(x_313, 2, x_285);
lean_ctor_set(x_313, 3, x_311);
x_314 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_314, 0, x_304);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_313);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set(x_314, 4, x_307);
lean_ctor_set(x_314, 5, x_308);
lean_ctor_set(x_291, 1, x_314);
return x_291;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_315 = lean_ctor_get(x_291, 0);
lean_inc(x_315);
lean_dec(x_291);
x_316 = lean_ctor_get(x_292, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_292, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_292, 3);
lean_inc(x_318);
x_319 = lean_ctor_get(x_292, 4);
lean_inc(x_319);
x_320 = lean_ctor_get(x_292, 5);
lean_inc(x_320);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 lean_ctor_release(x_292, 2);
 lean_ctor_release(x_292, 3);
 lean_ctor_release(x_292, 4);
 lean_ctor_release(x_292, 5);
 x_321 = x_292;
} else {
 lean_dec_ref(x_292);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_293, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_293, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_293, 3);
lean_inc(x_324);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 lean_ctor_release(x_293, 2);
 lean_ctor_release(x_293, 3);
 x_325 = x_293;
} else {
 lean_dec_ref(x_293);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 4, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_323);
lean_ctor_set(x_326, 2, x_285);
lean_ctor_set(x_326, 3, x_324);
if (lean_is_scalar(x_321)) {
 x_327 = lean_alloc_ctor(0, 6, 0);
} else {
 x_327 = x_321;
}
lean_ctor_set(x_327, 0, x_316);
lean_ctor_set(x_327, 1, x_317);
lean_ctor_set(x_327, 2, x_326);
lean_ctor_set(x_327, 3, x_318);
lean_ctor_set(x_327, 4, x_319);
lean_ctor_set(x_327, 5, x_320);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_315);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_329 = lean_ctor_get(x_291, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_329, 2);
lean_inc(x_330);
x_331 = !lean_is_exclusive(x_291);
if (x_331 == 0)
{
lean_object* x_332; uint8_t x_333; 
x_332 = lean_ctor_get(x_291, 1);
lean_dec(x_332);
x_333 = !lean_is_exclusive(x_329);
if (x_333 == 0)
{
lean_object* x_334; uint8_t x_335; 
x_334 = lean_ctor_get(x_329, 2);
lean_dec(x_334);
x_335 = !lean_is_exclusive(x_330);
if (x_335 == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_330, 2);
lean_dec(x_336);
lean_ctor_set(x_330, 2, x_285);
return x_291;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_330, 0);
x_338 = lean_ctor_get(x_330, 1);
x_339 = lean_ctor_get(x_330, 3);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_330);
x_340 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
lean_ctor_set(x_340, 2, x_285);
lean_ctor_set(x_340, 3, x_339);
lean_ctor_set(x_329, 2, x_340);
return x_291;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_341 = lean_ctor_get(x_329, 0);
x_342 = lean_ctor_get(x_329, 1);
x_343 = lean_ctor_get(x_329, 3);
x_344 = lean_ctor_get(x_329, 4);
x_345 = lean_ctor_get(x_329, 5);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_329);
x_346 = lean_ctor_get(x_330, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_330, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_330, 3);
lean_inc(x_348);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 x_349 = x_330;
} else {
 lean_dec_ref(x_330);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(0, 4, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_346);
lean_ctor_set(x_350, 1, x_347);
lean_ctor_set(x_350, 2, x_285);
lean_ctor_set(x_350, 3, x_348);
x_351 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_351, 0, x_341);
lean_ctor_set(x_351, 1, x_342);
lean_ctor_set(x_351, 2, x_350);
lean_ctor_set(x_351, 3, x_343);
lean_ctor_set(x_351, 4, x_344);
lean_ctor_set(x_351, 5, x_345);
lean_ctor_set(x_291, 1, x_351);
return x_291;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_352 = lean_ctor_get(x_291, 0);
lean_inc(x_352);
lean_dec(x_291);
x_353 = lean_ctor_get(x_329, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_329, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_329, 3);
lean_inc(x_355);
x_356 = lean_ctor_get(x_329, 4);
lean_inc(x_356);
x_357 = lean_ctor_get(x_329, 5);
lean_inc(x_357);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 lean_ctor_release(x_329, 2);
 lean_ctor_release(x_329, 3);
 lean_ctor_release(x_329, 4);
 lean_ctor_release(x_329, 5);
 x_358 = x_329;
} else {
 lean_dec_ref(x_329);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_330, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_330, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_330, 3);
lean_inc(x_361);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 x_362 = x_330;
} else {
 lean_dec_ref(x_330);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 4, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_359);
lean_ctor_set(x_363, 1, x_360);
lean_ctor_set(x_363, 2, x_285);
lean_ctor_set(x_363, 3, x_361);
if (lean_is_scalar(x_358)) {
 x_364 = lean_alloc_ctor(0, 6, 0);
} else {
 x_364 = x_358;
}
lean_ctor_set(x_364, 0, x_353);
lean_ctor_set(x_364, 1, x_354);
lean_ctor_set(x_364, 2, x_363);
lean_ctor_set(x_364, 3, x_355);
lean_ctor_set(x_364, 4, x_356);
lean_ctor_set(x_364, 5, x_357);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_352);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_366 = lean_ctor_get(x_12, 0);
x_367 = lean_ctor_get(x_12, 1);
x_368 = lean_ctor_get(x_12, 2);
x_369 = lean_ctor_get(x_12, 3);
x_370 = lean_ctor_get(x_12, 4);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_12);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_279);
lean_ctor_set(x_371, 1, x_21);
x_372 = lean_array_push(x_368, x_371);
x_373 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_373, 0, x_366);
lean_ctor_set(x_373, 1, x_367);
lean_ctor_set(x_373, 2, x_372);
lean_ctor_set(x_373, 3, x_369);
lean_ctor_set(x_373, 4, x_370);
x_374 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_281, x_373, x_278);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_375 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_375, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_374, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_378 = x_374;
} else {
 lean_dec_ref(x_374);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_375, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_375, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_375, 3);
lean_inc(x_381);
x_382 = lean_ctor_get(x_375, 4);
lean_inc(x_382);
x_383 = lean_ctor_get(x_375, 5);
lean_inc(x_383);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 lean_ctor_release(x_375, 4);
 lean_ctor_release(x_375, 5);
 x_384 = x_375;
} else {
 lean_dec_ref(x_375);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_376, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_376, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_376, 3);
lean_inc(x_387);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_388 = x_376;
} else {
 lean_dec_ref(x_376);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(0, 4, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_385);
lean_ctor_set(x_389, 1, x_386);
lean_ctor_set(x_389, 2, x_285);
lean_ctor_set(x_389, 3, x_387);
if (lean_is_scalar(x_384)) {
 x_390 = lean_alloc_ctor(0, 6, 0);
} else {
 x_390 = x_384;
}
lean_ctor_set(x_390, 0, x_379);
lean_ctor_set(x_390, 1, x_380);
lean_ctor_set(x_390, 2, x_389);
lean_ctor_set(x_390, 3, x_381);
lean_ctor_set(x_390, 4, x_382);
lean_ctor_set(x_390, 5, x_383);
if (lean_is_scalar(x_378)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_378;
}
lean_ctor_set(x_391, 0, x_377);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_392 = lean_ctor_get(x_374, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_392, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_374, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_395 = x_374;
} else {
 lean_dec_ref(x_374);
 x_395 = lean_box(0);
}
x_396 = lean_ctor_get(x_392, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_392, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_392, 3);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 4);
lean_inc(x_399);
x_400 = lean_ctor_get(x_392, 5);
lean_inc(x_400);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 lean_ctor_release(x_392, 4);
 lean_ctor_release(x_392, 5);
 x_401 = x_392;
} else {
 lean_dec_ref(x_392);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_393, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_393, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_393, 3);
lean_inc(x_404);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 lean_ctor_release(x_393, 2);
 lean_ctor_release(x_393, 3);
 x_405 = x_393;
} else {
 lean_dec_ref(x_393);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(0, 4, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_402);
lean_ctor_set(x_406, 1, x_403);
lean_ctor_set(x_406, 2, x_285);
lean_ctor_set(x_406, 3, x_404);
if (lean_is_scalar(x_401)) {
 x_407 = lean_alloc_ctor(0, 6, 0);
} else {
 x_407 = x_401;
}
lean_ctor_set(x_407, 0, x_396);
lean_ctor_set(x_407, 1, x_397);
lean_ctor_set(x_407, 2, x_406);
lean_ctor_set(x_407, 3, x_398);
lean_ctor_set(x_407, 4, x_399);
lean_ctor_set(x_407, 5, x_400);
if (lean_is_scalar(x_395)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_395;
}
lean_ctor_set(x_408, 0, x_394);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_409 = lean_ctor_get(x_283, 0);
x_410 = lean_ctor_get(x_283, 1);
x_411 = lean_ctor_get(x_283, 2);
x_412 = lean_ctor_get(x_283, 3);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_283);
x_413 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_414 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_414, 0, x_409);
lean_ctor_set(x_414, 1, x_410);
lean_ctor_set(x_414, 2, x_413);
lean_ctor_set(x_414, 3, x_412);
lean_ctor_set(x_278, 2, x_414);
x_415 = lean_ctor_get(x_12, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_12, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_12, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_12, 3);
lean_inc(x_418);
x_419 = lean_ctor_get(x_12, 4);
lean_inc(x_419);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_420 = x_12;
} else {
 lean_dec_ref(x_12);
 x_420 = lean_box(0);
}
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_279);
lean_ctor_set(x_421, 1, x_21);
x_422 = lean_array_push(x_417, x_421);
if (lean_is_scalar(x_420)) {
 x_423 = lean_alloc_ctor(0, 5, 0);
} else {
 x_423 = x_420;
}
lean_ctor_set(x_423, 0, x_415);
lean_ctor_set(x_423, 1, x_416);
lean_ctor_set(x_423, 2, x_422);
lean_ctor_set(x_423, 3, x_418);
lean_ctor_set(x_423, 4, x_419);
x_424 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_281, x_423, x_278);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_425, 2);
lean_inc(x_426);
x_427 = lean_ctor_get(x_424, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_428 = x_424;
} else {
 lean_dec_ref(x_424);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_425, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_425, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_425, 3);
lean_inc(x_431);
x_432 = lean_ctor_get(x_425, 4);
lean_inc(x_432);
x_433 = lean_ctor_get(x_425, 5);
lean_inc(x_433);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 lean_ctor_release(x_425, 4);
 lean_ctor_release(x_425, 5);
 x_434 = x_425;
} else {
 lean_dec_ref(x_425);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_426, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_426, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_426, 3);
lean_inc(x_437);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_438 = x_426;
} else {
 lean_dec_ref(x_426);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(0, 4, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_436);
lean_ctor_set(x_439, 2, x_411);
lean_ctor_set(x_439, 3, x_437);
if (lean_is_scalar(x_434)) {
 x_440 = lean_alloc_ctor(0, 6, 0);
} else {
 x_440 = x_434;
}
lean_ctor_set(x_440, 0, x_429);
lean_ctor_set(x_440, 1, x_430);
lean_ctor_set(x_440, 2, x_439);
lean_ctor_set(x_440, 3, x_431);
lean_ctor_set(x_440, 4, x_432);
lean_ctor_set(x_440, 5, x_433);
if (lean_is_scalar(x_428)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_428;
}
lean_ctor_set(x_441, 0, x_427);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_442 = lean_ctor_get(x_424, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_442, 2);
lean_inc(x_443);
x_444 = lean_ctor_get(x_424, 0);
lean_inc(x_444);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_445 = x_424;
} else {
 lean_dec_ref(x_424);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_442, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_442, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_442, 3);
lean_inc(x_448);
x_449 = lean_ctor_get(x_442, 4);
lean_inc(x_449);
x_450 = lean_ctor_get(x_442, 5);
lean_inc(x_450);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 lean_ctor_release(x_442, 2);
 lean_ctor_release(x_442, 3);
 lean_ctor_release(x_442, 4);
 lean_ctor_release(x_442, 5);
 x_451 = x_442;
} else {
 lean_dec_ref(x_442);
 x_451 = lean_box(0);
}
x_452 = lean_ctor_get(x_443, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_443, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_443, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 lean_ctor_release(x_443, 2);
 lean_ctor_release(x_443, 3);
 x_455 = x_443;
} else {
 lean_dec_ref(x_443);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 4, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_452);
lean_ctor_set(x_456, 1, x_453);
lean_ctor_set(x_456, 2, x_411);
lean_ctor_set(x_456, 3, x_454);
if (lean_is_scalar(x_451)) {
 x_457 = lean_alloc_ctor(0, 6, 0);
} else {
 x_457 = x_451;
}
lean_ctor_set(x_457, 0, x_446);
lean_ctor_set(x_457, 1, x_447);
lean_ctor_set(x_457, 2, x_456);
lean_ctor_set(x_457, 3, x_448);
lean_ctor_set(x_457, 4, x_449);
lean_ctor_set(x_457, 5, x_450);
if (lean_is_scalar(x_445)) {
 x_458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_458 = x_445;
}
lean_ctor_set(x_458, 0, x_444);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_459 = lean_ctor_get(x_278, 2);
x_460 = lean_ctor_get(x_278, 0);
x_461 = lean_ctor_get(x_278, 1);
x_462 = lean_ctor_get(x_278, 3);
x_463 = lean_ctor_get(x_278, 4);
x_464 = lean_ctor_get(x_278, 5);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_459);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_278);
x_465 = lean_ctor_get(x_459, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_459, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_459, 2);
lean_inc(x_467);
x_468 = lean_ctor_get(x_459, 3);
lean_inc(x_468);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_469 = x_459;
} else {
 lean_dec_ref(x_459);
 x_469 = lean_box(0);
}
x_470 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_469)) {
 x_471 = lean_alloc_ctor(0, 4, 0);
} else {
 x_471 = x_469;
}
lean_ctor_set(x_471, 0, x_465);
lean_ctor_set(x_471, 1, x_466);
lean_ctor_set(x_471, 2, x_470);
lean_ctor_set(x_471, 3, x_468);
x_472 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_472, 0, x_460);
lean_ctor_set(x_472, 1, x_461);
lean_ctor_set(x_472, 2, x_471);
lean_ctor_set(x_472, 3, x_462);
lean_ctor_set(x_472, 4, x_463);
lean_ctor_set(x_472, 5, x_464);
x_473 = lean_ctor_get(x_12, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_12, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_12, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_12, 3);
lean_inc(x_476);
x_477 = lean_ctor_get(x_12, 4);
lean_inc(x_477);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_478 = x_12;
} else {
 lean_dec_ref(x_12);
 x_478 = lean_box(0);
}
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_279);
lean_ctor_set(x_479, 1, x_21);
x_480 = lean_array_push(x_475, x_479);
if (lean_is_scalar(x_478)) {
 x_481 = lean_alloc_ctor(0, 5, 0);
} else {
 x_481 = x_478;
}
lean_ctor_set(x_481, 0, x_473);
lean_ctor_set(x_481, 1, x_474);
lean_ctor_set(x_481, 2, x_480);
lean_ctor_set(x_481, 3, x_476);
lean_ctor_set(x_481, 4, x_477);
x_482 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_281, x_481, x_472);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_483, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_482, 0);
lean_inc(x_485);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_486 = x_482;
} else {
 lean_dec_ref(x_482);
 x_486 = lean_box(0);
}
x_487 = lean_ctor_get(x_483, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_483, 1);
lean_inc(x_488);
x_489 = lean_ctor_get(x_483, 3);
lean_inc(x_489);
x_490 = lean_ctor_get(x_483, 4);
lean_inc(x_490);
x_491 = lean_ctor_get(x_483, 5);
lean_inc(x_491);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 lean_ctor_release(x_483, 2);
 lean_ctor_release(x_483, 3);
 lean_ctor_release(x_483, 4);
 lean_ctor_release(x_483, 5);
 x_492 = x_483;
} else {
 lean_dec_ref(x_483);
 x_492 = lean_box(0);
}
x_493 = lean_ctor_get(x_484, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_484, 1);
lean_inc(x_494);
x_495 = lean_ctor_get(x_484, 3);
lean_inc(x_495);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 lean_ctor_release(x_484, 2);
 lean_ctor_release(x_484, 3);
 x_496 = x_484;
} else {
 lean_dec_ref(x_484);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(0, 4, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_493);
lean_ctor_set(x_497, 1, x_494);
lean_ctor_set(x_497, 2, x_467);
lean_ctor_set(x_497, 3, x_495);
if (lean_is_scalar(x_492)) {
 x_498 = lean_alloc_ctor(0, 6, 0);
} else {
 x_498 = x_492;
}
lean_ctor_set(x_498, 0, x_487);
lean_ctor_set(x_498, 1, x_488);
lean_ctor_set(x_498, 2, x_497);
lean_ctor_set(x_498, 3, x_489);
lean_ctor_set(x_498, 4, x_490);
lean_ctor_set(x_498, 5, x_491);
if (lean_is_scalar(x_486)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_486;
}
lean_ctor_set(x_499, 0, x_485);
lean_ctor_set(x_499, 1, x_498);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_500 = lean_ctor_get(x_482, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_500, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_482, 0);
lean_inc(x_502);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_503 = x_482;
} else {
 lean_dec_ref(x_482);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_500, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_500, 1);
lean_inc(x_505);
x_506 = lean_ctor_get(x_500, 3);
lean_inc(x_506);
x_507 = lean_ctor_get(x_500, 4);
lean_inc(x_507);
x_508 = lean_ctor_get(x_500, 5);
lean_inc(x_508);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 lean_ctor_release(x_500, 2);
 lean_ctor_release(x_500, 3);
 lean_ctor_release(x_500, 4);
 lean_ctor_release(x_500, 5);
 x_509 = x_500;
} else {
 lean_dec_ref(x_500);
 x_509 = lean_box(0);
}
x_510 = lean_ctor_get(x_501, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_501, 1);
lean_inc(x_511);
x_512 = lean_ctor_get(x_501, 3);
lean_inc(x_512);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 lean_ctor_release(x_501, 2);
 lean_ctor_release(x_501, 3);
 x_513 = x_501;
} else {
 lean_dec_ref(x_501);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(0, 4, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_510);
lean_ctor_set(x_514, 1, x_511);
lean_ctor_set(x_514, 2, x_467);
lean_ctor_set(x_514, 3, x_512);
if (lean_is_scalar(x_509)) {
 x_515 = lean_alloc_ctor(0, 6, 0);
} else {
 x_515 = x_509;
}
lean_ctor_set(x_515, 0, x_504);
lean_ctor_set(x_515, 1, x_505);
lean_ctor_set(x_515, 2, x_514);
lean_ctor_set(x_515, 3, x_506);
lean_ctor_set(x_515, 4, x_507);
lean_ctor_set(x_515, 5, x_508);
if (lean_is_scalar(x_503)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_503;
}
lean_ctor_set(x_516, 0, x_502);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_517 = !lean_is_exclusive(x_272);
if (x_517 == 0)
{
return x_272;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_272, 0);
x_519 = lean_ctor_get(x_272, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_272);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
}
}
}
}
}
else
{
uint8_t x_521; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_521 = !lean_is_exclusive(x_26);
if (x_521 == 0)
{
return x_26;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_26, 0);
x_523 = lean_ctor_get(x_26, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_26);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
}
else
{
uint8_t x_525; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_525 = !lean_is_exclusive(x_22);
if (x_525 == 0)
{
return x_22;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_22, 0);
x_527 = lean_ctor_get(x_22, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_22);
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
return x_528;
}
}
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
switch (lean_obj_tag(x_8)) {
case 7:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 2);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_31 = lean_array_get_size(x_5);
x_32 = lean_expr_instantiate_rev_range(x_28, x_6, x_31, x_5);
lean_dec(x_31);
lean_dec(x_28);
x_33 = l_Lean_Expr_headBeta(x_32);
x_34 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_4);
x_37 = l_Lean_Meta_mkAuxName(x_1, x_4, x_27, x_7);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = (uint8_t)((x_30 << 24) >> 61);
lean_inc(x_35);
x_41 = lean_local_ctx_mk_local_decl(x_4, x_35, x_38, x_33, x_40);
x_42 = l_Lean_mkFVar(x_35);
x_43 = lean_array_push(x_5, x_42);
x_3 = x_14;
x_4 = x_41;
x_5 = x_43;
x_7 = x_39;
x_8 = x_29;
x_10 = x_36;
goto _start;
}
case 8:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_8, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_8, 3);
lean_inc(x_48);
lean_dec(x_8);
x_49 = lean_array_get_size(x_5);
x_50 = lean_expr_instantiate_rev_range(x_46, x_6, x_49, x_5);
lean_dec(x_46);
x_51 = l_Lean_Expr_headBeta(x_50);
x_52 = lean_expr_instantiate_rev_range(x_47, x_6, x_49, x_5);
lean_dec(x_49);
lean_dec(x_47);
x_53 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_4);
x_56 = l_Lean_Meta_mkAuxName(x_1, x_4, x_45, x_7);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_54);
x_59 = lean_local_ctx_mk_let_decl(x_4, x_54, x_57, x_51, x_52);
x_60 = l_Lean_mkFVar(x_54);
x_61 = lean_array_push(x_5, x_60);
x_3 = x_14;
x_4 = x_59;
x_5 = x_61;
x_7 = x_58;
x_8 = x_48;
x_10 = x_55;
goto _start;
}
default: 
{
lean_object* x_63; 
x_63 = lean_box(0);
x_15 = x_63;
goto block_26;
}
}
block_26:
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_15);
x_16 = lean_array_get_size(x_5);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_dec(x_18);
lean_inc(x_4);
lean_ctor_set(x_9, 1, x_4);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_14, x_16, x_5, x_6, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 2);
x_22 = lean_ctor_get(x_9, 3);
x_23 = lean_ctor_get(x_9, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
lean_inc(x_4);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_14, x_16, x_5, x_6, x_24, x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_25;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_7);
lean_dec(x_3);
x_64 = lean_array_get_size(x_5);
x_65 = lean_expr_instantiate_rev_range(x_8, x_6, x_64, x_5);
lean_dec(x_64);
lean_dec(x_8);
x_66 = !lean_is_exclusive(x_9);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_9, 1);
lean_dec(x_67);
lean_ctor_set(x_9, 1, x_4);
lean_inc(x_5);
x_68 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_2, x_5, x_65, x_5, x_6, x_9, x_10);
lean_dec(x_5);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 2);
x_71 = lean_ctor_get(x_9, 3);
x_72 = lean_ctor_get(x_9, 4);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_4);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_72);
lean_inc(x_5);
x_74 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_2, x_5, x_65, x_5, x_6, x_73, x_10);
lean_dec(x_5);
return x_74;
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
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_fget(x_2, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = x_5;
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_7, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getMVarType(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = l_Array_empty___closed__1;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_2, x_1, x_3, x_11, x_12, x_13, x_4, x_9, x_6, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = x_18;
x_20 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_13, x_19);
x_21 = x_20;
lean_ctor_set(x_16, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = x_22;
x_25 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_13, x_24);
x_26 = x_25;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_33 = x_30;
x_34 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_13, x_33);
x_35 = x_34;
if (lean_is_scalar(x_32)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_32;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 4, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_box(x_1);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1___boxed), 7, 4);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_getMVarDecl(x_2, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 4);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_withLocalContext___rarg(x_15, x_16, x_11, x_5, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_introN(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_4, x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_Meta_introN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_introN(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_Meta_intro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = 1;
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_7, x_1, x_8, x_6, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Name_inhabited;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_13, x_15);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = l_Lean_Name_inhabited;
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get(x_19, x_17, x_20);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
x_28 = l_Lean_Name_inhabited;
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get(x_28, x_25, x_29);
lean_dec(x_25);
if (lean_is_scalar(x_27)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_27;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Meta_intro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_intro(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_intro1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2, x_1, x_6, x_5, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Name_inhabited;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get(x_12, x_11, x_13);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = l_Lean_Name_inhabited;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_15, x_18);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = l_Lean_Name_inhabited;
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get(x_26, x_23, x_27);
lean_dec(x_23);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_intro1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_intro1(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Init_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Intro(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_Tactic_Util(lean_io_mk_world());
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
l_Lean_Meta_mkAuxName___closed__1 = _init_l_Lean_Meta_mkAuxName___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxName___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
