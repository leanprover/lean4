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
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_assignExprMVar(x_3, x_13, x_5, x_14);
lean_dec(x_5);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
x_8 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l_Lean_Meta_getMVarType(x_1, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = l_Array_empty___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_4, x_13, x_14, x_15, x_5, x_11, x_6, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = x_20;
x_22 = l_Id_monad;
x_23 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_24 = l_Array_umapMAux___main___rarg(x_22, lean_box(0), x_23, x_15, x_21);
x_25 = x_24;
lean_ctor_set(x_18, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = x_26;
x_29 = l_Id_monad;
x_30 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_31 = l_Array_umapMAux___main___rarg(x_29, lean_box(0), x_30, x_15, x_28);
x_32 = x_31;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_16, 0, x_33);
return x_16;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
x_39 = x_36;
x_40 = l_Id_monad;
x_41 = l_Lean_Meta_introNCore___rarg___lambda__2___closed__1;
x_42 = l_Array_umapMAux___main___rarg(x_40, lean_box(0), x_41, x_15, x_39);
x_43 = x_42;
if (lean_is_scalar(x_38)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_38;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
return x_10;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
return x_8;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_Meta_introNCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___rarg___lambda__2), 7, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_4);
x_9 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 4);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Meta_withLocalContext___rarg(x_12, x_13, x_8, x_5, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_25 = x_18;
} else {
 lean_dec_ref(x_18);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_5, x_27);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_84; uint8_t x_85; 
x_32 = lean_ctor_get(x_30, 2);
x_84 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_30, 2, x_84);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_6, 2);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_26);
lean_ctor_set(x_87, 1, x_13);
x_88 = lean_array_push(x_86, x_87);
lean_ctor_set(x_6, 2, x_88);
x_89 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_28, x_6, x_24);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_90);
x_33 = x_92;
x_34 = x_91;
goto block_83;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_93);
x_33 = x_95;
x_34 = x_94;
goto block_83;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_6, 0);
x_97 = lean_ctor_get(x_6, 1);
x_98 = lean_ctor_get(x_6, 2);
x_99 = lean_ctor_get(x_6, 3);
x_100 = lean_ctor_get(x_6, 4);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_6);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_26);
lean_ctor_set(x_101, 1, x_13);
x_102 = lean_array_push(x_98, x_101);
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_97);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_99);
lean_ctor_set(x_103, 4, x_100);
x_104 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_28, x_103, x_24);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_105);
x_33 = x_107;
x_34 = x_106;
goto block_83;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_108);
x_33 = x_110;
x_34 = x_109;
goto block_83;
}
}
block_83:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 2);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 2);
lean_dec(x_40);
lean_ctor_set(x_35, 2, x_32);
if (lean_is_scalar(x_25)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_25;
 lean_ctor_set_tag(x_41, 1);
}
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
x_44 = lean_ctor_get(x_35, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_32);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_34, 2, x_45);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_25;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_34);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_34, 0);
x_48 = lean_ctor_get(x_34, 1);
x_49 = lean_ctor_get(x_34, 3);
x_50 = lean_ctor_get(x_34, 4);
x_51 = lean_ctor_get(x_34, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_34);
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_35, 3);
lean_inc(x_54);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 x_55 = x_35;
} else {
 lean_dec_ref(x_35);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 4, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_32);
lean_ctor_set(x_56, 3, x_54);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_49);
lean_ctor_set(x_57, 4, x_50);
lean_ctor_set(x_57, 5, x_51);
if (lean_is_scalar(x_25)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_25;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_34, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = !lean_is_exclusive(x_34);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_34, 2);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_59, 2);
lean_dec(x_64);
lean_ctor_set(x_59, 2, x_32);
if (lean_is_scalar(x_25)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_25;
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_34);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
x_68 = lean_ctor_get(x_59, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_32);
lean_ctor_set(x_69, 3, x_68);
lean_ctor_set(x_34, 2, x_69);
if (lean_is_scalar(x_25)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_25;
}
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_34);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_34, 0);
x_72 = lean_ctor_get(x_34, 1);
x_73 = lean_ctor_get(x_34, 3);
x_74 = lean_ctor_get(x_34, 4);
x_75 = lean_ctor_get(x_34, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_34);
x_76 = lean_ctor_get(x_59, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_59, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_59, 3);
lean_inc(x_78);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 x_79 = x_59;
} else {
 lean_dec_ref(x_59);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 4, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_77);
lean_ctor_set(x_80, 2, x_32);
lean_ctor_set(x_80, 3, x_78);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_72);
lean_ctor_set(x_81, 2, x_80);
lean_ctor_set(x_81, 3, x_73);
lean_ctor_set(x_81, 4, x_74);
lean_ctor_set(x_81, 5, x_75);
if (lean_is_scalar(x_25)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_25;
}
lean_ctor_set(x_82, 0, x_60);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_111 = lean_ctor_get(x_30, 0);
x_112 = lean_ctor_get(x_30, 1);
x_113 = lean_ctor_get(x_30, 2);
x_114 = lean_ctor_get(x_30, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_30);
x_148 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_149 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_149, 0, x_111);
lean_ctor_set(x_149, 1, x_112);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_114);
lean_ctor_set(x_24, 2, x_149);
x_150 = lean_ctor_get(x_6, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_6, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_6, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_6, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_6, 4);
lean_inc(x_154);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_155 = x_6;
} else {
 lean_dec_ref(x_6);
 x_155 = lean_box(0);
}
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_26);
lean_ctor_set(x_156, 1, x_13);
x_157 = lean_array_push(x_152, x_156);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 5, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_151);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_153);
lean_ctor_set(x_158, 4, x_154);
x_159 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_28, x_158, x_24);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_160);
x_115 = x_162;
x_116 = x_161;
goto block_147;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_dec(x_159);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_163);
x_115 = x_165;
x_116 = x_164;
goto block_147;
}
block_147:
{
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_117 = lean_ctor_get(x_116, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 lean_ctor_release(x_116, 4);
 lean_ctor_release(x_116, 5);
 x_124 = x_116;
} else {
 lean_dec_ref(x_116);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_117, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_117, 3);
lean_inc(x_127);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_128 = x_117;
} else {
 lean_dec_ref(x_117);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 4, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_113);
lean_ctor_set(x_129, 3, x_127);
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(0, 6, 0);
} else {
 x_130 = x_124;
}
lean_ctor_set(x_130, 0, x_119);
lean_ctor_set(x_130, 1, x_120);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_121);
lean_ctor_set(x_130, 4, x_122);
lean_ctor_set(x_130, 5, x_123);
if (lean_is_scalar(x_25)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_25;
 lean_ctor_set_tag(x_131, 1);
}
lean_ctor_set(x_131, 0, x_118);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_132 = lean_ctor_get(x_116, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_115, 0);
lean_inc(x_133);
lean_dec(x_115);
x_134 = lean_ctor_get(x_116, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_116, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_116, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_116, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_116, 5);
lean_inc(x_138);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 lean_ctor_release(x_116, 4);
 lean_ctor_release(x_116, 5);
 x_139 = x_116;
} else {
 lean_dec_ref(x_116);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_132, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_132, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_132, 3);
lean_inc(x_142);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 x_143 = x_132;
} else {
 lean_dec_ref(x_132);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 4, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_141);
lean_ctor_set(x_144, 2, x_113);
lean_ctor_set(x_144, 3, x_142);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(0, 6, 0);
} else {
 x_145 = x_139;
}
lean_ctor_set(x_145, 0, x_134);
lean_ctor_set(x_145, 1, x_135);
lean_ctor_set(x_145, 2, x_144);
lean_ctor_set(x_145, 3, x_136);
lean_ctor_set(x_145, 4, x_137);
lean_ctor_set(x_145, 5, x_138);
if (lean_is_scalar(x_25)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_25;
}
lean_ctor_set(x_146, 0, x_133);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_166 = lean_ctor_get(x_24, 2);
x_167 = lean_ctor_get(x_24, 0);
x_168 = lean_ctor_get(x_24, 1);
x_169 = lean_ctor_get(x_24, 3);
x_170 = lean_ctor_get(x_24, 4);
x_171 = lean_ctor_get(x_24, 5);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_166);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_24);
x_172 = lean_ctor_get(x_166, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_166, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_166, 3);
lean_inc(x_175);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 x_176 = x_166;
} else {
 lean_dec_ref(x_166);
 x_176 = lean_box(0);
}
x_210 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_176)) {
 x_211 = lean_alloc_ctor(0, 4, 0);
} else {
 x_211 = x_176;
}
lean_ctor_set(x_211, 0, x_172);
lean_ctor_set(x_211, 1, x_173);
lean_ctor_set(x_211, 2, x_210);
lean_ctor_set(x_211, 3, x_175);
x_212 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_212, 0, x_167);
lean_ctor_set(x_212, 1, x_168);
lean_ctor_set(x_212, 2, x_211);
lean_ctor_set(x_212, 3, x_169);
lean_ctor_set(x_212, 4, x_170);
lean_ctor_set(x_212, 5, x_171);
x_213 = lean_ctor_get(x_6, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_6, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_6, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_6, 3);
lean_inc(x_216);
x_217 = lean_ctor_get(x_6, 4);
lean_inc(x_217);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_218 = x_6;
} else {
 lean_dec_ref(x_6);
 x_218 = lean_box(0);
}
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_26);
lean_ctor_set(x_219, 1, x_13);
x_220 = lean_array_push(x_215, x_219);
if (lean_is_scalar(x_218)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_218;
}
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_214);
lean_ctor_set(x_221, 2, x_220);
lean_ctor_set(x_221, 3, x_216);
lean_ctor_set(x_221, 4, x_217);
x_222 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_28, x_221, x_212);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_223);
x_177 = x_225;
x_178 = x_224;
goto block_209;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_222, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
lean_dec(x_222);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_226);
x_177 = x_228;
x_178 = x_227;
goto block_209;
}
block_209:
{
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_179 = lean_ctor_get(x_178, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
lean_dec(x_177);
x_181 = lean_ctor_get(x_178, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 5);
lean_inc(x_185);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 lean_ctor_release(x_178, 5);
 x_186 = x_178;
} else {
 lean_dec_ref(x_178);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_179, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_179, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_179, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 x_190 = x_179;
} else {
 lean_dec_ref(x_179);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 4, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_188);
lean_ctor_set(x_191, 2, x_174);
lean_ctor_set(x_191, 3, x_189);
if (lean_is_scalar(x_186)) {
 x_192 = lean_alloc_ctor(0, 6, 0);
} else {
 x_192 = x_186;
}
lean_ctor_set(x_192, 0, x_181);
lean_ctor_set(x_192, 1, x_182);
lean_ctor_set(x_192, 2, x_191);
lean_ctor_set(x_192, 3, x_183);
lean_ctor_set(x_192, 4, x_184);
lean_ctor_set(x_192, 5, x_185);
if (lean_is_scalar(x_25)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_25;
 lean_ctor_set_tag(x_193, 1);
}
lean_ctor_set(x_193, 0, x_180);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_194 = lean_ctor_get(x_178, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_177, 0);
lean_inc(x_195);
lean_dec(x_177);
x_196 = lean_ctor_get(x_178, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_178, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_178, 3);
lean_inc(x_198);
x_199 = lean_ctor_get(x_178, 4);
lean_inc(x_199);
x_200 = lean_ctor_get(x_178, 5);
lean_inc(x_200);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 lean_ctor_release(x_178, 5);
 x_201 = x_178;
} else {
 lean_dec_ref(x_178);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_194, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_194, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_194, 3);
lean_inc(x_204);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_205 = x_194;
} else {
 lean_dec_ref(x_194);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 4, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_202);
lean_ctor_set(x_206, 1, x_203);
lean_ctor_set(x_206, 2, x_174);
lean_ctor_set(x_206, 3, x_204);
if (lean_is_scalar(x_201)) {
 x_207 = lean_alloc_ctor(0, 6, 0);
} else {
 x_207 = x_201;
}
lean_ctor_set(x_207, 0, x_196);
lean_ctor_set(x_207, 1, x_197);
lean_ctor_set(x_207, 2, x_206);
lean_ctor_set(x_207, 3, x_198);
lean_ctor_set(x_207, 4, x_199);
lean_ctor_set(x_207, 5, x_200);
if (lean_is_scalar(x_25)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_25;
}
lean_ctor_set(x_208, 0, x_195);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
default: 
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_18, 1);
lean_inc(x_229);
lean_dec(x_18);
lean_inc(x_6);
x_230 = l_Lean_Meta_isClassExpensive___main(x_17, x_6, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_13);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_nat_add(x_5, x_233);
lean_dec(x_5);
x_5 = x_234;
x_7 = x_232;
goto _start;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_237 = x_230;
} else {
 lean_dec_ref(x_230);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_231, 0);
lean_inc(x_238);
lean_dec(x_231);
x_239 = lean_unsigned_to_nat(1u);
x_240 = lean_nat_add(x_5, x_239);
lean_dec(x_5);
x_241 = !lean_is_exclusive(x_236);
if (x_241 == 0)
{
lean_object* x_242; uint8_t x_243; 
x_242 = lean_ctor_get(x_236, 2);
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_296; uint8_t x_297; 
x_244 = lean_ctor_get(x_242, 2);
x_296 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_242, 2, x_296);
x_297 = !lean_is_exclusive(x_6);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_298 = lean_ctor_get(x_6, 2);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_238);
lean_ctor_set(x_299, 1, x_13);
x_300 = lean_array_push(x_298, x_299);
lean_ctor_set(x_6, 2, x_300);
x_301 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_240, x_6, x_236);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_302);
x_245 = x_304;
x_246 = x_303;
goto block_295;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_301, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_301, 1);
lean_inc(x_306);
lean_dec(x_301);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_305);
x_245 = x_307;
x_246 = x_306;
goto block_295;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_308 = lean_ctor_get(x_6, 0);
x_309 = lean_ctor_get(x_6, 1);
x_310 = lean_ctor_get(x_6, 2);
x_311 = lean_ctor_get(x_6, 3);
x_312 = lean_ctor_get(x_6, 4);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_6);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_238);
lean_ctor_set(x_313, 1, x_13);
x_314 = lean_array_push(x_310, x_313);
x_315 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_315, 0, x_308);
lean_ctor_set(x_315, 1, x_309);
lean_ctor_set(x_315, 2, x_314);
lean_ctor_set(x_315, 3, x_311);
lean_ctor_set(x_315, 4, x_312);
x_316 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_240, x_315, x_236);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_317);
x_245 = x_319;
x_246 = x_318;
goto block_295;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_316, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_316, 1);
lean_inc(x_321);
lean_dec(x_316);
x_322 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_322, 0, x_320);
x_245 = x_322;
x_246 = x_321;
goto block_295;
}
}
block_295:
{
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_247 = lean_ctor_get(x_246, 2);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
lean_dec(x_245);
x_249 = !lean_is_exclusive(x_246);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_246, 2);
lean_dec(x_250);
x_251 = !lean_is_exclusive(x_247);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_247, 2);
lean_dec(x_252);
lean_ctor_set(x_247, 2, x_244);
if (lean_is_scalar(x_237)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_237;
 lean_ctor_set_tag(x_253, 1);
}
lean_ctor_set(x_253, 0, x_248);
lean_ctor_set(x_253, 1, x_246);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_247, 0);
x_255 = lean_ctor_get(x_247, 1);
x_256 = lean_ctor_get(x_247, 3);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_247);
x_257 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
lean_ctor_set(x_257, 2, x_244);
lean_ctor_set(x_257, 3, x_256);
lean_ctor_set(x_246, 2, x_257);
if (lean_is_scalar(x_237)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_237;
 lean_ctor_set_tag(x_258, 1);
}
lean_ctor_set(x_258, 0, x_248);
lean_ctor_set(x_258, 1, x_246);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_259 = lean_ctor_get(x_246, 0);
x_260 = lean_ctor_get(x_246, 1);
x_261 = lean_ctor_get(x_246, 3);
x_262 = lean_ctor_get(x_246, 4);
x_263 = lean_ctor_get(x_246, 5);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_246);
x_264 = lean_ctor_get(x_247, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_247, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_247, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_267 = x_247;
} else {
 lean_dec_ref(x_247);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 4, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_265);
lean_ctor_set(x_268, 2, x_244);
lean_ctor_set(x_268, 3, x_266);
x_269 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_269, 0, x_259);
lean_ctor_set(x_269, 1, x_260);
lean_ctor_set(x_269, 2, x_268);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set(x_269, 4, x_262);
lean_ctor_set(x_269, 5, x_263);
if (lean_is_scalar(x_237)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_237;
 lean_ctor_set_tag(x_270, 1);
}
lean_ctor_set(x_270, 0, x_248);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_271 = lean_ctor_get(x_246, 2);
lean_inc(x_271);
x_272 = lean_ctor_get(x_245, 0);
lean_inc(x_272);
lean_dec(x_245);
x_273 = !lean_is_exclusive(x_246);
if (x_273 == 0)
{
lean_object* x_274; uint8_t x_275; 
x_274 = lean_ctor_get(x_246, 2);
lean_dec(x_274);
x_275 = !lean_is_exclusive(x_271);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_271, 2);
lean_dec(x_276);
lean_ctor_set(x_271, 2, x_244);
if (lean_is_scalar(x_237)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_237;
}
lean_ctor_set(x_277, 0, x_272);
lean_ctor_set(x_277, 1, x_246);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_278 = lean_ctor_get(x_271, 0);
x_279 = lean_ctor_get(x_271, 1);
x_280 = lean_ctor_get(x_271, 3);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_271);
x_281 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
lean_ctor_set(x_281, 2, x_244);
lean_ctor_set(x_281, 3, x_280);
lean_ctor_set(x_246, 2, x_281);
if (lean_is_scalar(x_237)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_237;
}
lean_ctor_set(x_282, 0, x_272);
lean_ctor_set(x_282, 1, x_246);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_283 = lean_ctor_get(x_246, 0);
x_284 = lean_ctor_get(x_246, 1);
x_285 = lean_ctor_get(x_246, 3);
x_286 = lean_ctor_get(x_246, 4);
x_287 = lean_ctor_get(x_246, 5);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_246);
x_288 = lean_ctor_get(x_271, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_271, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_271, 3);
lean_inc(x_290);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_291 = x_271;
} else {
 lean_dec_ref(x_271);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 4, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_289);
lean_ctor_set(x_292, 2, x_244);
lean_ctor_set(x_292, 3, x_290);
x_293 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_293, 0, x_283);
lean_ctor_set(x_293, 1, x_284);
lean_ctor_set(x_293, 2, x_292);
lean_ctor_set(x_293, 3, x_285);
lean_ctor_set(x_293, 4, x_286);
lean_ctor_set(x_293, 5, x_287);
if (lean_is_scalar(x_237)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_237;
}
lean_ctor_set(x_294, 0, x_272);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_323 = lean_ctor_get(x_242, 0);
x_324 = lean_ctor_get(x_242, 1);
x_325 = lean_ctor_get(x_242, 2);
x_326 = lean_ctor_get(x_242, 3);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_242);
x_360 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_361 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_361, 0, x_323);
lean_ctor_set(x_361, 1, x_324);
lean_ctor_set(x_361, 2, x_360);
lean_ctor_set(x_361, 3, x_326);
lean_ctor_set(x_236, 2, x_361);
x_362 = lean_ctor_get(x_6, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_6, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_6, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_6, 3);
lean_inc(x_365);
x_366 = lean_ctor_get(x_6, 4);
lean_inc(x_366);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_367 = x_6;
} else {
 lean_dec_ref(x_6);
 x_367 = lean_box(0);
}
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_238);
lean_ctor_set(x_368, 1, x_13);
x_369 = lean_array_push(x_364, x_368);
if (lean_is_scalar(x_367)) {
 x_370 = lean_alloc_ctor(0, 5, 0);
} else {
 x_370 = x_367;
}
lean_ctor_set(x_370, 0, x_362);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_369);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set(x_370, 4, x_366);
x_371 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_240, x_370, x_236);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec(x_371);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_372);
x_327 = x_374;
x_328 = x_373;
goto block_359;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_371, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_371, 1);
lean_inc(x_376);
lean_dec(x_371);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_375);
x_327 = x_377;
x_328 = x_376;
goto block_359;
}
block_359:
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_329 = lean_ctor_get(x_328, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_327, 0);
lean_inc(x_330);
lean_dec(x_327);
x_331 = lean_ctor_get(x_328, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_328, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_328, 3);
lean_inc(x_333);
x_334 = lean_ctor_get(x_328, 4);
lean_inc(x_334);
x_335 = lean_ctor_get(x_328, 5);
lean_inc(x_335);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 lean_ctor_release(x_328, 2);
 lean_ctor_release(x_328, 3);
 lean_ctor_release(x_328, 4);
 lean_ctor_release(x_328, 5);
 x_336 = x_328;
} else {
 lean_dec_ref(x_328);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_329, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_329, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_329, 3);
lean_inc(x_339);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 lean_ctor_release(x_329, 2);
 lean_ctor_release(x_329, 3);
 x_340 = x_329;
} else {
 lean_dec_ref(x_329);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(0, 4, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_337);
lean_ctor_set(x_341, 1, x_338);
lean_ctor_set(x_341, 2, x_325);
lean_ctor_set(x_341, 3, x_339);
if (lean_is_scalar(x_336)) {
 x_342 = lean_alloc_ctor(0, 6, 0);
} else {
 x_342 = x_336;
}
lean_ctor_set(x_342, 0, x_331);
lean_ctor_set(x_342, 1, x_332);
lean_ctor_set(x_342, 2, x_341);
lean_ctor_set(x_342, 3, x_333);
lean_ctor_set(x_342, 4, x_334);
lean_ctor_set(x_342, 5, x_335);
if (lean_is_scalar(x_237)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_237;
 lean_ctor_set_tag(x_343, 1);
}
lean_ctor_set(x_343, 0, x_330);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_344 = lean_ctor_get(x_328, 2);
lean_inc(x_344);
x_345 = lean_ctor_get(x_327, 0);
lean_inc(x_345);
lean_dec(x_327);
x_346 = lean_ctor_get(x_328, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_328, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_328, 3);
lean_inc(x_348);
x_349 = lean_ctor_get(x_328, 4);
lean_inc(x_349);
x_350 = lean_ctor_get(x_328, 5);
lean_inc(x_350);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 lean_ctor_release(x_328, 2);
 lean_ctor_release(x_328, 3);
 lean_ctor_release(x_328, 4);
 lean_ctor_release(x_328, 5);
 x_351 = x_328;
} else {
 lean_dec_ref(x_328);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_344, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_344, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_344, 3);
lean_inc(x_354);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 lean_ctor_release(x_344, 2);
 lean_ctor_release(x_344, 3);
 x_355 = x_344;
} else {
 lean_dec_ref(x_344);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(0, 4, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_352);
lean_ctor_set(x_356, 1, x_353);
lean_ctor_set(x_356, 2, x_325);
lean_ctor_set(x_356, 3, x_354);
if (lean_is_scalar(x_351)) {
 x_357 = lean_alloc_ctor(0, 6, 0);
} else {
 x_357 = x_351;
}
lean_ctor_set(x_357, 0, x_346);
lean_ctor_set(x_357, 1, x_347);
lean_ctor_set(x_357, 2, x_356);
lean_ctor_set(x_357, 3, x_348);
lean_ctor_set(x_357, 4, x_349);
lean_ctor_set(x_357, 5, x_350);
if (lean_is_scalar(x_237)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_237;
}
lean_ctor_set(x_358, 0, x_345);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_378 = lean_ctor_get(x_236, 2);
x_379 = lean_ctor_get(x_236, 0);
x_380 = lean_ctor_get(x_236, 1);
x_381 = lean_ctor_get(x_236, 3);
x_382 = lean_ctor_get(x_236, 4);
x_383 = lean_ctor_get(x_236, 5);
lean_inc(x_383);
lean_inc(x_382);
lean_inc(x_381);
lean_inc(x_378);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_236);
x_384 = lean_ctor_get(x_378, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_378, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_378, 2);
lean_inc(x_386);
x_387 = lean_ctor_get(x_378, 3);
lean_inc(x_387);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_388 = x_378;
} else {
 lean_dec_ref(x_378);
 x_388 = lean_box(0);
}
x_422 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_388)) {
 x_423 = lean_alloc_ctor(0, 4, 0);
} else {
 x_423 = x_388;
}
lean_ctor_set(x_423, 0, x_384);
lean_ctor_set(x_423, 1, x_385);
lean_ctor_set(x_423, 2, x_422);
lean_ctor_set(x_423, 3, x_387);
x_424 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_424, 0, x_379);
lean_ctor_set(x_424, 1, x_380);
lean_ctor_set(x_424, 2, x_423);
lean_ctor_set(x_424, 3, x_381);
lean_ctor_set(x_424, 4, x_382);
lean_ctor_set(x_424, 5, x_383);
x_425 = lean_ctor_get(x_6, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_6, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_6, 2);
lean_inc(x_427);
x_428 = lean_ctor_get(x_6, 3);
lean_inc(x_428);
x_429 = lean_ctor_get(x_6, 4);
lean_inc(x_429);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_430 = x_6;
} else {
 lean_dec_ref(x_6);
 x_430 = lean_box(0);
}
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_238);
lean_ctor_set(x_431, 1, x_13);
x_432 = lean_array_push(x_427, x_431);
if (lean_is_scalar(x_430)) {
 x_433 = lean_alloc_ctor(0, 5, 0);
} else {
 x_433 = x_430;
}
lean_ctor_set(x_433, 0, x_425);
lean_ctor_set(x_433, 1, x_426);
lean_ctor_set(x_433, 2, x_432);
lean_ctor_set(x_433, 3, x_428);
lean_ctor_set(x_433, 4, x_429);
x_434 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_240, x_433, x_424);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_437, 0, x_435);
x_389 = x_437;
x_390 = x_436;
goto block_421;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_434, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_434, 1);
lean_inc(x_439);
lean_dec(x_434);
x_440 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_440, 0, x_438);
x_389 = x_440;
x_390 = x_439;
goto block_421;
}
block_421:
{
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_391 = lean_ctor_get(x_390, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_389, 0);
lean_inc(x_392);
lean_dec(x_389);
x_393 = lean_ctor_get(x_390, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_390, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_390, 3);
lean_inc(x_395);
x_396 = lean_ctor_get(x_390, 4);
lean_inc(x_396);
x_397 = lean_ctor_get(x_390, 5);
lean_inc(x_397);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 lean_ctor_release(x_390, 2);
 lean_ctor_release(x_390, 3);
 lean_ctor_release(x_390, 4);
 lean_ctor_release(x_390, 5);
 x_398 = x_390;
} else {
 lean_dec_ref(x_390);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_391, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_391, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_391, 3);
lean_inc(x_401);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 lean_ctor_release(x_391, 2);
 lean_ctor_release(x_391, 3);
 x_402 = x_391;
} else {
 lean_dec_ref(x_391);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(0, 4, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_399);
lean_ctor_set(x_403, 1, x_400);
lean_ctor_set(x_403, 2, x_386);
lean_ctor_set(x_403, 3, x_401);
if (lean_is_scalar(x_398)) {
 x_404 = lean_alloc_ctor(0, 6, 0);
} else {
 x_404 = x_398;
}
lean_ctor_set(x_404, 0, x_393);
lean_ctor_set(x_404, 1, x_394);
lean_ctor_set(x_404, 2, x_403);
lean_ctor_set(x_404, 3, x_395);
lean_ctor_set(x_404, 4, x_396);
lean_ctor_set(x_404, 5, x_397);
if (lean_is_scalar(x_237)) {
 x_405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_405 = x_237;
 lean_ctor_set_tag(x_405, 1);
}
lean_ctor_set(x_405, 0, x_392);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_406 = lean_ctor_get(x_390, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_389, 0);
lean_inc(x_407);
lean_dec(x_389);
x_408 = lean_ctor_get(x_390, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_390, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_390, 3);
lean_inc(x_410);
x_411 = lean_ctor_get(x_390, 4);
lean_inc(x_411);
x_412 = lean_ctor_get(x_390, 5);
lean_inc(x_412);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 lean_ctor_release(x_390, 2);
 lean_ctor_release(x_390, 3);
 lean_ctor_release(x_390, 4);
 lean_ctor_release(x_390, 5);
 x_413 = x_390;
} else {
 lean_dec_ref(x_390);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_406, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_406, 1);
lean_inc(x_415);
x_416 = lean_ctor_get(x_406, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 lean_ctor_release(x_406, 2);
 lean_ctor_release(x_406, 3);
 x_417 = x_406;
} else {
 lean_dec_ref(x_406);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(0, 4, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_414);
lean_ctor_set(x_418, 1, x_415);
lean_ctor_set(x_418, 2, x_386);
lean_ctor_set(x_418, 3, x_416);
if (lean_is_scalar(x_413)) {
 x_419 = lean_alloc_ctor(0, 6, 0);
} else {
 x_419 = x_413;
}
lean_ctor_set(x_419, 0, x_408);
lean_ctor_set(x_419, 1, x_409);
lean_ctor_set(x_419, 2, x_418);
lean_ctor_set(x_419, 3, x_410);
lean_ctor_set(x_419, 4, x_411);
lean_ctor_set(x_419, 5, x_412);
if (lean_is_scalar(x_237)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_237;
}
lean_ctor_set(x_420, 0, x_407);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
}
}
else
{
uint8_t x_441; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_441 = !lean_is_exclusive(x_230);
if (x_441 == 0)
{
return x_230;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_230, 0);
x_443 = lean_ctor_get(x_230, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_230);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
return x_444;
}
}
}
}
}
else
{
uint8_t x_445; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_445 = !lean_is_exclusive(x_18);
if (x_445 == 0)
{
return x_18;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_18, 0);
x_447 = lean_ctor_get(x_18, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_18);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
else
{
uint8_t x_449; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_449 = !lean_is_exclusive(x_14);
if (x_449 == 0)
{
return x_14;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_14, 0);
x_451 = lean_ctor_get(x_14, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_14);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
return x_452;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_11, x_35);
lean_dec(x_11);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_32, 2);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_92; uint8_t x_93; 
x_40 = lean_ctor_get(x_38, 2);
x_92 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_38, 2, x_92);
x_93 = !lean_is_exclusive(x_12);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_12, 2);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_34);
lean_ctor_set(x_95, 1, x_21);
x_96 = lean_array_push(x_94, x_95);
lean_ctor_set(x_12, 2, x_96);
x_97 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_12, x_32);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_98);
x_41 = x_100;
x_42 = x_99;
goto block_91;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_dec(x_97);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_41 = x_103;
x_42 = x_102;
goto block_91;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_12, 0);
x_105 = lean_ctor_get(x_12, 1);
x_106 = lean_ctor_get(x_12, 2);
x_107 = lean_ctor_get(x_12, 3);
x_108 = lean_ctor_get(x_12, 4);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_12);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_34);
lean_ctor_set(x_109, 1, x_21);
x_110 = lean_array_push(x_106, x_109);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_105);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_111, 3, x_107);
lean_ctor_set(x_111, 4, x_108);
x_112 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_111, x_32);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_113);
x_41 = x_115;
x_42 = x_114;
goto block_91;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_41 = x_118;
x_42 = x_117;
goto block_91;
}
}
block_91:
{
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 2);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_43, 2);
lean_dec(x_48);
lean_ctor_set(x_43, 2, x_40);
if (lean_is_scalar(x_33)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_33;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
x_52 = lean_ctor_get(x_43, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_42, 2, x_53);
if (lean_is_scalar(x_33)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_33;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_42);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 1);
x_57 = lean_ctor_get(x_42, 3);
x_58 = lean_ctor_get(x_42, 4);
x_59 = lean_ctor_get(x_42, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_60 = lean_ctor_get(x_43, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_43, 3);
lean_inc(x_62);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_63 = x_43;
} else {
 lean_dec_ref(x_43);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 4, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_40);
lean_ctor_set(x_64, 3, x_62);
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_56);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_57);
lean_ctor_set(x_65, 4, x_58);
lean_ctor_set(x_65, 5, x_59);
if (lean_is_scalar(x_33)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_33;
 lean_ctor_set_tag(x_66, 1);
}
lean_ctor_set(x_66, 0, x_44);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_42, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_41, 0);
lean_inc(x_68);
lean_dec(x_41);
x_69 = !lean_is_exclusive(x_42);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_42, 2);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_67, 2);
lean_dec(x_72);
lean_ctor_set(x_67, 2, x_40);
if (lean_is_scalar(x_33)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_33;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_42);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
x_76 = lean_ctor_get(x_67, 3);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_40);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_42, 2, x_77);
if (lean_is_scalar(x_33)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_33;
}
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_42);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = lean_ctor_get(x_42, 0);
x_80 = lean_ctor_get(x_42, 1);
x_81 = lean_ctor_get(x_42, 3);
x_82 = lean_ctor_get(x_42, 4);
x_83 = lean_ctor_get(x_42, 5);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_42);
x_84 = lean_ctor_get(x_67, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_67, 3);
lean_inc(x_86);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 x_87 = x_67;
} else {
 lean_dec_ref(x_67);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 4, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_88, 2, x_40);
lean_ctor_set(x_88, 3, x_86);
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_81);
lean_ctor_set(x_89, 4, x_82);
lean_ctor_set(x_89, 5, x_83);
if (lean_is_scalar(x_33)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_33;
}
lean_ctor_set(x_90, 0, x_68);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_119 = lean_ctor_get(x_38, 0);
x_120 = lean_ctor_get(x_38, 1);
x_121 = lean_ctor_get(x_38, 2);
x_122 = lean_ctor_get(x_38, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_38);
x_156 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_157 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_157, 0, x_119);
lean_ctor_set(x_157, 1, x_120);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_122);
lean_ctor_set(x_32, 2, x_157);
x_158 = lean_ctor_get(x_12, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_12, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_12, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_12, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_12, 4);
lean_inc(x_162);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_163 = x_12;
} else {
 lean_dec_ref(x_12);
 x_163 = lean_box(0);
}
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_34);
lean_ctor_set(x_164, 1, x_21);
x_165 = lean_array_push(x_160, x_164);
if (lean_is_scalar(x_163)) {
 x_166 = lean_alloc_ctor(0, 5, 0);
} else {
 x_166 = x_163;
}
lean_ctor_set(x_166, 0, x_158);
lean_ctor_set(x_166, 1, x_159);
lean_ctor_set(x_166, 2, x_165);
lean_ctor_set(x_166, 3, x_161);
lean_ctor_set(x_166, 4, x_162);
x_167 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_166, x_32);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_168);
x_123 = x_170;
x_124 = x_169;
goto block_155;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_167, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
lean_dec(x_167);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_171);
x_123 = x_173;
x_124 = x_172;
goto block_155;
}
block_155:
{
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_125 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 5);
lean_inc(x_131);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_132 = x_124;
} else {
 lean_dec_ref(x_124);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_125, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_125, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_125, 3);
lean_inc(x_135);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 x_136 = x_125;
} else {
 lean_dec_ref(x_125);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 4, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_121);
lean_ctor_set(x_137, 3, x_135);
if (lean_is_scalar(x_132)) {
 x_138 = lean_alloc_ctor(0, 6, 0);
} else {
 x_138 = x_132;
}
lean_ctor_set(x_138, 0, x_127);
lean_ctor_set(x_138, 1, x_128);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_138, 3, x_129);
lean_ctor_set(x_138, 4, x_130);
lean_ctor_set(x_138, 5, x_131);
if (lean_is_scalar(x_33)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_33;
 lean_ctor_set_tag(x_139, 1);
}
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_140 = lean_ctor_get(x_124, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_123, 0);
lean_inc(x_141);
lean_dec(x_123);
x_142 = lean_ctor_get(x_124, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_124, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_124, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_124, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_124, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_147 = x_124;
} else {
 lean_dec_ref(x_124);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_140, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_140, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_140, 3);
lean_inc(x_150);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 lean_ctor_release(x_140, 2);
 lean_ctor_release(x_140, 3);
 x_151 = x_140;
} else {
 lean_dec_ref(x_140);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 4, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set(x_152, 2, x_121);
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
if (lean_is_scalar(x_33)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_33;
}
lean_ctor_set(x_154, 0, x_141);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_174 = lean_ctor_get(x_32, 2);
x_175 = lean_ctor_get(x_32, 0);
x_176 = lean_ctor_get(x_32, 1);
x_177 = lean_ctor_get(x_32, 3);
x_178 = lean_ctor_get(x_32, 4);
x_179 = lean_ctor_get(x_32, 5);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_174);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_32);
x_180 = lean_ctor_get(x_174, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_174, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_174, 3);
lean_inc(x_183);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 x_184 = x_174;
} else {
 lean_dec_ref(x_174);
 x_184 = lean_box(0);
}
x_218 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_184)) {
 x_219 = lean_alloc_ctor(0, 4, 0);
} else {
 x_219 = x_184;
}
lean_ctor_set(x_219, 0, x_180);
lean_ctor_set(x_219, 1, x_181);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_183);
x_220 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_220, 0, x_175);
lean_ctor_set(x_220, 1, x_176);
lean_ctor_set(x_220, 2, x_219);
lean_ctor_set(x_220, 3, x_177);
lean_ctor_set(x_220, 4, x_178);
lean_ctor_set(x_220, 5, x_179);
x_221 = lean_ctor_get(x_12, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_12, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_12, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_12, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_12, 4);
lean_inc(x_225);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_226 = x_12;
} else {
 lean_dec_ref(x_12);
 x_226 = lean_box(0);
}
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_34);
lean_ctor_set(x_227, 1, x_21);
x_228 = lean_array_push(x_223, x_227);
if (lean_is_scalar(x_226)) {
 x_229 = lean_alloc_ctor(0, 5, 0);
} else {
 x_229 = x_226;
}
lean_ctor_set(x_229, 0, x_221);
lean_ctor_set(x_229, 1, x_222);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_224);
lean_ctor_set(x_229, 4, x_225);
x_230 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_229, x_220);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_231);
x_185 = x_233;
x_186 = x_232;
goto block_217;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_230, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_230, 1);
lean_inc(x_235);
lean_dec(x_230);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_234);
x_185 = x_236;
x_186 = x_235;
goto block_217;
}
block_217:
{
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_187 = lean_ctor_get(x_186, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 x_194 = x_186;
} else {
 lean_dec_ref(x_186);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_187, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_187, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_187, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_198 = x_187;
} else {
 lean_dec_ref(x_187);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 4, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_195);
lean_ctor_set(x_199, 1, x_196);
lean_ctor_set(x_199, 2, x_182);
lean_ctor_set(x_199, 3, x_197);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_194;
}
lean_ctor_set(x_200, 0, x_189);
lean_ctor_set(x_200, 1, x_190);
lean_ctor_set(x_200, 2, x_199);
lean_ctor_set(x_200, 3, x_191);
lean_ctor_set(x_200, 4, x_192);
lean_ctor_set(x_200, 5, x_193);
if (lean_is_scalar(x_33)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_33;
 lean_ctor_set_tag(x_201, 1);
}
lean_ctor_set(x_201, 0, x_188);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_202 = lean_ctor_get(x_186, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_185, 0);
lean_inc(x_203);
lean_dec(x_185);
x_204 = lean_ctor_get(x_186, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_186, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_186, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_186, 4);
lean_inc(x_207);
x_208 = lean_ctor_get(x_186, 5);
lean_inc(x_208);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 x_209 = x_186;
} else {
 lean_dec_ref(x_186);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_202, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_202, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_202, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 x_213 = x_202;
} else {
 lean_dec_ref(x_202);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 4, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_210);
lean_ctor_set(x_214, 1, x_211);
lean_ctor_set(x_214, 2, x_182);
lean_ctor_set(x_214, 3, x_212);
if (lean_is_scalar(x_209)) {
 x_215 = lean_alloc_ctor(0, 6, 0);
} else {
 x_215 = x_209;
}
lean_ctor_set(x_215, 0, x_204);
lean_ctor_set(x_215, 1, x_205);
lean_ctor_set(x_215, 2, x_214);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set(x_215, 4, x_207);
lean_ctor_set(x_215, 5, x_208);
if (lean_is_scalar(x_33)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_33;
}
lean_ctor_set(x_216, 0, x_203);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
default: 
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_26, 1);
lean_inc(x_237);
lean_dec(x_26);
lean_inc(x_12);
x_238 = l_Lean_Meta_isClassExpensive___main(x_25, x_12, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_21);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_11, x_241);
lean_dec(x_11);
x_11 = x_242;
x_13 = x_240;
goto _start;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_244 = lean_ctor_get(x_238, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_245 = x_238;
} else {
 lean_dec_ref(x_238);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_239, 0);
lean_inc(x_246);
lean_dec(x_239);
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_nat_add(x_11, x_247);
lean_dec(x_11);
x_249 = !lean_is_exclusive(x_244);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_244, 2);
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_304; uint8_t x_305; 
x_252 = lean_ctor_get(x_250, 2);
x_304 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_250, 2, x_304);
x_305 = !lean_is_exclusive(x_12);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_12, 2);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_246);
lean_ctor_set(x_307, 1, x_21);
x_308 = lean_array_push(x_306, x_307);
lean_ctor_set(x_12, 2, x_308);
x_309 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_248, x_12, x_244);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_310);
x_253 = x_312;
x_254 = x_311;
goto block_303;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_309, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_309, 1);
lean_inc(x_314);
lean_dec(x_309);
x_315 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_315, 0, x_313);
x_253 = x_315;
x_254 = x_314;
goto block_303;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_316 = lean_ctor_get(x_12, 0);
x_317 = lean_ctor_get(x_12, 1);
x_318 = lean_ctor_get(x_12, 2);
x_319 = lean_ctor_get(x_12, 3);
x_320 = lean_ctor_get(x_12, 4);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_12);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_246);
lean_ctor_set(x_321, 1, x_21);
x_322 = lean_array_push(x_318, x_321);
x_323 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set(x_323, 4, x_320);
x_324 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_248, x_323, x_244);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_325);
x_253 = x_327;
x_254 = x_326;
goto block_303;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_324, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_324, 1);
lean_inc(x_329);
lean_dec(x_324);
x_330 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_330, 0, x_328);
x_253 = x_330;
x_254 = x_329;
goto block_303;
}
}
block_303:
{
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_254, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
lean_dec(x_253);
x_257 = !lean_is_exclusive(x_254);
if (x_257 == 0)
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_254, 2);
lean_dec(x_258);
x_259 = !lean_is_exclusive(x_255);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_255, 2);
lean_dec(x_260);
lean_ctor_set(x_255, 2, x_252);
if (lean_is_scalar(x_245)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_245;
 lean_ctor_set_tag(x_261, 1);
}
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_254);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_262 = lean_ctor_get(x_255, 0);
x_263 = lean_ctor_get(x_255, 1);
x_264 = lean_ctor_get(x_255, 3);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_255);
x_265 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
lean_ctor_set(x_265, 2, x_252);
lean_ctor_set(x_265, 3, x_264);
lean_ctor_set(x_254, 2, x_265);
if (lean_is_scalar(x_245)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_245;
 lean_ctor_set_tag(x_266, 1);
}
lean_ctor_set(x_266, 0, x_256);
lean_ctor_set(x_266, 1, x_254);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_267 = lean_ctor_get(x_254, 0);
x_268 = lean_ctor_get(x_254, 1);
x_269 = lean_ctor_get(x_254, 3);
x_270 = lean_ctor_get(x_254, 4);
x_271 = lean_ctor_get(x_254, 5);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_254);
x_272 = lean_ctor_get(x_255, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_255, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_255, 3);
lean_inc(x_274);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 lean_ctor_release(x_255, 3);
 x_275 = x_255;
} else {
 lean_dec_ref(x_255);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 4, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_272);
lean_ctor_set(x_276, 1, x_273);
lean_ctor_set(x_276, 2, x_252);
lean_ctor_set(x_276, 3, x_274);
x_277 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_277, 0, x_267);
lean_ctor_set(x_277, 1, x_268);
lean_ctor_set(x_277, 2, x_276);
lean_ctor_set(x_277, 3, x_269);
lean_ctor_set(x_277, 4, x_270);
lean_ctor_set(x_277, 5, x_271);
if (lean_is_scalar(x_245)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_245;
 lean_ctor_set_tag(x_278, 1);
}
lean_ctor_set(x_278, 0, x_256);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_279 = lean_ctor_get(x_254, 2);
lean_inc(x_279);
x_280 = lean_ctor_get(x_253, 0);
lean_inc(x_280);
lean_dec(x_253);
x_281 = !lean_is_exclusive(x_254);
if (x_281 == 0)
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_254, 2);
lean_dec(x_282);
x_283 = !lean_is_exclusive(x_279);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_279, 2);
lean_dec(x_284);
lean_ctor_set(x_279, 2, x_252);
if (lean_is_scalar(x_245)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_245;
}
lean_ctor_set(x_285, 0, x_280);
lean_ctor_set(x_285, 1, x_254);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_279, 0);
x_287 = lean_ctor_get(x_279, 1);
x_288 = lean_ctor_get(x_279, 3);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_279);
x_289 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
lean_ctor_set(x_289, 2, x_252);
lean_ctor_set(x_289, 3, x_288);
lean_ctor_set(x_254, 2, x_289);
if (lean_is_scalar(x_245)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_245;
}
lean_ctor_set(x_290, 0, x_280);
lean_ctor_set(x_290, 1, x_254);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_291 = lean_ctor_get(x_254, 0);
x_292 = lean_ctor_get(x_254, 1);
x_293 = lean_ctor_get(x_254, 3);
x_294 = lean_ctor_get(x_254, 4);
x_295 = lean_ctor_get(x_254, 5);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_254);
x_296 = lean_ctor_get(x_279, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_279, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_279, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 x_299 = x_279;
} else {
 lean_dec_ref(x_279);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(0, 4, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_297);
lean_ctor_set(x_300, 2, x_252);
lean_ctor_set(x_300, 3, x_298);
x_301 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_301, 0, x_291);
lean_ctor_set(x_301, 1, x_292);
lean_ctor_set(x_301, 2, x_300);
lean_ctor_set(x_301, 3, x_293);
lean_ctor_set(x_301, 4, x_294);
lean_ctor_set(x_301, 5, x_295);
if (lean_is_scalar(x_245)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_245;
}
lean_ctor_set(x_302, 0, x_280);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_331 = lean_ctor_get(x_250, 0);
x_332 = lean_ctor_get(x_250, 1);
x_333 = lean_ctor_get(x_250, 2);
x_334 = lean_ctor_get(x_250, 3);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_250);
x_368 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_369 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_369, 0, x_331);
lean_ctor_set(x_369, 1, x_332);
lean_ctor_set(x_369, 2, x_368);
lean_ctor_set(x_369, 3, x_334);
lean_ctor_set(x_244, 2, x_369);
x_370 = lean_ctor_get(x_12, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_12, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_12, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_12, 3);
lean_inc(x_373);
x_374 = lean_ctor_get(x_12, 4);
lean_inc(x_374);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_375 = x_12;
} else {
 lean_dec_ref(x_12);
 x_375 = lean_box(0);
}
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_246);
lean_ctor_set(x_376, 1, x_21);
x_377 = lean_array_push(x_372, x_376);
if (lean_is_scalar(x_375)) {
 x_378 = lean_alloc_ctor(0, 5, 0);
} else {
 x_378 = x_375;
}
lean_ctor_set(x_378, 0, x_370);
lean_ctor_set(x_378, 1, x_371);
lean_ctor_set(x_378, 2, x_377);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set(x_378, 4, x_374);
x_379 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_248, x_378, x_244);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_380);
x_335 = x_382;
x_336 = x_381;
goto block_367;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_379, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_379, 1);
lean_inc(x_384);
lean_dec(x_379);
x_385 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_385, 0, x_383);
x_335 = x_385;
x_336 = x_384;
goto block_367;
}
block_367:
{
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_337 = lean_ctor_get(x_336, 2);
lean_inc(x_337);
x_338 = lean_ctor_get(x_335, 0);
lean_inc(x_338);
lean_dec(x_335);
x_339 = lean_ctor_get(x_336, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_336, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_336, 3);
lean_inc(x_341);
x_342 = lean_ctor_get(x_336, 4);
lean_inc(x_342);
x_343 = lean_ctor_get(x_336, 5);
lean_inc(x_343);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 lean_ctor_release(x_336, 4);
 lean_ctor_release(x_336, 5);
 x_344 = x_336;
} else {
 lean_dec_ref(x_336);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_337, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_337, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_337, 3);
lean_inc(x_347);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_348 = x_337;
} else {
 lean_dec_ref(x_337);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 4, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_345);
lean_ctor_set(x_349, 1, x_346);
lean_ctor_set(x_349, 2, x_333);
lean_ctor_set(x_349, 3, x_347);
if (lean_is_scalar(x_344)) {
 x_350 = lean_alloc_ctor(0, 6, 0);
} else {
 x_350 = x_344;
}
lean_ctor_set(x_350, 0, x_339);
lean_ctor_set(x_350, 1, x_340);
lean_ctor_set(x_350, 2, x_349);
lean_ctor_set(x_350, 3, x_341);
lean_ctor_set(x_350, 4, x_342);
lean_ctor_set(x_350, 5, x_343);
if (lean_is_scalar(x_245)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_245;
 lean_ctor_set_tag(x_351, 1);
}
lean_ctor_set(x_351, 0, x_338);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_352 = lean_ctor_get(x_336, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_335, 0);
lean_inc(x_353);
lean_dec(x_335);
x_354 = lean_ctor_get(x_336, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_336, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_336, 3);
lean_inc(x_356);
x_357 = lean_ctor_get(x_336, 4);
lean_inc(x_357);
x_358 = lean_ctor_get(x_336, 5);
lean_inc(x_358);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 lean_ctor_release(x_336, 4);
 lean_ctor_release(x_336, 5);
 x_359 = x_336;
} else {
 lean_dec_ref(x_336);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_352, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_352, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_352, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_363 = x_352;
} else {
 lean_dec_ref(x_352);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 4, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_360);
lean_ctor_set(x_364, 1, x_361);
lean_ctor_set(x_364, 2, x_333);
lean_ctor_set(x_364, 3, x_362);
if (lean_is_scalar(x_359)) {
 x_365 = lean_alloc_ctor(0, 6, 0);
} else {
 x_365 = x_359;
}
lean_ctor_set(x_365, 0, x_354);
lean_ctor_set(x_365, 1, x_355);
lean_ctor_set(x_365, 2, x_364);
lean_ctor_set(x_365, 3, x_356);
lean_ctor_set(x_365, 4, x_357);
lean_ctor_set(x_365, 5, x_358);
if (lean_is_scalar(x_245)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_245;
}
lean_ctor_set(x_366, 0, x_353);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_386 = lean_ctor_get(x_244, 2);
x_387 = lean_ctor_get(x_244, 0);
x_388 = lean_ctor_get(x_244, 1);
x_389 = lean_ctor_get(x_244, 3);
x_390 = lean_ctor_get(x_244, 4);
x_391 = lean_ctor_get(x_244, 5);
lean_inc(x_391);
lean_inc(x_390);
lean_inc(x_389);
lean_inc(x_386);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_244);
x_392 = lean_ctor_get(x_386, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_386, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_386, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_386, 3);
lean_inc(x_395);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 lean_ctor_release(x_386, 2);
 lean_ctor_release(x_386, 3);
 x_396 = x_386;
} else {
 lean_dec_ref(x_386);
 x_396 = lean_box(0);
}
x_430 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_396)) {
 x_431 = lean_alloc_ctor(0, 4, 0);
} else {
 x_431 = x_396;
}
lean_ctor_set(x_431, 0, x_392);
lean_ctor_set(x_431, 1, x_393);
lean_ctor_set(x_431, 2, x_430);
lean_ctor_set(x_431, 3, x_395);
x_432 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_432, 0, x_387);
lean_ctor_set(x_432, 1, x_388);
lean_ctor_set(x_432, 2, x_431);
lean_ctor_set(x_432, 3, x_389);
lean_ctor_set(x_432, 4, x_390);
lean_ctor_set(x_432, 5, x_391);
x_433 = lean_ctor_get(x_12, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_12, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_12, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_12, 3);
lean_inc(x_436);
x_437 = lean_ctor_get(x_12, 4);
lean_inc(x_437);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_438 = x_12;
} else {
 lean_dec_ref(x_12);
 x_438 = lean_box(0);
}
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_246);
lean_ctor_set(x_439, 1, x_21);
x_440 = lean_array_push(x_435, x_439);
if (lean_is_scalar(x_438)) {
 x_441 = lean_alloc_ctor(0, 5, 0);
} else {
 x_441 = x_438;
}
lean_ctor_set(x_441, 0, x_433);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_440);
lean_ctor_set(x_441, 3, x_436);
lean_ctor_set(x_441, 4, x_437);
x_442 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_248, x_441, x_432);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_443);
x_397 = x_445;
x_398 = x_444;
goto block_429;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_442, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_442, 1);
lean_inc(x_447);
lean_dec(x_442);
x_448 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_448, 0, x_446);
x_397 = x_448;
x_398 = x_447;
goto block_429;
}
block_429:
{
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_399 = lean_ctor_get(x_398, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_397, 0);
lean_inc(x_400);
lean_dec(x_397);
x_401 = lean_ctor_get(x_398, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_398, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_398, 3);
lean_inc(x_403);
x_404 = lean_ctor_get(x_398, 4);
lean_inc(x_404);
x_405 = lean_ctor_get(x_398, 5);
lean_inc(x_405);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 lean_ctor_release(x_398, 2);
 lean_ctor_release(x_398, 3);
 lean_ctor_release(x_398, 4);
 lean_ctor_release(x_398, 5);
 x_406 = x_398;
} else {
 lean_dec_ref(x_398);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_399, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_399, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_399, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 lean_ctor_release(x_399, 2);
 lean_ctor_release(x_399, 3);
 x_410 = x_399;
} else {
 lean_dec_ref(x_399);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(0, 4, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_407);
lean_ctor_set(x_411, 1, x_408);
lean_ctor_set(x_411, 2, x_394);
lean_ctor_set(x_411, 3, x_409);
if (lean_is_scalar(x_406)) {
 x_412 = lean_alloc_ctor(0, 6, 0);
} else {
 x_412 = x_406;
}
lean_ctor_set(x_412, 0, x_401);
lean_ctor_set(x_412, 1, x_402);
lean_ctor_set(x_412, 2, x_411);
lean_ctor_set(x_412, 3, x_403);
lean_ctor_set(x_412, 4, x_404);
lean_ctor_set(x_412, 5, x_405);
if (lean_is_scalar(x_245)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_245;
 lean_ctor_set_tag(x_413, 1);
}
lean_ctor_set(x_413, 0, x_400);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_414 = lean_ctor_get(x_398, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_397, 0);
lean_inc(x_415);
lean_dec(x_397);
x_416 = lean_ctor_get(x_398, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_398, 1);
lean_inc(x_417);
x_418 = lean_ctor_get(x_398, 3);
lean_inc(x_418);
x_419 = lean_ctor_get(x_398, 4);
lean_inc(x_419);
x_420 = lean_ctor_get(x_398, 5);
lean_inc(x_420);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 lean_ctor_release(x_398, 2);
 lean_ctor_release(x_398, 3);
 lean_ctor_release(x_398, 4);
 lean_ctor_release(x_398, 5);
 x_421 = x_398;
} else {
 lean_dec_ref(x_398);
 x_421 = lean_box(0);
}
x_422 = lean_ctor_get(x_414, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_414, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_414, 3);
lean_inc(x_424);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 lean_ctor_release(x_414, 2);
 lean_ctor_release(x_414, 3);
 x_425 = x_414;
} else {
 lean_dec_ref(x_414);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(0, 4, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_422);
lean_ctor_set(x_426, 1, x_423);
lean_ctor_set(x_426, 2, x_394);
lean_ctor_set(x_426, 3, x_424);
if (lean_is_scalar(x_421)) {
 x_427 = lean_alloc_ctor(0, 6, 0);
} else {
 x_427 = x_421;
}
lean_ctor_set(x_427, 0, x_416);
lean_ctor_set(x_427, 1, x_417);
lean_ctor_set(x_427, 2, x_426);
lean_ctor_set(x_427, 3, x_418);
lean_ctor_set(x_427, 4, x_419);
lean_ctor_set(x_427, 5, x_420);
if (lean_is_scalar(x_245)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_245;
}
lean_ctor_set(x_428, 0, x_415);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
}
}
else
{
uint8_t x_449; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_449 = !lean_is_exclusive(x_238);
if (x_449 == 0)
{
return x_238;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_238, 0);
x_451 = lean_ctor_get(x_238, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_238);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
return x_452;
}
}
}
}
}
else
{
uint8_t x_453; 
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
x_453 = !lean_is_exclusive(x_26);
if (x_453 == 0)
{
return x_26;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_26, 0);
x_455 = lean_ctor_get(x_26, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_26);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
else
{
uint8_t x_457; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_457 = !lean_is_exclusive(x_22);
if (x_457 == 0)
{
return x_22;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_22, 0);
x_459 = lean_ctor_get(x_22, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_22);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
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
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l_Lean_Meta_getMVarType(x_1, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = l_Array_empty___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_3, x_1, x_4, x_13, x_14, x_15, x_5, x_11, x_6, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = x_20;
x_22 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_15, x_21);
x_23 = x_22;
lean_ctor_set(x_18, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = x_24;
x_27 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_15, x_26);
x_28 = x_27;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
x_35 = x_32;
x_36 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_15, x_35);
x_37 = x_36;
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_10;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_8 = lean_box(x_1);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1___boxed), 7, 5);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_4);
x_10 = l_Lean_Meta_getMVarDecl(x_2, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 4);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_withLocalContext___rarg(x_13, x_14, x_9, x_5, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
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
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
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
l_Lean_Meta_mkAuxName___closed__1 = _init_l_Lean_Meta_mkAuxName___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxName___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
