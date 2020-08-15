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
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkThunk___closed__1;
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
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_13 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_13, x_14, x_9, x_10);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_88; uint8_t x_89; 
x_32 = lean_ctor_get(x_30, 2);
x_88 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_30, 2, x_88);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_6, 2);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_26);
lean_ctor_set(x_91, 1, x_13);
x_92 = lean_array_push(x_90, x_91);
lean_ctor_set(x_6, 2, x_92);
x_93 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_28, x_6, x_24);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_94);
x_33 = x_96;
x_34 = x_95;
goto block_87;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_97);
x_33 = x_99;
x_34 = x_98;
goto block_87;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_6, 0);
x_101 = lean_ctor_get(x_6, 1);
x_102 = lean_ctor_get(x_6, 2);
x_103 = lean_ctor_get(x_6, 3);
x_104 = lean_ctor_get(x_6, 4);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_6);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_26);
lean_ctor_set(x_105, 1, x_13);
x_106 = lean_array_push(x_102, x_105);
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_101);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_103);
lean_ctor_set(x_107, 4, x_104);
x_108 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_28, x_107, x_24);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_109);
x_33 = x_111;
x_34 = x_110;
goto block_87;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_112);
x_33 = x_114;
x_34 = x_113;
goto block_87;
}
}
block_87:
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
x_44 = lean_ctor_get(x_35, 3);
x_45 = lean_ctor_get(x_35, 4);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_32);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_34, 2, x_46);
if (lean_is_scalar(x_25)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_25;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_34);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
x_50 = lean_ctor_get(x_34, 3);
x_51 = lean_ctor_get(x_34, 4);
x_52 = lean_ctor_get(x_34, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_35, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_35, 4);
lean_inc(x_56);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 lean_ctor_release(x_35, 4);
 x_57 = x_35;
} else {
 lean_dec_ref(x_35);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_32);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_49);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_50);
lean_ctor_set(x_59, 4, x_51);
lean_ctor_set(x_59, 5, x_52);
if (lean_is_scalar(x_25)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_25;
 lean_ctor_set_tag(x_60, 1);
}
lean_ctor_set(x_60, 0, x_36);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_34, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_33, 0);
lean_inc(x_62);
lean_dec(x_33);
x_63 = !lean_is_exclusive(x_34);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_34, 2);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_61, 2);
lean_dec(x_66);
lean_ctor_set(x_61, 2, x_32);
if (lean_is_scalar(x_25)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_25;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_34);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_61, 0);
x_69 = lean_ctor_get(x_61, 1);
x_70 = lean_ctor_get(x_61, 3);
x_71 = lean_ctor_get(x_61, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_61);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_32);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set(x_34, 2, x_72);
if (lean_is_scalar(x_25)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_25;
}
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_34);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_74 = lean_ctor_get(x_34, 0);
x_75 = lean_ctor_get(x_34, 1);
x_76 = lean_ctor_get(x_34, 3);
x_77 = lean_ctor_get(x_34, 4);
x_78 = lean_ctor_get(x_34, 5);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_34);
x_79 = lean_ctor_get(x_61, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_61, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_61, 4);
lean_inc(x_82);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 x_83 = x_61;
} else {
 lean_dec_ref(x_61);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 5, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_32);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_75);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_76);
lean_ctor_set(x_85, 4, x_77);
lean_ctor_set(x_85, 5, x_78);
if (lean_is_scalar(x_25)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_25;
}
lean_ctor_set(x_86, 0, x_62);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_115 = lean_ctor_get(x_30, 0);
x_116 = lean_ctor_get(x_30, 1);
x_117 = lean_ctor_get(x_30, 2);
x_118 = lean_ctor_get(x_30, 3);
x_119 = lean_ctor_get(x_30, 4);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_30);
x_155 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_115);
lean_ctor_set(x_156, 1, x_116);
lean_ctor_set(x_156, 2, x_155);
lean_ctor_set(x_156, 3, x_118);
lean_ctor_set(x_156, 4, x_119);
lean_ctor_set(x_24, 2, x_156);
x_157 = lean_ctor_get(x_6, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_6, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_6, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_6, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_6, 4);
lean_inc(x_161);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_162 = x_6;
} else {
 lean_dec_ref(x_6);
 x_162 = lean_box(0);
}
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_26);
lean_ctor_set(x_163, 1, x_13);
x_164 = lean_array_push(x_159, x_163);
if (lean_is_scalar(x_162)) {
 x_165 = lean_alloc_ctor(0, 5, 0);
} else {
 x_165 = x_162;
}
lean_ctor_set(x_165, 0, x_157);
lean_ctor_set(x_165, 1, x_158);
lean_ctor_set(x_165, 2, x_164);
lean_ctor_set(x_165, 3, x_160);
lean_ctor_set(x_165, 4, x_161);
x_166 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_28, x_165, x_24);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_167);
x_120 = x_169;
x_121 = x_168;
goto block_154;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_166, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_170);
x_120 = x_172;
x_121 = x_171;
goto block_154;
}
block_154:
{
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_122 = lean_ctor_get(x_121, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_121, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_121, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 5);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 lean_ctor_release(x_121, 5);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_122, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_122, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_122, 4);
lean_inc(x_133);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 x_134 = x_122;
} else {
 lean_dec_ref(x_122);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 5, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_117);
lean_ctor_set(x_135, 3, x_132);
lean_ctor_set(x_135, 4, x_133);
if (lean_is_scalar(x_129)) {
 x_136 = lean_alloc_ctor(0, 6, 0);
} else {
 x_136 = x_129;
}
lean_ctor_set(x_136, 0, x_124);
lean_ctor_set(x_136, 1, x_125);
lean_ctor_set(x_136, 2, x_135);
lean_ctor_set(x_136, 3, x_126);
lean_ctor_set(x_136, 4, x_127);
lean_ctor_set(x_136, 5, x_128);
if (lean_is_scalar(x_25)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_25;
 lean_ctor_set_tag(x_137, 1);
}
lean_ctor_set(x_137, 0, x_123);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_138 = lean_ctor_get(x_121, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_120, 0);
lean_inc(x_139);
lean_dec(x_120);
x_140 = lean_ctor_get(x_121, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_121, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_121, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_121, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_121, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 lean_ctor_release(x_121, 5);
 x_145 = x_121;
} else {
 lean_dec_ref(x_121);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_138, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_138, 4);
lean_inc(x_149);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 lean_ctor_release(x_138, 4);
 x_150 = x_138;
} else {
 lean_dec_ref(x_138);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 5, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set(x_151, 1, x_147);
lean_ctor_set(x_151, 2, x_117);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set(x_151, 4, x_149);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(0, 6, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_140);
lean_ctor_set(x_152, 1, x_141);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_142);
lean_ctor_set(x_152, 4, x_143);
lean_ctor_set(x_152, 5, x_144);
if (lean_is_scalar(x_25)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_25;
}
lean_ctor_set(x_153, 0, x_139);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_173 = lean_ctor_get(x_24, 2);
x_174 = lean_ctor_get(x_24, 0);
x_175 = lean_ctor_get(x_24, 1);
x_176 = lean_ctor_get(x_24, 3);
x_177 = lean_ctor_get(x_24, 4);
x_178 = lean_ctor_get(x_24, 5);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_173);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_24);
x_179 = lean_ctor_get(x_173, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_173, 2);
lean_inc(x_181);
x_182 = lean_ctor_get(x_173, 3);
lean_inc(x_182);
x_183 = lean_ctor_get(x_173, 4);
lean_inc(x_183);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 lean_ctor_release(x_173, 3);
 lean_ctor_release(x_173, 4);
 x_184 = x_173;
} else {
 lean_dec_ref(x_173);
 x_184 = lean_box(0);
}
x_220 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_184)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_184;
}
lean_ctor_set(x_221, 0, x_179);
lean_ctor_set(x_221, 1, x_180);
lean_ctor_set(x_221, 2, x_220);
lean_ctor_set(x_221, 3, x_182);
lean_ctor_set(x_221, 4, x_183);
x_222 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_222, 0, x_174);
lean_ctor_set(x_222, 1, x_175);
lean_ctor_set(x_222, 2, x_221);
lean_ctor_set(x_222, 3, x_176);
lean_ctor_set(x_222, 4, x_177);
lean_ctor_set(x_222, 5, x_178);
x_223 = lean_ctor_get(x_6, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_6, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_6, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_6, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_6, 4);
lean_inc(x_227);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_228 = x_6;
} else {
 lean_dec_ref(x_6);
 x_228 = lean_box(0);
}
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_26);
lean_ctor_set(x_229, 1, x_13);
x_230 = lean_array_push(x_225, x_229);
if (lean_is_scalar(x_228)) {
 x_231 = lean_alloc_ctor(0, 5, 0);
} else {
 x_231 = x_228;
}
lean_ctor_set(x_231, 0, x_223);
lean_ctor_set(x_231, 1, x_224);
lean_ctor_set(x_231, 2, x_230);
lean_ctor_set(x_231, 3, x_226);
lean_ctor_set(x_231, 4, x_227);
x_232 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_28, x_231, x_222);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_233);
x_185 = x_235;
x_186 = x_234;
goto block_219;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_232, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_232, 1);
lean_inc(x_237);
lean_dec(x_232);
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_236);
x_185 = x_238;
x_186 = x_237;
goto block_219;
}
block_219:
{
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
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
x_198 = lean_ctor_get(x_187, 4);
lean_inc(x_198);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 lean_ctor_release(x_187, 4);
 x_199 = x_187;
} else {
 lean_dec_ref(x_187);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 5, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_196);
lean_ctor_set(x_200, 2, x_181);
lean_ctor_set(x_200, 3, x_197);
lean_ctor_set(x_200, 4, x_198);
if (lean_is_scalar(x_194)) {
 x_201 = lean_alloc_ctor(0, 6, 0);
} else {
 x_201 = x_194;
}
lean_ctor_set(x_201, 0, x_189);
lean_ctor_set(x_201, 1, x_190);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_191);
lean_ctor_set(x_201, 4, x_192);
lean_ctor_set(x_201, 5, x_193);
if (lean_is_scalar(x_25)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_25;
 lean_ctor_set_tag(x_202, 1);
}
lean_ctor_set(x_202, 0, x_188);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_203 = lean_ctor_get(x_186, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_185, 0);
lean_inc(x_204);
lean_dec(x_185);
x_205 = lean_ctor_get(x_186, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_186, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_186, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_186, 4);
lean_inc(x_208);
x_209 = lean_ctor_get(x_186, 5);
lean_inc(x_209);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 x_210 = x_186;
} else {
 lean_dec_ref(x_186);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_203, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_203, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_203, 3);
lean_inc(x_213);
x_214 = lean_ctor_get(x_203, 4);
lean_inc(x_214);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 lean_ctor_release(x_203, 3);
 lean_ctor_release(x_203, 4);
 x_215 = x_203;
} else {
 lean_dec_ref(x_203);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_212);
lean_ctor_set(x_216, 2, x_181);
lean_ctor_set(x_216, 3, x_213);
lean_ctor_set(x_216, 4, x_214);
if (lean_is_scalar(x_210)) {
 x_217 = lean_alloc_ctor(0, 6, 0);
} else {
 x_217 = x_210;
}
lean_ctor_set(x_217, 0, x_205);
lean_ctor_set(x_217, 1, x_206);
lean_ctor_set(x_217, 2, x_216);
lean_ctor_set(x_217, 3, x_207);
lean_ctor_set(x_217, 4, x_208);
lean_ctor_set(x_217, 5, x_209);
if (lean_is_scalar(x_25)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_25;
}
lean_ctor_set(x_218, 0, x_204);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
default: 
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_18, 1);
lean_inc(x_239);
lean_dec(x_18);
lean_inc(x_6);
x_240 = l_Lean_Meta_isClassExpensive___main(x_17, x_6, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_13);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_unsigned_to_nat(1u);
x_244 = lean_nat_add(x_5, x_243);
lean_dec(x_5);
x_5 = x_244;
x_7 = x_242;
goto _start;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_240, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_247 = x_240;
} else {
 lean_dec_ref(x_240);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_241, 0);
lean_inc(x_248);
lean_dec(x_241);
x_249 = lean_unsigned_to_nat(1u);
x_250 = lean_nat_add(x_5, x_249);
lean_dec(x_5);
x_251 = !lean_is_exclusive(x_246);
if (x_251 == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_246, 2);
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_310; uint8_t x_311; 
x_254 = lean_ctor_get(x_252, 2);
x_310 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_252, 2, x_310);
x_311 = !lean_is_exclusive(x_6);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_6, 2);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_248);
lean_ctor_set(x_313, 1, x_13);
x_314 = lean_array_push(x_312, x_313);
lean_ctor_set(x_6, 2, x_314);
x_315 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_250, x_6, x_246);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_316);
x_255 = x_318;
x_256 = x_317;
goto block_309;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_315, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_315, 1);
lean_inc(x_320);
lean_dec(x_315);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_319);
x_255 = x_321;
x_256 = x_320;
goto block_309;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_322 = lean_ctor_get(x_6, 0);
x_323 = lean_ctor_get(x_6, 1);
x_324 = lean_ctor_get(x_6, 2);
x_325 = lean_ctor_get(x_6, 3);
x_326 = lean_ctor_get(x_6, 4);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_6);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_248);
lean_ctor_set(x_327, 1, x_13);
x_328 = lean_array_push(x_324, x_327);
x_329 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_323);
lean_ctor_set(x_329, 2, x_328);
lean_ctor_set(x_329, 3, x_325);
lean_ctor_set(x_329, 4, x_326);
x_330 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_250, x_329, x_246);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_331);
x_255 = x_333;
x_256 = x_332;
goto block_309;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_330, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_330, 1);
lean_inc(x_335);
lean_dec(x_330);
x_336 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_336, 0, x_334);
x_255 = x_336;
x_256 = x_335;
goto block_309;
}
}
block_309:
{
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_ctor_get(x_256, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
lean_dec(x_255);
x_259 = !lean_is_exclusive(x_256);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_256, 2);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_257);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_257, 2);
lean_dec(x_262);
lean_ctor_set(x_257, 2, x_254);
if (lean_is_scalar(x_247)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_247;
 lean_ctor_set_tag(x_263, 1);
}
lean_ctor_set(x_263, 0, x_258);
lean_ctor_set(x_263, 1, x_256);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = lean_ctor_get(x_257, 0);
x_265 = lean_ctor_get(x_257, 1);
x_266 = lean_ctor_get(x_257, 3);
x_267 = lean_ctor_get(x_257, 4);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_257);
x_268 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_265);
lean_ctor_set(x_268, 2, x_254);
lean_ctor_set(x_268, 3, x_266);
lean_ctor_set(x_268, 4, x_267);
lean_ctor_set(x_256, 2, x_268);
if (lean_is_scalar(x_247)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_247;
 lean_ctor_set_tag(x_269, 1);
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_256);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_270 = lean_ctor_get(x_256, 0);
x_271 = lean_ctor_get(x_256, 1);
x_272 = lean_ctor_get(x_256, 3);
x_273 = lean_ctor_get(x_256, 4);
x_274 = lean_ctor_get(x_256, 5);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_256);
x_275 = lean_ctor_get(x_257, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_257, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_257, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_257, 4);
lean_inc(x_278);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 lean_ctor_release(x_257, 4);
 x_279 = x_257;
} else {
 lean_dec_ref(x_257);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(0, 5, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_275);
lean_ctor_set(x_280, 1, x_276);
lean_ctor_set(x_280, 2, x_254);
lean_ctor_set(x_280, 3, x_277);
lean_ctor_set(x_280, 4, x_278);
x_281 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_281, 0, x_270);
lean_ctor_set(x_281, 1, x_271);
lean_ctor_set(x_281, 2, x_280);
lean_ctor_set(x_281, 3, x_272);
lean_ctor_set(x_281, 4, x_273);
lean_ctor_set(x_281, 5, x_274);
if (lean_is_scalar(x_247)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_247;
 lean_ctor_set_tag(x_282, 1);
}
lean_ctor_set(x_282, 0, x_258);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_256, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_255, 0);
lean_inc(x_284);
lean_dec(x_255);
x_285 = !lean_is_exclusive(x_256);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_256, 2);
lean_dec(x_286);
x_287 = !lean_is_exclusive(x_283);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_283, 2);
lean_dec(x_288);
lean_ctor_set(x_283, 2, x_254);
if (lean_is_scalar(x_247)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_247;
}
lean_ctor_set(x_289, 0, x_284);
lean_ctor_set(x_289, 1, x_256);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_290 = lean_ctor_get(x_283, 0);
x_291 = lean_ctor_get(x_283, 1);
x_292 = lean_ctor_get(x_283, 3);
x_293 = lean_ctor_get(x_283, 4);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_283);
x_294 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_294, 0, x_290);
lean_ctor_set(x_294, 1, x_291);
lean_ctor_set(x_294, 2, x_254);
lean_ctor_set(x_294, 3, x_292);
lean_ctor_set(x_294, 4, x_293);
lean_ctor_set(x_256, 2, x_294);
if (lean_is_scalar(x_247)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_247;
}
lean_ctor_set(x_295, 0, x_284);
lean_ctor_set(x_295, 1, x_256);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_296 = lean_ctor_get(x_256, 0);
x_297 = lean_ctor_get(x_256, 1);
x_298 = lean_ctor_get(x_256, 3);
x_299 = lean_ctor_get(x_256, 4);
x_300 = lean_ctor_get(x_256, 5);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_256);
x_301 = lean_ctor_get(x_283, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_283, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_283, 3);
lean_inc(x_303);
x_304 = lean_ctor_get(x_283, 4);
lean_inc(x_304);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 lean_ctor_release(x_283, 2);
 lean_ctor_release(x_283, 3);
 lean_ctor_release(x_283, 4);
 x_305 = x_283;
} else {
 lean_dec_ref(x_283);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 5, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_301);
lean_ctor_set(x_306, 1, x_302);
lean_ctor_set(x_306, 2, x_254);
lean_ctor_set(x_306, 3, x_303);
lean_ctor_set(x_306, 4, x_304);
x_307 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_307, 0, x_296);
lean_ctor_set(x_307, 1, x_297);
lean_ctor_set(x_307, 2, x_306);
lean_ctor_set(x_307, 3, x_298);
lean_ctor_set(x_307, 4, x_299);
lean_ctor_set(x_307, 5, x_300);
if (lean_is_scalar(x_247)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_247;
}
lean_ctor_set(x_308, 0, x_284);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_337 = lean_ctor_get(x_252, 0);
x_338 = lean_ctor_get(x_252, 1);
x_339 = lean_ctor_get(x_252, 2);
x_340 = lean_ctor_get(x_252, 3);
x_341 = lean_ctor_get(x_252, 4);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_252);
x_377 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_378 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_378, 0, x_337);
lean_ctor_set(x_378, 1, x_338);
lean_ctor_set(x_378, 2, x_377);
lean_ctor_set(x_378, 3, x_340);
lean_ctor_set(x_378, 4, x_341);
lean_ctor_set(x_246, 2, x_378);
x_379 = lean_ctor_get(x_6, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_6, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_6, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_6, 3);
lean_inc(x_382);
x_383 = lean_ctor_get(x_6, 4);
lean_inc(x_383);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_384 = x_6;
} else {
 lean_dec_ref(x_6);
 x_384 = lean_box(0);
}
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_248);
lean_ctor_set(x_385, 1, x_13);
x_386 = lean_array_push(x_381, x_385);
if (lean_is_scalar(x_384)) {
 x_387 = lean_alloc_ctor(0, 5, 0);
} else {
 x_387 = x_384;
}
lean_ctor_set(x_387, 0, x_379);
lean_ctor_set(x_387, 1, x_380);
lean_ctor_set(x_387, 2, x_386);
lean_ctor_set(x_387, 3, x_382);
lean_ctor_set(x_387, 4, x_383);
x_388 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_250, x_387, x_246);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_342 = x_391;
x_343 = x_390;
goto block_376;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_388, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_388, 1);
lean_inc(x_393);
lean_dec(x_388);
x_394 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_394, 0, x_392);
x_342 = x_394;
x_343 = x_393;
goto block_376;
}
block_376:
{
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_344 = lean_ctor_get(x_343, 2);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
lean_dec(x_342);
x_346 = lean_ctor_get(x_343, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_343, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_343, 3);
lean_inc(x_348);
x_349 = lean_ctor_get(x_343, 4);
lean_inc(x_349);
x_350 = lean_ctor_get(x_343, 5);
lean_inc(x_350);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 lean_ctor_release(x_343, 4);
 lean_ctor_release(x_343, 5);
 x_351 = x_343;
} else {
 lean_dec_ref(x_343);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_344, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_344, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_344, 3);
lean_inc(x_354);
x_355 = lean_ctor_get(x_344, 4);
lean_inc(x_355);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 lean_ctor_release(x_344, 2);
 lean_ctor_release(x_344, 3);
 lean_ctor_release(x_344, 4);
 x_356 = x_344;
} else {
 lean_dec_ref(x_344);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 5, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_352);
lean_ctor_set(x_357, 1, x_353);
lean_ctor_set(x_357, 2, x_339);
lean_ctor_set(x_357, 3, x_354);
lean_ctor_set(x_357, 4, x_355);
if (lean_is_scalar(x_351)) {
 x_358 = lean_alloc_ctor(0, 6, 0);
} else {
 x_358 = x_351;
}
lean_ctor_set(x_358, 0, x_346);
lean_ctor_set(x_358, 1, x_347);
lean_ctor_set(x_358, 2, x_357);
lean_ctor_set(x_358, 3, x_348);
lean_ctor_set(x_358, 4, x_349);
lean_ctor_set(x_358, 5, x_350);
if (lean_is_scalar(x_247)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_247;
 lean_ctor_set_tag(x_359, 1);
}
lean_ctor_set(x_359, 0, x_345);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_360 = lean_ctor_get(x_343, 2);
lean_inc(x_360);
x_361 = lean_ctor_get(x_342, 0);
lean_inc(x_361);
lean_dec(x_342);
x_362 = lean_ctor_get(x_343, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_343, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_343, 3);
lean_inc(x_364);
x_365 = lean_ctor_get(x_343, 4);
lean_inc(x_365);
x_366 = lean_ctor_get(x_343, 5);
lean_inc(x_366);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 lean_ctor_release(x_343, 4);
 lean_ctor_release(x_343, 5);
 x_367 = x_343;
} else {
 lean_dec_ref(x_343);
 x_367 = lean_box(0);
}
x_368 = lean_ctor_get(x_360, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_360, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_360, 3);
lean_inc(x_370);
x_371 = lean_ctor_get(x_360, 4);
lean_inc(x_371);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 lean_ctor_release(x_360, 2);
 lean_ctor_release(x_360, 3);
 lean_ctor_release(x_360, 4);
 x_372 = x_360;
} else {
 lean_dec_ref(x_360);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(0, 5, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_368);
lean_ctor_set(x_373, 1, x_369);
lean_ctor_set(x_373, 2, x_339);
lean_ctor_set(x_373, 3, x_370);
lean_ctor_set(x_373, 4, x_371);
if (lean_is_scalar(x_367)) {
 x_374 = lean_alloc_ctor(0, 6, 0);
} else {
 x_374 = x_367;
}
lean_ctor_set(x_374, 0, x_362);
lean_ctor_set(x_374, 1, x_363);
lean_ctor_set(x_374, 2, x_373);
lean_ctor_set(x_374, 3, x_364);
lean_ctor_set(x_374, 4, x_365);
lean_ctor_set(x_374, 5, x_366);
if (lean_is_scalar(x_247)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_247;
}
lean_ctor_set(x_375, 0, x_361);
lean_ctor_set(x_375, 1, x_374);
return x_375;
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_395 = lean_ctor_get(x_246, 2);
x_396 = lean_ctor_get(x_246, 0);
x_397 = lean_ctor_get(x_246, 1);
x_398 = lean_ctor_get(x_246, 3);
x_399 = lean_ctor_get(x_246, 4);
x_400 = lean_ctor_get(x_246, 5);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_395);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_246);
x_401 = lean_ctor_get(x_395, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_395, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_395, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_395, 3);
lean_inc(x_404);
x_405 = lean_ctor_get(x_395, 4);
lean_inc(x_405);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 lean_ctor_release(x_395, 2);
 lean_ctor_release(x_395, 3);
 lean_ctor_release(x_395, 4);
 x_406 = x_395;
} else {
 lean_dec_ref(x_395);
 x_406 = lean_box(0);
}
x_442 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_406)) {
 x_443 = lean_alloc_ctor(0, 5, 0);
} else {
 x_443 = x_406;
}
lean_ctor_set(x_443, 0, x_401);
lean_ctor_set(x_443, 1, x_402);
lean_ctor_set(x_443, 2, x_442);
lean_ctor_set(x_443, 3, x_404);
lean_ctor_set(x_443, 4, x_405);
x_444 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_444, 0, x_396);
lean_ctor_set(x_444, 1, x_397);
lean_ctor_set(x_444, 2, x_443);
lean_ctor_set(x_444, 3, x_398);
lean_ctor_set(x_444, 4, x_399);
lean_ctor_set(x_444, 5, x_400);
x_445 = lean_ctor_get(x_6, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_6, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_6, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_6, 3);
lean_inc(x_448);
x_449 = lean_ctor_get(x_6, 4);
lean_inc(x_449);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_450 = x_6;
} else {
 lean_dec_ref(x_6);
 x_450 = lean_box(0);
}
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_248);
lean_ctor_set(x_451, 1, x_13);
x_452 = lean_array_push(x_447, x_451);
if (lean_is_scalar(x_450)) {
 x_453 = lean_alloc_ctor(0, 5, 0);
} else {
 x_453 = x_450;
}
lean_ctor_set(x_453, 0, x_445);
lean_ctor_set(x_453, 1, x_446);
lean_ctor_set(x_453, 2, x_452);
lean_ctor_set(x_453, 3, x_448);
lean_ctor_set(x_453, 4, x_449);
x_454 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_250, x_453, x_444);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec(x_454);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_455);
x_407 = x_457;
x_408 = x_456;
goto block_441;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_454, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_454, 1);
lean_inc(x_459);
lean_dec(x_454);
x_460 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_460, 0, x_458);
x_407 = x_460;
x_408 = x_459;
goto block_441;
}
block_441:
{
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_409 = lean_ctor_get(x_408, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 0);
lean_inc(x_410);
lean_dec(x_407);
x_411 = lean_ctor_get(x_408, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_408, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_408, 3);
lean_inc(x_413);
x_414 = lean_ctor_get(x_408, 4);
lean_inc(x_414);
x_415 = lean_ctor_get(x_408, 5);
lean_inc(x_415);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 lean_ctor_release(x_408, 2);
 lean_ctor_release(x_408, 3);
 lean_ctor_release(x_408, 4);
 lean_ctor_release(x_408, 5);
 x_416 = x_408;
} else {
 lean_dec_ref(x_408);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_409, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_409, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_409, 3);
lean_inc(x_419);
x_420 = lean_ctor_get(x_409, 4);
lean_inc(x_420);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 lean_ctor_release(x_409, 2);
 lean_ctor_release(x_409, 3);
 lean_ctor_release(x_409, 4);
 x_421 = x_409;
} else {
 lean_dec_ref(x_409);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(0, 5, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_417);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_403);
lean_ctor_set(x_422, 3, x_419);
lean_ctor_set(x_422, 4, x_420);
if (lean_is_scalar(x_416)) {
 x_423 = lean_alloc_ctor(0, 6, 0);
} else {
 x_423 = x_416;
}
lean_ctor_set(x_423, 0, x_411);
lean_ctor_set(x_423, 1, x_412);
lean_ctor_set(x_423, 2, x_422);
lean_ctor_set(x_423, 3, x_413);
lean_ctor_set(x_423, 4, x_414);
lean_ctor_set(x_423, 5, x_415);
if (lean_is_scalar(x_247)) {
 x_424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_424 = x_247;
 lean_ctor_set_tag(x_424, 1);
}
lean_ctor_set(x_424, 0, x_410);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_425 = lean_ctor_get(x_408, 2);
lean_inc(x_425);
x_426 = lean_ctor_get(x_407, 0);
lean_inc(x_426);
lean_dec(x_407);
x_427 = lean_ctor_get(x_408, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_408, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_408, 3);
lean_inc(x_429);
x_430 = lean_ctor_get(x_408, 4);
lean_inc(x_430);
x_431 = lean_ctor_get(x_408, 5);
lean_inc(x_431);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 lean_ctor_release(x_408, 2);
 lean_ctor_release(x_408, 3);
 lean_ctor_release(x_408, 4);
 lean_ctor_release(x_408, 5);
 x_432 = x_408;
} else {
 lean_dec_ref(x_408);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_425, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_425, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_425, 3);
lean_inc(x_435);
x_436 = lean_ctor_get(x_425, 4);
lean_inc(x_436);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 lean_ctor_release(x_425, 4);
 x_437 = x_425;
} else {
 lean_dec_ref(x_425);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(0, 5, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_433);
lean_ctor_set(x_438, 1, x_434);
lean_ctor_set(x_438, 2, x_403);
lean_ctor_set(x_438, 3, x_435);
lean_ctor_set(x_438, 4, x_436);
if (lean_is_scalar(x_432)) {
 x_439 = lean_alloc_ctor(0, 6, 0);
} else {
 x_439 = x_432;
}
lean_ctor_set(x_439, 0, x_427);
lean_ctor_set(x_439, 1, x_428);
lean_ctor_set(x_439, 2, x_438);
lean_ctor_set(x_439, 3, x_429);
lean_ctor_set(x_439, 4, x_430);
lean_ctor_set(x_439, 5, x_431);
if (lean_is_scalar(x_247)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_247;
}
lean_ctor_set(x_440, 0, x_426);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_461 = !lean_is_exclusive(x_240);
if (x_461 == 0)
{
return x_240;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_240, 0);
x_463 = lean_ctor_get(x_240, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_240);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
}
}
else
{
uint8_t x_465; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_465 = !lean_is_exclusive(x_18);
if (x_465 == 0)
{
return x_18;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_18, 0);
x_467 = lean_ctor_get(x_18, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_18);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
}
else
{
uint8_t x_469; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_469 = !lean_is_exclusive(x_14);
if (x_469 == 0)
{
return x_14;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_14, 0);
x_471 = lean_ctor_get(x_14, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_14);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
return x_472;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_13 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_13, x_14, x_9, x_10);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_96; uint8_t x_97; 
x_40 = lean_ctor_get(x_38, 2);
x_96 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_38, 2, x_96);
x_97 = !lean_is_exclusive(x_12);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_12, 2);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_34);
lean_ctor_set(x_99, 1, x_21);
x_100 = lean_array_push(x_98, x_99);
lean_ctor_set(x_12, 2, x_100);
x_101 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_12, x_32);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_102);
x_41 = x_104;
x_42 = x_103;
goto block_95;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_dec(x_101);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_105);
x_41 = x_107;
x_42 = x_106;
goto block_95;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_12, 0);
x_109 = lean_ctor_get(x_12, 1);
x_110 = lean_ctor_get(x_12, 2);
x_111 = lean_ctor_get(x_12, 3);
x_112 = lean_ctor_get(x_12, 4);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_12);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_34);
lean_ctor_set(x_113, 1, x_21);
x_114 = lean_array_push(x_110, x_113);
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_111);
lean_ctor_set(x_115, 4, x_112);
x_116 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_115, x_32);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_117);
x_41 = x_119;
x_42 = x_118;
goto block_95;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_120);
x_41 = x_122;
x_42 = x_121;
goto block_95;
}
}
block_95:
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
x_52 = lean_ctor_get(x_43, 3);
x_53 = lean_ctor_get(x_43, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_40);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_42, 2, x_54);
if (lean_is_scalar(x_33)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_33;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_42);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
x_58 = lean_ctor_get(x_42, 3);
x_59 = lean_ctor_get(x_42, 4);
x_60 = lean_ctor_get(x_42, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_61 = lean_ctor_get(x_43, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_43, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_43, 4);
lean_inc(x_64);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 x_65 = x_43;
} else {
 lean_dec_ref(x_43);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 5, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_40);
lean_ctor_set(x_66, 3, x_63);
lean_ctor_set(x_66, 4, x_64);
x_67 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_57);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set(x_67, 4, x_59);
lean_ctor_set(x_67, 5, x_60);
if (lean_is_scalar(x_33)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_33;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_44);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_42, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_41, 0);
lean_inc(x_70);
lean_dec(x_41);
x_71 = !lean_is_exclusive(x_42);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_42, 2);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_69, 2);
lean_dec(x_74);
lean_ctor_set(x_69, 2, x_40);
if (lean_is_scalar(x_33)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_33;
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_42);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_69, 0);
x_77 = lean_ctor_get(x_69, 1);
x_78 = lean_ctor_get(x_69, 3);
x_79 = lean_ctor_get(x_69, 4);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_69);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_77);
lean_ctor_set(x_80, 2, x_40);
lean_ctor_set(x_80, 3, x_78);
lean_ctor_set(x_80, 4, x_79);
lean_ctor_set(x_42, 2, x_80);
if (lean_is_scalar(x_33)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_33;
}
lean_ctor_set(x_81, 0, x_70);
lean_ctor_set(x_81, 1, x_42);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_82 = lean_ctor_get(x_42, 0);
x_83 = lean_ctor_get(x_42, 1);
x_84 = lean_ctor_get(x_42, 3);
x_85 = lean_ctor_get(x_42, 4);
x_86 = lean_ctor_get(x_42, 5);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_42);
x_87 = lean_ctor_get(x_69, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_69, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_69, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_69, 4);
lean_inc(x_90);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 lean_ctor_release(x_69, 4);
 x_91 = x_69;
} else {
 lean_dec_ref(x_69);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 5, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_40);
lean_ctor_set(x_92, 3, x_89);
lean_ctor_set(x_92, 4, x_90);
x_93 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_83);
lean_ctor_set(x_93, 2, x_92);
lean_ctor_set(x_93, 3, x_84);
lean_ctor_set(x_93, 4, x_85);
lean_ctor_set(x_93, 5, x_86);
if (lean_is_scalar(x_33)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_33;
}
lean_ctor_set(x_94, 0, x_70);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_123 = lean_ctor_get(x_38, 0);
x_124 = lean_ctor_get(x_38, 1);
x_125 = lean_ctor_get(x_38, 2);
x_126 = lean_ctor_get(x_38, 3);
x_127 = lean_ctor_get(x_38, 4);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_38);
x_163 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_164 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_164, 0, x_123);
lean_ctor_set(x_164, 1, x_124);
lean_ctor_set(x_164, 2, x_163);
lean_ctor_set(x_164, 3, x_126);
lean_ctor_set(x_164, 4, x_127);
lean_ctor_set(x_32, 2, x_164);
x_165 = lean_ctor_get(x_12, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_12, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_12, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_12, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_12, 4);
lean_inc(x_169);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_170 = x_12;
} else {
 lean_dec_ref(x_12);
 x_170 = lean_box(0);
}
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_34);
lean_ctor_set(x_171, 1, x_21);
x_172 = lean_array_push(x_167, x_171);
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(0, 5, 0);
} else {
 x_173 = x_170;
}
lean_ctor_set(x_173, 0, x_165);
lean_ctor_set(x_173, 1, x_166);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_173, 3, x_168);
lean_ctor_set(x_173, 4, x_169);
x_174 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_173, x_32);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_175);
x_128 = x_177;
x_129 = x_176;
goto block_162;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_dec(x_174);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_178);
x_128 = x_180;
x_129 = x_179;
goto block_162;
}
block_162:
{
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_130 = lean_ctor_get(x_129, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 4);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 5);
lean_inc(x_136);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 x_137 = x_129;
} else {
 lean_dec_ref(x_129);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_130, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_130, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_130, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_130, 4);
lean_inc(x_141);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 x_142 = x_130;
} else {
 lean_dec_ref(x_130);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set(x_143, 2, x_125);
lean_ctor_set(x_143, 3, x_140);
lean_ctor_set(x_143, 4, x_141);
if (lean_is_scalar(x_137)) {
 x_144 = lean_alloc_ctor(0, 6, 0);
} else {
 x_144 = x_137;
}
lean_ctor_set(x_144, 0, x_132);
lean_ctor_set(x_144, 1, x_133);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_134);
lean_ctor_set(x_144, 4, x_135);
lean_ctor_set(x_144, 5, x_136);
if (lean_is_scalar(x_33)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_33;
 lean_ctor_set_tag(x_145, 1);
}
lean_ctor_set(x_145, 0, x_131);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_146 = lean_ctor_get(x_129, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_128, 0);
lean_inc(x_147);
lean_dec(x_128);
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_129, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_129, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_129, 4);
lean_inc(x_151);
x_152 = lean_ctor_get(x_129, 5);
lean_inc(x_152);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 x_153 = x_129;
} else {
 lean_dec_ref(x_129);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_146, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_146, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_146, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_146, 4);
lean_inc(x_157);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 x_158 = x_146;
} else {
 lean_dec_ref(x_146);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_155);
lean_ctor_set(x_159, 2, x_125);
lean_ctor_set(x_159, 3, x_156);
lean_ctor_set(x_159, 4, x_157);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(0, 6, 0);
} else {
 x_160 = x_153;
}
lean_ctor_set(x_160, 0, x_148);
lean_ctor_set(x_160, 1, x_149);
lean_ctor_set(x_160, 2, x_159);
lean_ctor_set(x_160, 3, x_150);
lean_ctor_set(x_160, 4, x_151);
lean_ctor_set(x_160, 5, x_152);
if (lean_is_scalar(x_33)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_33;
}
lean_ctor_set(x_161, 0, x_147);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_181 = lean_ctor_get(x_32, 2);
x_182 = lean_ctor_get(x_32, 0);
x_183 = lean_ctor_get(x_32, 1);
x_184 = lean_ctor_get(x_32, 3);
x_185 = lean_ctor_get(x_32, 4);
x_186 = lean_ctor_get(x_32, 5);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_181);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_32);
x_187 = lean_ctor_get(x_181, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_181, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_181, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_181, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_181, 4);
lean_inc(x_191);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 lean_ctor_release(x_181, 3);
 lean_ctor_release(x_181, 4);
 x_192 = x_181;
} else {
 lean_dec_ref(x_181);
 x_192 = lean_box(0);
}
x_228 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_192)) {
 x_229 = lean_alloc_ctor(0, 5, 0);
} else {
 x_229 = x_192;
}
lean_ctor_set(x_229, 0, x_187);
lean_ctor_set(x_229, 1, x_188);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_190);
lean_ctor_set(x_229, 4, x_191);
x_230 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_230, 0, x_182);
lean_ctor_set(x_230, 1, x_183);
lean_ctor_set(x_230, 2, x_229);
lean_ctor_set(x_230, 3, x_184);
lean_ctor_set(x_230, 4, x_185);
lean_ctor_set(x_230, 5, x_186);
x_231 = lean_ctor_get(x_12, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_12, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_12, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_12, 3);
lean_inc(x_234);
x_235 = lean_ctor_get(x_12, 4);
lean_inc(x_235);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_236 = x_12;
} else {
 lean_dec_ref(x_12);
 x_236 = lean_box(0);
}
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_34);
lean_ctor_set(x_237, 1, x_21);
x_238 = lean_array_push(x_233, x_237);
if (lean_is_scalar(x_236)) {
 x_239 = lean_alloc_ctor(0, 5, 0);
} else {
 x_239 = x_236;
}
lean_ctor_set(x_239, 0, x_231);
lean_ctor_set(x_239, 1, x_232);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_239, 3, x_234);
lean_ctor_set(x_239, 4, x_235);
x_240 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_239, x_230);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_241);
x_193 = x_243;
x_194 = x_242;
goto block_227;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_240, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 1);
lean_inc(x_245);
lean_dec(x_240);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_244);
x_193 = x_246;
x_194 = x_245;
goto block_227;
}
block_227:
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_195 = lean_ctor_get(x_194, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_ctor_get(x_194, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_194, 4);
lean_inc(x_200);
x_201 = lean_ctor_get(x_194, 5);
lean_inc(x_201);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 lean_ctor_release(x_194, 4);
 lean_ctor_release(x_194, 5);
 x_202 = x_194;
} else {
 lean_dec_ref(x_194);
 x_202 = lean_box(0);
}
x_203 = lean_ctor_get(x_195, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_195, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_195, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_195, 4);
lean_inc(x_206);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 x_207 = x_195;
} else {
 lean_dec_ref(x_195);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_203);
lean_ctor_set(x_208, 1, x_204);
lean_ctor_set(x_208, 2, x_189);
lean_ctor_set(x_208, 3, x_205);
lean_ctor_set(x_208, 4, x_206);
if (lean_is_scalar(x_202)) {
 x_209 = lean_alloc_ctor(0, 6, 0);
} else {
 x_209 = x_202;
}
lean_ctor_set(x_209, 0, x_197);
lean_ctor_set(x_209, 1, x_198);
lean_ctor_set(x_209, 2, x_208);
lean_ctor_set(x_209, 3, x_199);
lean_ctor_set(x_209, 4, x_200);
lean_ctor_set(x_209, 5, x_201);
if (lean_is_scalar(x_33)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_33;
 lean_ctor_set_tag(x_210, 1);
}
lean_ctor_set(x_210, 0, x_196);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_211 = lean_ctor_get(x_194, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_193, 0);
lean_inc(x_212);
lean_dec(x_193);
x_213 = lean_ctor_get(x_194, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_194, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_194, 3);
lean_inc(x_215);
x_216 = lean_ctor_get(x_194, 4);
lean_inc(x_216);
x_217 = lean_ctor_get(x_194, 5);
lean_inc(x_217);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 lean_ctor_release(x_194, 4);
 lean_ctor_release(x_194, 5);
 x_218 = x_194;
} else {
 lean_dec_ref(x_194);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_211, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_211, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_211, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_211, 4);
lean_inc(x_222);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 lean_ctor_release(x_211, 2);
 lean_ctor_release(x_211, 3);
 lean_ctor_release(x_211, 4);
 x_223 = x_211;
} else {
 lean_dec_ref(x_211);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 5, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_219);
lean_ctor_set(x_224, 1, x_220);
lean_ctor_set(x_224, 2, x_189);
lean_ctor_set(x_224, 3, x_221);
lean_ctor_set(x_224, 4, x_222);
if (lean_is_scalar(x_218)) {
 x_225 = lean_alloc_ctor(0, 6, 0);
} else {
 x_225 = x_218;
}
lean_ctor_set(x_225, 0, x_213);
lean_ctor_set(x_225, 1, x_214);
lean_ctor_set(x_225, 2, x_224);
lean_ctor_set(x_225, 3, x_215);
lean_ctor_set(x_225, 4, x_216);
lean_ctor_set(x_225, 5, x_217);
if (lean_is_scalar(x_33)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_33;
}
lean_ctor_set(x_226, 0, x_212);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
default: 
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_26, 1);
lean_inc(x_247);
lean_dec(x_26);
lean_inc(x_12);
x_248 = l_Lean_Meta_isClassExpensive___main(x_25, x_12, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_21);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_nat_add(x_11, x_251);
lean_dec(x_11);
x_11 = x_252;
x_13 = x_250;
goto _start;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_254 = lean_ctor_get(x_248, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_255 = x_248;
} else {
 lean_dec_ref(x_248);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_249, 0);
lean_inc(x_256);
lean_dec(x_249);
x_257 = lean_unsigned_to_nat(1u);
x_258 = lean_nat_add(x_11, x_257);
lean_dec(x_11);
x_259 = !lean_is_exclusive(x_254);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_254, 2);
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_318; uint8_t x_319; 
x_262 = lean_ctor_get(x_260, 2);
x_318 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_260, 2, x_318);
x_319 = !lean_is_exclusive(x_12);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_320 = lean_ctor_get(x_12, 2);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_256);
lean_ctor_set(x_321, 1, x_21);
x_322 = lean_array_push(x_320, x_321);
lean_ctor_set(x_12, 2, x_322);
x_323 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_258, x_12, x_254);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_324);
x_263 = x_326;
x_264 = x_325;
goto block_317;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_323, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_323, 1);
lean_inc(x_328);
lean_dec(x_323);
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_327);
x_263 = x_329;
x_264 = x_328;
goto block_317;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_330 = lean_ctor_get(x_12, 0);
x_331 = lean_ctor_get(x_12, 1);
x_332 = lean_ctor_get(x_12, 2);
x_333 = lean_ctor_get(x_12, 3);
x_334 = lean_ctor_get(x_12, 4);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_12);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_256);
lean_ctor_set(x_335, 1, x_21);
x_336 = lean_array_push(x_332, x_335);
x_337 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_337, 0, x_330);
lean_ctor_set(x_337, 1, x_331);
lean_ctor_set(x_337, 2, x_336);
lean_ctor_set(x_337, 3, x_333);
lean_ctor_set(x_337, 4, x_334);
x_338 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_258, x_337, x_254);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_339);
x_263 = x_341;
x_264 = x_340;
goto block_317;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_338, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_338, 1);
lean_inc(x_343);
lean_dec(x_338);
x_344 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_344, 0, x_342);
x_263 = x_344;
x_264 = x_343;
goto block_317;
}
}
block_317:
{
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_265 = lean_ctor_get(x_264, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_263, 0);
lean_inc(x_266);
lean_dec(x_263);
x_267 = !lean_is_exclusive(x_264);
if (x_267 == 0)
{
lean_object* x_268; uint8_t x_269; 
x_268 = lean_ctor_get(x_264, 2);
lean_dec(x_268);
x_269 = !lean_is_exclusive(x_265);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_265, 2);
lean_dec(x_270);
lean_ctor_set(x_265, 2, x_262);
if (lean_is_scalar(x_255)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_255;
 lean_ctor_set_tag(x_271, 1);
}
lean_ctor_set(x_271, 0, x_266);
lean_ctor_set(x_271, 1, x_264);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_272 = lean_ctor_get(x_265, 0);
x_273 = lean_ctor_get(x_265, 1);
x_274 = lean_ctor_get(x_265, 3);
x_275 = lean_ctor_get(x_265, 4);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_265);
x_276 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_276, 0, x_272);
lean_ctor_set(x_276, 1, x_273);
lean_ctor_set(x_276, 2, x_262);
lean_ctor_set(x_276, 3, x_274);
lean_ctor_set(x_276, 4, x_275);
lean_ctor_set(x_264, 2, x_276);
if (lean_is_scalar(x_255)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_255;
 lean_ctor_set_tag(x_277, 1);
}
lean_ctor_set(x_277, 0, x_266);
lean_ctor_set(x_277, 1, x_264);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_278 = lean_ctor_get(x_264, 0);
x_279 = lean_ctor_get(x_264, 1);
x_280 = lean_ctor_get(x_264, 3);
x_281 = lean_ctor_get(x_264, 4);
x_282 = lean_ctor_get(x_264, 5);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_264);
x_283 = lean_ctor_get(x_265, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_265, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_265, 3);
lean_inc(x_285);
x_286 = lean_ctor_get(x_265, 4);
lean_inc(x_286);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 x_287 = x_265;
} else {
 lean_dec_ref(x_265);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 5, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_283);
lean_ctor_set(x_288, 1, x_284);
lean_ctor_set(x_288, 2, x_262);
lean_ctor_set(x_288, 3, x_285);
lean_ctor_set(x_288, 4, x_286);
x_289 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_289, 0, x_278);
lean_ctor_set(x_289, 1, x_279);
lean_ctor_set(x_289, 2, x_288);
lean_ctor_set(x_289, 3, x_280);
lean_ctor_set(x_289, 4, x_281);
lean_ctor_set(x_289, 5, x_282);
if (lean_is_scalar(x_255)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_255;
 lean_ctor_set_tag(x_290, 1);
}
lean_ctor_set(x_290, 0, x_266);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_291 = lean_ctor_get(x_264, 2);
lean_inc(x_291);
x_292 = lean_ctor_get(x_263, 0);
lean_inc(x_292);
lean_dec(x_263);
x_293 = !lean_is_exclusive(x_264);
if (x_293 == 0)
{
lean_object* x_294; uint8_t x_295; 
x_294 = lean_ctor_get(x_264, 2);
lean_dec(x_294);
x_295 = !lean_is_exclusive(x_291);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_291, 2);
lean_dec(x_296);
lean_ctor_set(x_291, 2, x_262);
if (lean_is_scalar(x_255)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_255;
}
lean_ctor_set(x_297, 0, x_292);
lean_ctor_set(x_297, 1, x_264);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_ctor_get(x_291, 0);
x_299 = lean_ctor_get(x_291, 1);
x_300 = lean_ctor_get(x_291, 3);
x_301 = lean_ctor_get(x_291, 4);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_291);
x_302 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_299);
lean_ctor_set(x_302, 2, x_262);
lean_ctor_set(x_302, 3, x_300);
lean_ctor_set(x_302, 4, x_301);
lean_ctor_set(x_264, 2, x_302);
if (lean_is_scalar(x_255)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_255;
}
lean_ctor_set(x_303, 0, x_292);
lean_ctor_set(x_303, 1, x_264);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_304 = lean_ctor_get(x_264, 0);
x_305 = lean_ctor_get(x_264, 1);
x_306 = lean_ctor_get(x_264, 3);
x_307 = lean_ctor_get(x_264, 4);
x_308 = lean_ctor_get(x_264, 5);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_264);
x_309 = lean_ctor_get(x_291, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_291, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_291, 3);
lean_inc(x_311);
x_312 = lean_ctor_get(x_291, 4);
lean_inc(x_312);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 lean_ctor_release(x_291, 2);
 lean_ctor_release(x_291, 3);
 lean_ctor_release(x_291, 4);
 x_313 = x_291;
} else {
 lean_dec_ref(x_291);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(0, 5, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_309);
lean_ctor_set(x_314, 1, x_310);
lean_ctor_set(x_314, 2, x_262);
lean_ctor_set(x_314, 3, x_311);
lean_ctor_set(x_314, 4, x_312);
x_315 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_315, 0, x_304);
lean_ctor_set(x_315, 1, x_305);
lean_ctor_set(x_315, 2, x_314);
lean_ctor_set(x_315, 3, x_306);
lean_ctor_set(x_315, 4, x_307);
lean_ctor_set(x_315, 5, x_308);
if (lean_is_scalar(x_255)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_255;
}
lean_ctor_set(x_316, 0, x_292);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_345 = lean_ctor_get(x_260, 0);
x_346 = lean_ctor_get(x_260, 1);
x_347 = lean_ctor_get(x_260, 2);
x_348 = lean_ctor_get(x_260, 3);
x_349 = lean_ctor_get(x_260, 4);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_260);
x_385 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_386 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_386, 0, x_345);
lean_ctor_set(x_386, 1, x_346);
lean_ctor_set(x_386, 2, x_385);
lean_ctor_set(x_386, 3, x_348);
lean_ctor_set(x_386, 4, x_349);
lean_ctor_set(x_254, 2, x_386);
x_387 = lean_ctor_get(x_12, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_12, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_12, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_12, 3);
lean_inc(x_390);
x_391 = lean_ctor_get(x_12, 4);
lean_inc(x_391);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_392 = x_12;
} else {
 lean_dec_ref(x_12);
 x_392 = lean_box(0);
}
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_256);
lean_ctor_set(x_393, 1, x_21);
x_394 = lean_array_push(x_389, x_393);
if (lean_is_scalar(x_392)) {
 x_395 = lean_alloc_ctor(0, 5, 0);
} else {
 x_395 = x_392;
}
lean_ctor_set(x_395, 0, x_387);
lean_ctor_set(x_395, 1, x_388);
lean_ctor_set(x_395, 2, x_394);
lean_ctor_set(x_395, 3, x_390);
lean_ctor_set(x_395, 4, x_391);
x_396 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_258, x_395, x_254);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_397);
x_350 = x_399;
x_351 = x_398;
goto block_384;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_396, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_396, 1);
lean_inc(x_401);
lean_dec(x_396);
x_402 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_402, 0, x_400);
x_350 = x_402;
x_351 = x_401;
goto block_384;
}
block_384:
{
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_352 = lean_ctor_get(x_351, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_350, 0);
lean_inc(x_353);
lean_dec(x_350);
x_354 = lean_ctor_get(x_351, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_351, 3);
lean_inc(x_356);
x_357 = lean_ctor_get(x_351, 4);
lean_inc(x_357);
x_358 = lean_ctor_get(x_351, 5);
lean_inc(x_358);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 lean_ctor_release(x_351, 4);
 lean_ctor_release(x_351, 5);
 x_359 = x_351;
} else {
 lean_dec_ref(x_351);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_352, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_352, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_352, 3);
lean_inc(x_362);
x_363 = lean_ctor_get(x_352, 4);
lean_inc(x_363);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 lean_ctor_release(x_352, 4);
 x_364 = x_352;
} else {
 lean_dec_ref(x_352);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(0, 5, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_360);
lean_ctor_set(x_365, 1, x_361);
lean_ctor_set(x_365, 2, x_347);
lean_ctor_set(x_365, 3, x_362);
lean_ctor_set(x_365, 4, x_363);
if (lean_is_scalar(x_359)) {
 x_366 = lean_alloc_ctor(0, 6, 0);
} else {
 x_366 = x_359;
}
lean_ctor_set(x_366, 0, x_354);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set(x_366, 2, x_365);
lean_ctor_set(x_366, 3, x_356);
lean_ctor_set(x_366, 4, x_357);
lean_ctor_set(x_366, 5, x_358);
if (lean_is_scalar(x_255)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_255;
 lean_ctor_set_tag(x_367, 1);
}
lean_ctor_set(x_367, 0, x_353);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_368 = lean_ctor_get(x_351, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_350, 0);
lean_inc(x_369);
lean_dec(x_350);
x_370 = lean_ctor_get(x_351, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_351, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_351, 3);
lean_inc(x_372);
x_373 = lean_ctor_get(x_351, 4);
lean_inc(x_373);
x_374 = lean_ctor_get(x_351, 5);
lean_inc(x_374);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 lean_ctor_release(x_351, 4);
 lean_ctor_release(x_351, 5);
 x_375 = x_351;
} else {
 lean_dec_ref(x_351);
 x_375 = lean_box(0);
}
x_376 = lean_ctor_get(x_368, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_368, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_368, 3);
lean_inc(x_378);
x_379 = lean_ctor_get(x_368, 4);
lean_inc(x_379);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 lean_ctor_release(x_368, 4);
 x_380 = x_368;
} else {
 lean_dec_ref(x_368);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(0, 5, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_376);
lean_ctor_set(x_381, 1, x_377);
lean_ctor_set(x_381, 2, x_347);
lean_ctor_set(x_381, 3, x_378);
lean_ctor_set(x_381, 4, x_379);
if (lean_is_scalar(x_375)) {
 x_382 = lean_alloc_ctor(0, 6, 0);
} else {
 x_382 = x_375;
}
lean_ctor_set(x_382, 0, x_370);
lean_ctor_set(x_382, 1, x_371);
lean_ctor_set(x_382, 2, x_381);
lean_ctor_set(x_382, 3, x_372);
lean_ctor_set(x_382, 4, x_373);
lean_ctor_set(x_382, 5, x_374);
if (lean_is_scalar(x_255)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_255;
}
lean_ctor_set(x_383, 0, x_369);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_403 = lean_ctor_get(x_254, 2);
x_404 = lean_ctor_get(x_254, 0);
x_405 = lean_ctor_get(x_254, 1);
x_406 = lean_ctor_get(x_254, 3);
x_407 = lean_ctor_get(x_254, 4);
x_408 = lean_ctor_get(x_254, 5);
lean_inc(x_408);
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_403);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_254);
x_409 = lean_ctor_get(x_403, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_403, 1);
lean_inc(x_410);
x_411 = lean_ctor_get(x_403, 2);
lean_inc(x_411);
x_412 = lean_ctor_get(x_403, 3);
lean_inc(x_412);
x_413 = lean_ctor_get(x_403, 4);
lean_inc(x_413);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 lean_ctor_release(x_403, 4);
 x_414 = x_403;
} else {
 lean_dec_ref(x_403);
 x_414 = lean_box(0);
}
x_450 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_414)) {
 x_451 = lean_alloc_ctor(0, 5, 0);
} else {
 x_451 = x_414;
}
lean_ctor_set(x_451, 0, x_409);
lean_ctor_set(x_451, 1, x_410);
lean_ctor_set(x_451, 2, x_450);
lean_ctor_set(x_451, 3, x_412);
lean_ctor_set(x_451, 4, x_413);
x_452 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_452, 0, x_404);
lean_ctor_set(x_452, 1, x_405);
lean_ctor_set(x_452, 2, x_451);
lean_ctor_set(x_452, 3, x_406);
lean_ctor_set(x_452, 4, x_407);
lean_ctor_set(x_452, 5, x_408);
x_453 = lean_ctor_get(x_12, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_12, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_12, 2);
lean_inc(x_455);
x_456 = lean_ctor_get(x_12, 3);
lean_inc(x_456);
x_457 = lean_ctor_get(x_12, 4);
lean_inc(x_457);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_458 = x_12;
} else {
 lean_dec_ref(x_12);
 x_458 = lean_box(0);
}
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_256);
lean_ctor_set(x_459, 1, x_21);
x_460 = lean_array_push(x_455, x_459);
if (lean_is_scalar(x_458)) {
 x_461 = lean_alloc_ctor(0, 5, 0);
} else {
 x_461 = x_458;
}
lean_ctor_set(x_461, 0, x_453);
lean_ctor_set(x_461, 1, x_454);
lean_ctor_set(x_461, 2, x_460);
lean_ctor_set(x_461, 3, x_456);
lean_ctor_set(x_461, 4, x_457);
x_462 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_258, x_461, x_452);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_465, 0, x_463);
x_415 = x_465;
x_416 = x_464;
goto block_449;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_462, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_462, 1);
lean_inc(x_467);
lean_dec(x_462);
x_468 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_468, 0, x_466);
x_415 = x_468;
x_416 = x_467;
goto block_449;
}
block_449:
{
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_417 = lean_ctor_get(x_416, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_415, 0);
lean_inc(x_418);
lean_dec(x_415);
x_419 = lean_ctor_get(x_416, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_416, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_416, 3);
lean_inc(x_421);
x_422 = lean_ctor_get(x_416, 4);
lean_inc(x_422);
x_423 = lean_ctor_get(x_416, 5);
lean_inc(x_423);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 lean_ctor_release(x_416, 4);
 lean_ctor_release(x_416, 5);
 x_424 = x_416;
} else {
 lean_dec_ref(x_416);
 x_424 = lean_box(0);
}
x_425 = lean_ctor_get(x_417, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_417, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_417, 3);
lean_inc(x_427);
x_428 = lean_ctor_get(x_417, 4);
lean_inc(x_428);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 lean_ctor_release(x_417, 4);
 x_429 = x_417;
} else {
 lean_dec_ref(x_417);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(0, 5, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_425);
lean_ctor_set(x_430, 1, x_426);
lean_ctor_set(x_430, 2, x_411);
lean_ctor_set(x_430, 3, x_427);
lean_ctor_set(x_430, 4, x_428);
if (lean_is_scalar(x_424)) {
 x_431 = lean_alloc_ctor(0, 6, 0);
} else {
 x_431 = x_424;
}
lean_ctor_set(x_431, 0, x_419);
lean_ctor_set(x_431, 1, x_420);
lean_ctor_set(x_431, 2, x_430);
lean_ctor_set(x_431, 3, x_421);
lean_ctor_set(x_431, 4, x_422);
lean_ctor_set(x_431, 5, x_423);
if (lean_is_scalar(x_255)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_255;
 lean_ctor_set_tag(x_432, 1);
}
lean_ctor_set(x_432, 0, x_418);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_433 = lean_ctor_get(x_416, 2);
lean_inc(x_433);
x_434 = lean_ctor_get(x_415, 0);
lean_inc(x_434);
lean_dec(x_415);
x_435 = lean_ctor_get(x_416, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_416, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_416, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_416, 4);
lean_inc(x_438);
x_439 = lean_ctor_get(x_416, 5);
lean_inc(x_439);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 lean_ctor_release(x_416, 4);
 lean_ctor_release(x_416, 5);
 x_440 = x_416;
} else {
 lean_dec_ref(x_416);
 x_440 = lean_box(0);
}
x_441 = lean_ctor_get(x_433, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_433, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_433, 3);
lean_inc(x_443);
x_444 = lean_ctor_get(x_433, 4);
lean_inc(x_444);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 lean_ctor_release(x_433, 4);
 x_445 = x_433;
} else {
 lean_dec_ref(x_433);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(0, 5, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_441);
lean_ctor_set(x_446, 1, x_442);
lean_ctor_set(x_446, 2, x_411);
lean_ctor_set(x_446, 3, x_443);
lean_ctor_set(x_446, 4, x_444);
if (lean_is_scalar(x_440)) {
 x_447 = lean_alloc_ctor(0, 6, 0);
} else {
 x_447 = x_440;
}
lean_ctor_set(x_447, 0, x_435);
lean_ctor_set(x_447, 1, x_436);
lean_ctor_set(x_447, 2, x_446);
lean_ctor_set(x_447, 3, x_437);
lean_ctor_set(x_447, 4, x_438);
lean_ctor_set(x_447, 5, x_439);
if (lean_is_scalar(x_255)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_255;
}
lean_ctor_set(x_448, 0, x_434);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
}
}
else
{
uint8_t x_469; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_469 = !lean_is_exclusive(x_248);
if (x_469 == 0)
{
return x_248;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_248, 0);
x_471 = lean_ctor_get(x_248, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_248);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
return x_472;
}
}
}
}
}
else
{
uint8_t x_473; 
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
x_473 = !lean_is_exclusive(x_26);
if (x_473 == 0)
{
return x_26;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_26, 0);
x_475 = lean_ctor_get(x_26, 1);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_26);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_475);
return x_476;
}
}
}
else
{
uint8_t x_477; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_477 = !lean_is_exclusive(x_22);
if (x_477 == 0)
{
return x_22;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_22, 0);
x_479 = lean_ctor_get(x_22, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_22);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
return x_480;
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_4, x_1, x_2, x_3, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = l_Array_empty___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = 1;
x_9 = l_Lean_Meta_introN(x_1, x_7, x_6, x_8, x_3, x_4);
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
x_7 = l_Lean_Meta_introN(x_1, x_6, x_5, x_2, x_3, x_4);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
