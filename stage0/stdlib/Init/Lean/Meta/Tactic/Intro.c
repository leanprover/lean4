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
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__4;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__3;
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalInstance_hasBeq___closed__1;
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_introNCoreAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Lean_Meta_mkAuxName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main(lean_object*);
lean_object* l_Lean_Meta_introNCoreAux(lean_object*);
lean_object* l_Lean_Meta_intro1___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = 2;
lean_inc(x_5);
x_8 = l_Lean_Meta_mkFreshExprMVar(x_1, x_4, x_7, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
lean_inc(x_2);
x_11 = l_Lean_Meta_mkLambda(x_2, x_9, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_MetavarContext_assignExpr(x_16, x_3, x_15);
lean_ctor_set(x_13, 1, x_17);
x_18 = l_Lean_Expr_mvarId_x21(x_9);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
x_23 = lean_ctor_get(x_13, 2);
x_24 = lean_ctor_get(x_13, 3);
x_25 = lean_ctor_get(x_13, 4);
x_26 = lean_ctor_get(x_13, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_27 = l_Lean_MetavarContext_assignExpr(x_22, x_3, x_20);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
x_29 = l_Lean_Expr_mvarId_x21(x_9);
lean_dec(x_9);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_11, 1, x_28);
lean_ctor_set(x_11, 0, x_30);
return x_11;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_11, 1);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 5);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 lean_ctor_release(x_31, 4);
 lean_ctor_release(x_31, 5);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
x_40 = l_Lean_MetavarContext_assignExpr(x_34, x_3, x_32);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 6, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 4, x_37);
lean_ctor_set(x_41, 5, x_38);
x_42 = l_Lean_Expr_mvarId_x21(x_9);
lean_dec(x_9);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
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
x_40 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_2);
lean_inc(x_4);
x_43 = lean_apply_3(x_2, x_4, x_34, x_7);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = (uint8_t)((x_37 << 24) >> 61);
lean_inc(x_41);
x_47 = lean_local_ctx_mk_local_decl(x_4, x_41, x_44, x_39, x_46);
x_48 = l_Lean_mkFVar(x_41);
x_49 = lean_array_push(x_5, x_48);
x_3 = x_14;
x_4 = x_47;
x_5 = x_49;
x_7 = x_45;
x_8 = x_36;
x_10 = x_42;
goto _start;
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
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
x_57 = lean_expr_instantiate_rev_range(x_53, x_6, x_55, x_5);
lean_dec(x_55);
lean_dec(x_53);
x_58 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_2);
lean_inc(x_4);
x_61 = lean_apply_3(x_2, x_4, x_51, x_7);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_59);
x_64 = lean_local_ctx_mk_let_decl(x_4, x_59, x_62, x_56, x_57);
x_65 = l_Lean_mkFVar(x_59);
x_66 = lean_array_push(x_5, x_65);
x_3 = x_14;
x_4 = x_64;
x_5 = x_66;
x_7 = x_63;
x_8 = x_54;
x_10 = x_60;
goto _start;
}
default: 
{
lean_object* x_68; 
x_68 = lean_box(0);
x_15 = x_68;
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
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_array_get_size(x_5);
x_70 = lean_expr_instantiate_rev_range(x_8, x_6, x_69, x_5);
lean_dec(x_69);
lean_dec(x_8);
lean_inc(x_1);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 3, 1);
lean_closure_set(x_71, 0, x_1);
lean_inc(x_5);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__2), 6, 3);
lean_closure_set(x_72, 0, x_70);
lean_closure_set(x_72, 1, x_5);
lean_closure_set(x_72, 2, x_1);
x_73 = l_EIO_Monad___closed__1;
x_74 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_74, 0, x_73);
lean_closure_set(x_74, 1, lean_box(0));
lean_closure_set(x_74, 2, lean_box(0));
lean_closure_set(x_74, 3, x_71);
lean_closure_set(x_74, 4, x_72);
x_75 = !lean_is_exclusive(x_9);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_9, 1);
lean_dec(x_76);
lean_ctor_set(x_9, 1, x_4);
x_77 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_78 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_77, x_5, x_6, x_74, x_9, x_10);
lean_dec(x_5);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_9, 0);
x_80 = lean_ctor_get(x_9, 2);
x_81 = lean_ctor_get(x_9, 3);
x_82 = lean_ctor_get(x_9, 4);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_9);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_4);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_81);
lean_ctor_set(x_83, 4, x_82);
x_84 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_85 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_84, x_5, x_6, x_74, x_83, x_10);
lean_dec(x_5);
return x_85;
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
lean_object* l_Lean_Meta_introNCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_get_size(x_12);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_ctor_set(x_5, 2, x_15);
lean_ctor_set(x_5, 1, x_14);
if (x_18 == 0)
{
lean_object* x_211; 
lean_dec(x_15);
lean_dec(x_12);
x_211 = lean_box(0);
x_19 = x_211;
goto block_210;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_212 = l_Lean_LocalInstance_hasBeq___closed__1;
x_213 = lean_unsigned_to_nat(0u);
x_214 = l_Array_isEqvAux___main___rarg(x_12, x_15, lean_box(0), x_212, x_213);
lean_dec(x_15);
lean_dec(x_12);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_box(0);
x_19 = x_215;
goto block_210;
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_10);
x_216 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_217 = l_Lean_Meta_checkNotAssigned(x_1, x_216, x_5, x_9);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
lean_inc(x_1);
x_219 = l_Lean_Meta_getMVarType(x_1, x_5, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = l_Array_empty___closed__1;
x_223 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_2, x_14, x_222, x_213, x_4, x_220, x_5, x_221);
return x_223;
}
else
{
uint8_t x_224; 
lean_dec(x_5);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_219);
if (x_224 == 0)
{
return x_219;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_219, 0);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_219);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_5);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_217);
if (x_228 == 0)
{
return x_217;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_217, 0);
x_230 = lean_ctor_get(x_217, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_217);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
block_210:
{
uint8_t x_20; 
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_9, 2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_23 = lean_ctor_get(x_21, 2);
x_48 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_21, 2, x_48);
x_49 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_50 = l_Lean_Meta_checkNotAssigned(x_1, x_49, x_5, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_1);
x_52 = l_Lean_Meta_getMVarType(x_1, x_5, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Array_empty___closed__1;
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_2, x_14, x_55, x_56, x_4, x_53, x_5, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_10);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_58, 2);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 2);
lean_dec(x_65);
lean_ctor_set(x_59, 2, x_23);
return x_57;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_23);
lean_ctor_set(x_58, 2, x_68);
return x_57;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
x_71 = lean_ctor_get(x_58, 3);
x_72 = lean_ctor_get(x_58, 4);
x_73 = lean_ctor_get(x_58, 5);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_74 = lean_ctor_get(x_59, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_59, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_76 = x_59;
} else {
 lean_dec_ref(x_59);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 3, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_23);
x_78 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_78, 3, x_71);
lean_ctor_set(x_78, 4, x_72);
lean_ctor_set(x_78, 5, x_73);
lean_ctor_set(x_57, 1, x_78);
return x_57;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_57, 0);
lean_inc(x_79);
lean_dec(x_57);
x_80 = lean_ctor_get(x_58, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_58, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_58, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_58, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_58, 5);
lean_inc(x_84);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 lean_ctor_release(x_58, 5);
 x_85 = x_58;
} else {
 lean_dec_ref(x_58);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_59, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_59, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_88 = x_59;
} else {
 lean_dec_ref(x_59);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 3, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set(x_89, 2, x_23);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 6, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_81);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_82);
lean_ctor_set(x_90, 4, x_83);
lean_ctor_set(x_90, 5, x_84);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_79);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_57, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_dec(x_57);
x_24 = x_92;
x_25 = x_93;
goto block_47;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_52, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_52, 1);
lean_inc(x_95);
lean_dec(x_52);
x_24 = x_94;
x_25 = x_95;
goto block_47;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_50, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_50, 1);
lean_inc(x_97);
lean_dec(x_50);
x_24 = x_96;
x_25 = x_97;
goto block_47;
}
block_47:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 2);
lean_dec(x_29);
lean_ctor_set(x_27, 2, x_23);
if (lean_is_scalar(x_10)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_10;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_25, 2, x_33);
if (lean_is_scalar(x_10)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_10;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_25, 2);
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
x_38 = lean_ctor_get(x_25, 3);
x_39 = lean_ctor_get(x_25, 4);
x_40 = lean_ctor_get(x_25, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 3, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_23);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_38);
lean_ctor_set(x_45, 4, x_39);
lean_ctor_set(x_45, 5, x_40);
if (lean_is_scalar(x_10)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_10;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_98 = lean_ctor_get(x_21, 0);
x_99 = lean_ctor_get(x_21, 1);
x_100 = lean_ctor_get(x_21, 2);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_21);
x_117 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_98);
lean_ctor_set(x_118, 1, x_99);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_9, 2, x_118);
x_119 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_120 = l_Lean_Meta_checkNotAssigned(x_1, x_119, x_5, x_9);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
lean_inc(x_1);
x_122 = l_Lean_Meta_getMVarType(x_1, x_5, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Array_empty___closed__1;
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_2, x_14, x_125, x_126, x_4, x_123, x_5, x_124);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_10);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_128, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 4);
lean_inc(x_135);
x_136 = lean_ctor_get(x_128, 5);
lean_inc(x_136);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 lean_ctor_release(x_128, 5);
 x_137 = x_128;
} else {
 lean_dec_ref(x_128);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_129, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_129, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 x_140 = x_129;
} else {
 lean_dec_ref(x_129);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 3, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
lean_ctor_set(x_141, 2, x_100);
if (lean_is_scalar(x_137)) {
 x_142 = lean_alloc_ctor(0, 6, 0);
} else {
 x_142 = x_137;
}
lean_ctor_set(x_142, 0, x_132);
lean_ctor_set(x_142, 1, x_133);
lean_ctor_set(x_142, 2, x_141);
lean_ctor_set(x_142, 3, x_134);
lean_ctor_set(x_142, 4, x_135);
lean_ctor_set(x_142, 5, x_136);
if (lean_is_scalar(x_131)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_131;
}
lean_ctor_set(x_143, 0, x_130);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_127, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_127, 1);
lean_inc(x_145);
lean_dec(x_127);
x_101 = x_144;
x_102 = x_145;
goto block_116;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_5);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_122, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_122, 1);
lean_inc(x_147);
lean_dec(x_122);
x_101 = x_146;
x_102 = x_147;
goto block_116;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_5);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_ctor_get(x_120, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_120, 1);
lean_inc(x_149);
lean_dec(x_120);
x_101 = x_148;
x_102 = x_149;
goto block_116;
}
block_116:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_ctor_get(x_102, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_102, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_102, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 5);
lean_inc(x_108);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 lean_ctor_release(x_102, 3);
 lean_ctor_release(x_102, 4);
 lean_ctor_release(x_102, 5);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 3, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set(x_113, 2, x_100);
if (lean_is_scalar(x_109)) {
 x_114 = lean_alloc_ctor(0, 6, 0);
} else {
 x_114 = x_109;
}
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_105);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_106);
lean_ctor_set(x_114, 4, x_107);
lean_ctor_set(x_114, 5, x_108);
if (lean_is_scalar(x_10)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_10;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_101);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_150 = lean_ctor_get(x_9, 2);
x_151 = lean_ctor_get(x_9, 0);
x_152 = lean_ctor_get(x_9, 1);
x_153 = lean_ctor_get(x_9, 3);
x_154 = lean_ctor_get(x_9, 4);
x_155 = lean_ctor_get(x_9, 5);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_150);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_9);
x_156 = lean_ctor_get(x_150, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_150, 2);
lean_inc(x_158);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 x_159 = x_150;
} else {
 lean_dec_ref(x_150);
 x_159 = lean_box(0);
}
x_176 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_159)) {
 x_177 = lean_alloc_ctor(0, 3, 0);
} else {
 x_177 = x_159;
}
lean_ctor_set(x_177, 0, x_156);
lean_ctor_set(x_177, 1, x_157);
lean_ctor_set(x_177, 2, x_176);
x_178 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_178, 0, x_151);
lean_ctor_set(x_178, 1, x_152);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_178, 3, x_153);
lean_ctor_set(x_178, 4, x_154);
lean_ctor_set(x_178, 5, x_155);
x_179 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_180 = l_Lean_Meta_checkNotAssigned(x_1, x_179, x_5, x_178);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
lean_inc(x_1);
x_182 = l_Lean_Meta_getMVarType(x_1, x_5, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Array_empty___closed__1;
x_186 = lean_unsigned_to_nat(0u);
x_187 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_2, x_14, x_185, x_186, x_4, x_183, x_5, x_184);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_10);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
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
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_200 = x_189;
} else {
 lean_dec_ref(x_189);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(0, 3, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_158);
if (lean_is_scalar(x_197)) {
 x_202 = lean_alloc_ctor(0, 6, 0);
} else {
 x_202 = x_197;
}
lean_ctor_set(x_202, 0, x_192);
lean_ctor_set(x_202, 1, x_193);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_194);
lean_ctor_set(x_202, 4, x_195);
lean_ctor_set(x_202, 5, x_196);
if (lean_is_scalar(x_191)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_191;
}
lean_ctor_set(x_203, 0, x_190);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_187, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_187, 1);
lean_inc(x_205);
lean_dec(x_187);
x_160 = x_204;
x_161 = x_205;
goto block_175;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_5);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = lean_ctor_get(x_182, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_182, 1);
lean_inc(x_207);
lean_dec(x_182);
x_160 = x_206;
x_161 = x_207;
goto block_175;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_5);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_208 = lean_ctor_get(x_180, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_180, 1);
lean_inc(x_209);
lean_dec(x_180);
x_160 = x_208;
x_161 = x_209;
goto block_175;
}
block_175:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_162 = lean_ctor_get(x_161, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 5);
lean_inc(x_167);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 x_168 = x_161;
} else {
 lean_dec_ref(x_161);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_162, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 x_171 = x_162;
} else {
 lean_dec_ref(x_162);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 3, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_158);
if (lean_is_scalar(x_168)) {
 x_173 = lean_alloc_ctor(0, 6, 0);
} else {
 x_173 = x_168;
}
lean_ctor_set(x_173, 0, x_163);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_173, 3, x_165);
lean_ctor_set(x_173, 4, x_166);
lean_ctor_set(x_173, 5, x_167);
if (lean_is_scalar(x_10)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_10;
 lean_ctor_set_tag(x_174, 1);
}
lean_ctor_set(x_174, 0, x_160);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; 
x_232 = lean_ctor_get(x_5, 0);
x_233 = lean_ctor_get(x_5, 2);
x_234 = lean_ctor_get(x_5, 3);
x_235 = lean_ctor_get(x_5, 4);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_5);
x_236 = lean_ctor_get(x_8, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_8, 4);
lean_inc(x_237);
lean_dec(x_8);
x_238 = lean_array_get_size(x_233);
x_239 = lean_array_get_size(x_237);
x_240 = lean_nat_dec_eq(x_238, x_239);
lean_dec(x_239);
lean_dec(x_238);
lean_inc(x_237);
lean_inc(x_236);
x_241 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_241, 0, x_232);
lean_ctor_set(x_241, 1, x_236);
lean_ctor_set(x_241, 2, x_237);
lean_ctor_set(x_241, 3, x_234);
lean_ctor_set(x_241, 4, x_235);
if (x_240 == 0)
{
lean_object* x_305; 
lean_dec(x_237);
lean_dec(x_233);
x_305 = lean_box(0);
x_242 = x_305;
goto block_304;
}
else
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_306 = l_Lean_LocalInstance_hasBeq___closed__1;
x_307 = lean_unsigned_to_nat(0u);
x_308 = l_Array_isEqvAux___main___rarg(x_233, x_237, lean_box(0), x_306, x_307);
lean_dec(x_237);
lean_dec(x_233);
if (x_308 == 0)
{
lean_object* x_309; 
x_309 = lean_box(0);
x_242 = x_309;
goto block_304;
}
else
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_10);
x_310 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_311 = l_Lean_Meta_checkNotAssigned(x_1, x_310, x_241, x_9);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec(x_311);
lean_inc(x_1);
x_313 = l_Lean_Meta_getMVarType(x_1, x_241, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = l_Array_empty___closed__1;
x_317 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_2, x_236, x_316, x_307, x_4, x_314, x_241, x_315);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_241);
lean_dec(x_236);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_318 = lean_ctor_get(x_313, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_313, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_320 = x_313;
} else {
 lean_dec_ref(x_313);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_241);
lean_dec(x_236);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_322 = lean_ctor_get(x_311, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_311, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_324 = x_311;
} else {
 lean_dec_ref(x_311);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
}
block_304:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_242);
x_243 = lean_ctor_get(x_9, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_9, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_9, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_9, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_9, 4);
lean_inc(x_247);
x_248 = lean_ctor_get(x_9, 5);
lean_inc(x_248);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 x_249 = x_9;
} else {
 lean_dec_ref(x_9);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_243, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_243, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_243, 2);
lean_inc(x_252);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_253 = x_243;
} else {
 lean_dec_ref(x_243);
 x_253 = lean_box(0);
}
x_270 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_253)) {
 x_271 = lean_alloc_ctor(0, 3, 0);
} else {
 x_271 = x_253;
}
lean_ctor_set(x_271, 0, x_250);
lean_ctor_set(x_271, 1, x_251);
lean_ctor_set(x_271, 2, x_270);
if (lean_is_scalar(x_249)) {
 x_272 = lean_alloc_ctor(0, 6, 0);
} else {
 x_272 = x_249;
}
lean_ctor_set(x_272, 0, x_244);
lean_ctor_set(x_272, 1, x_245);
lean_ctor_set(x_272, 2, x_271);
lean_ctor_set(x_272, 3, x_246);
lean_ctor_set(x_272, 4, x_247);
lean_ctor_set(x_272, 5, x_248);
x_273 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_274 = l_Lean_Meta_checkNotAssigned(x_1, x_273, x_241, x_272);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
lean_inc(x_1);
x_276 = l_Lean_Meta_getMVarType(x_1, x_241, x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = l_Array_empty___closed__1;
x_280 = lean_unsigned_to_nat(0u);
x_281 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_2, x_236, x_279, x_280, x_4, x_277, x_241, x_278);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_10);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_282, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_285 = x_281;
} else {
 lean_dec_ref(x_281);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_282, 3);
lean_inc(x_288);
x_289 = lean_ctor_get(x_282, 4);
lean_inc(x_289);
x_290 = lean_ctor_get(x_282, 5);
lean_inc(x_290);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 lean_ctor_release(x_282, 2);
 lean_ctor_release(x_282, 3);
 lean_ctor_release(x_282, 4);
 lean_ctor_release(x_282, 5);
 x_291 = x_282;
} else {
 lean_dec_ref(x_282);
 x_291 = lean_box(0);
}
x_292 = lean_ctor_get(x_283, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_283, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 lean_ctor_release(x_283, 2);
 x_294 = x_283;
} else {
 lean_dec_ref(x_283);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(0, 3, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
lean_ctor_set(x_295, 2, x_252);
if (lean_is_scalar(x_291)) {
 x_296 = lean_alloc_ctor(0, 6, 0);
} else {
 x_296 = x_291;
}
lean_ctor_set(x_296, 0, x_286);
lean_ctor_set(x_296, 1, x_287);
lean_ctor_set(x_296, 2, x_295);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set(x_296, 4, x_289);
lean_ctor_set(x_296, 5, x_290);
if (lean_is_scalar(x_285)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_285;
}
lean_ctor_set(x_297, 0, x_284);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_281, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_281, 1);
lean_inc(x_299);
lean_dec(x_281);
x_254 = x_298;
x_255 = x_299;
goto block_269;
}
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_241);
lean_dec(x_236);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = lean_ctor_get(x_276, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_276, 1);
lean_inc(x_301);
lean_dec(x_276);
x_254 = x_300;
x_255 = x_301;
goto block_269;
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_241);
lean_dec(x_236);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = lean_ctor_get(x_274, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_274, 1);
lean_inc(x_303);
lean_dec(x_274);
x_254 = x_302;
x_255 = x_303;
goto block_269;
}
block_269:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_256 = lean_ctor_get(x_255, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_255, 4);
lean_inc(x_260);
x_261 = lean_ctor_get(x_255, 5);
lean_inc(x_261);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 lean_ctor_release(x_255, 3);
 lean_ctor_release(x_255, 4);
 lean_ctor_release(x_255, 5);
 x_262 = x_255;
} else {
 lean_dec_ref(x_255);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_256, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_256, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_265 = x_256;
} else {
 lean_dec_ref(x_256);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(0, 3, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
lean_ctor_set(x_266, 2, x_252);
if (lean_is_scalar(x_262)) {
 x_267 = lean_alloc_ctor(0, 6, 0);
} else {
 x_267 = x_262;
}
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_258);
lean_ctor_set(x_267, 2, x_266);
lean_ctor_set(x_267, 3, x_259);
lean_ctor_set(x_267, 4, x_260);
lean_ctor_set(x_267, 5, x_261);
if (lean_is_scalar(x_10)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_10;
 lean_ctor_set_tag(x_268, 1);
}
lean_ctor_set(x_268, 0, x_254);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_326 = !lean_is_exclusive(x_7);
if (x_326 == 0)
{
return x_7;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_7, 0);
x_328 = lean_ctor_get(x_7, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_7);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
}
lean_object* l_Lean_Meta_introNCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___rarg), 6, 0);
return x_2;
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
lean_object* l_Lean_Meta_mkAuxName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_local_ctx_get_unused_name(x_1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_Meta_mkAuxName___closed__1;
x_9 = lean_name_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = lean_local_ctx_get_unused_name(x_1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_31);
lean_ctor_set(x_38, 2, x_48);
return x_37;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
x_51 = lean_ctor_get(x_38, 3);
x_52 = lean_ctor_get(x_38, 4);
x_53 = lean_ctor_get(x_38, 5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_56 = x_39;
} else {
 lean_dec_ref(x_39);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 3, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_31);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_51);
lean_ctor_set(x_58, 4, x_52);
lean_ctor_set(x_58, 5, x_53);
lean_ctor_set(x_37, 1, x_58);
return x_37;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_37, 0);
lean_inc(x_59);
lean_dec(x_37);
x_60 = lean_ctor_get(x_38, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_38, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_38, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 5);
lean_inc(x_64);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_65 = x_38;
} else {
 lean_dec_ref(x_38);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_39, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_39, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_68 = x_39;
} else {
 lean_dec_ref(x_39);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 3, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_31);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 6, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_62);
lean_ctor_set(x_70, 4, x_63);
lean_ctor_set(x_70, 5, x_64);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_37, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 2);
lean_inc(x_73);
x_74 = !lean_is_exclusive(x_37);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_37, 1);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_72, 2);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_73, 2);
lean_dec(x_79);
lean_ctor_set(x_73, 2, x_31);
return x_37;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_73, 0);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_73);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_31);
lean_ctor_set(x_72, 2, x_82);
return x_37;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_72, 0);
x_84 = lean_ctor_get(x_72, 1);
x_85 = lean_ctor_get(x_72, 3);
x_86 = lean_ctor_get(x_72, 4);
x_87 = lean_ctor_get(x_72, 5);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_72);
x_88 = lean_ctor_get(x_73, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_73, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_90 = x_73;
} else {
 lean_dec_ref(x_73);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 3, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_31);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_92, 2, x_91);
lean_ctor_set(x_92, 3, x_85);
lean_ctor_set(x_92, 4, x_86);
lean_ctor_set(x_92, 5, x_87);
lean_ctor_set(x_37, 1, x_92);
return x_37;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_93 = lean_ctor_get(x_37, 0);
lean_inc(x_93);
lean_dec(x_37);
x_94 = lean_ctor_get(x_72, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_72, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_72, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_72, 4);
lean_inc(x_97);
x_98 = lean_ctor_get(x_72, 5);
lean_inc(x_98);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_99 = x_72;
} else {
 lean_dec_ref(x_72);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_73, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_73, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_102 = x_73;
} else {
 lean_dec_ref(x_73);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 3, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_31);
if (lean_is_scalar(x_99)) {
 x_104 = lean_alloc_ctor(0, 6, 0);
} else {
 x_104 = x_99;
}
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_95);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_96);
lean_ctor_set(x_104, 4, x_97);
lean_ctor_set(x_104, 5, x_98);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_6, 0);
x_107 = lean_ctor_get(x_6, 1);
x_108 = lean_ctor_get(x_6, 2);
x_109 = lean_ctor_get(x_6, 3);
x_110 = lean_ctor_get(x_6, 4);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_6);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_25);
lean_ctor_set(x_111, 1, x_13);
x_112 = lean_array_push(x_108, x_111);
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_107);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_109);
lean_ctor_set(x_113, 4, x_110);
x_114 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_27, x_113, x_24);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_115, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 lean_ctor_release(x_115, 5);
 x_124 = x_115;
} else {
 lean_dec_ref(x_115);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_116, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 x_127 = x_116;
} else {
 lean_dec_ref(x_116);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 3, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_31);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 6, 0);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set(x_129, 4, x_122);
lean_ctor_set(x_129, 5, x_123);
if (lean_is_scalar(x_118)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_118;
}
lean_ctor_set(x_130, 0, x_117);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_131 = lean_ctor_get(x_114, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_114, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_134 = x_114;
} else {
 lean_dec_ref(x_114);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 4);
lean_inc(x_138);
x_139 = lean_ctor_get(x_131, 5);
lean_inc(x_139);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 x_140 = x_131;
} else {
 lean_dec_ref(x_131);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_132, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 x_143 = x_132;
} else {
 lean_dec_ref(x_132);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 3, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_144, 2, x_31);
if (lean_is_scalar(x_140)) {
 x_145 = lean_alloc_ctor(0, 6, 0);
} else {
 x_145 = x_140;
}
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_136);
lean_ctor_set(x_145, 2, x_144);
lean_ctor_set(x_145, 3, x_137);
lean_ctor_set(x_145, 4, x_138);
lean_ctor_set(x_145, 5, x_139);
if (lean_is_scalar(x_134)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_134;
}
lean_ctor_set(x_146, 0, x_133);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_147 = lean_ctor_get(x_29, 0);
x_148 = lean_ctor_get(x_29, 1);
x_149 = lean_ctor_get(x_29, 2);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_29);
x_150 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_148);
lean_ctor_set(x_151, 2, x_150);
lean_ctor_set(x_24, 2, x_151);
x_152 = lean_ctor_get(x_6, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_6, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_6, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_6, 3);
lean_inc(x_155);
x_156 = lean_ctor_get(x_6, 4);
lean_inc(x_156);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_157 = x_6;
} else {
 lean_dec_ref(x_6);
 x_157 = lean_box(0);
}
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_25);
lean_ctor_set(x_158, 1, x_13);
x_159 = lean_array_push(x_154, x_158);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 5, 0);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_152);
lean_ctor_set(x_160, 1, x_153);
lean_ctor_set(x_160, 2, x_159);
lean_ctor_set(x_160, 3, x_155);
lean_ctor_set(x_160, 4, x_156);
x_161 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_27, x_160, x_24);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_165 = x_161;
} else {
 lean_dec_ref(x_161);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_162, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 5);
lean_inc(x_170);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 lean_ctor_release(x_162, 4);
 lean_ctor_release(x_162, 5);
 x_171 = x_162;
} else {
 lean_dec_ref(x_162);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_163, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_163, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 x_174 = x_163;
} else {
 lean_dec_ref(x_163);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(0, 3, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 2, x_149);
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 6, 0);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_166);
lean_ctor_set(x_176, 1, x_167);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_176, 3, x_168);
lean_ctor_set(x_176, 4, x_169);
lean_ctor_set(x_176, 5, x_170);
if (lean_is_scalar(x_165)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_165;
}
lean_ctor_set(x_177, 0, x_164);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_178 = lean_ctor_get(x_161, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_161, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_181 = x_161;
} else {
 lean_dec_ref(x_161);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 4);
lean_inc(x_185);
x_186 = lean_ctor_get(x_178, 5);
lean_inc(x_186);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 lean_ctor_release(x_178, 5);
 x_187 = x_178;
} else {
 lean_dec_ref(x_178);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_179, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_179, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 x_190 = x_179;
} else {
 lean_dec_ref(x_179);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 3, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
lean_ctor_set(x_191, 2, x_149);
if (lean_is_scalar(x_187)) {
 x_192 = lean_alloc_ctor(0, 6, 0);
} else {
 x_192 = x_187;
}
lean_ctor_set(x_192, 0, x_182);
lean_ctor_set(x_192, 1, x_183);
lean_ctor_set(x_192, 2, x_191);
lean_ctor_set(x_192, 3, x_184);
lean_ctor_set(x_192, 4, x_185);
lean_ctor_set(x_192, 5, x_186);
if (lean_is_scalar(x_181)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_181;
}
lean_ctor_set(x_193, 0, x_180);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_194 = lean_ctor_get(x_24, 2);
x_195 = lean_ctor_get(x_24, 0);
x_196 = lean_ctor_get(x_24, 1);
x_197 = lean_ctor_get(x_24, 3);
x_198 = lean_ctor_get(x_24, 4);
x_199 = lean_ctor_get(x_24, 5);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_194);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_24);
x_200 = lean_ctor_get(x_194, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_194, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_194, 2);
lean_inc(x_202);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 x_203 = x_194;
} else {
 lean_dec_ref(x_194);
 x_203 = lean_box(0);
}
x_204 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 3, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_200);
lean_ctor_set(x_205, 1, x_201);
lean_ctor_set(x_205, 2, x_204);
x_206 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_206, 0, x_195);
lean_ctor_set(x_206, 1, x_196);
lean_ctor_set(x_206, 2, x_205);
lean_ctor_set(x_206, 3, x_197);
lean_ctor_set(x_206, 4, x_198);
lean_ctor_set(x_206, 5, x_199);
x_207 = lean_ctor_get(x_6, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_6, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_6, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_6, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_6, 4);
lean_inc(x_211);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_212 = x_6;
} else {
 lean_dec_ref(x_6);
 x_212 = lean_box(0);
}
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_25);
lean_ctor_set(x_213, 1, x_13);
x_214 = lean_array_push(x_209, x_213);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 5, 0);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_207);
lean_ctor_set(x_215, 1, x_208);
lean_ctor_set(x_215, 2, x_214);
lean_ctor_set(x_215, 3, x_210);
lean_ctor_set(x_215, 4, x_211);
x_216 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_27, x_215, x_206);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_217, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_220 = x_216;
} else {
 lean_dec_ref(x_216);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_217, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_217, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_217, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 4);
lean_inc(x_224);
x_225 = lean_ctor_get(x_217, 5);
lean_inc(x_225);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 lean_ctor_release(x_217, 4);
 lean_ctor_release(x_217, 5);
 x_226 = x_217;
} else {
 lean_dec_ref(x_217);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_218, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_218, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 x_229 = x_218;
} else {
 lean_dec_ref(x_218);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(0, 3, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
lean_ctor_set(x_230, 2, x_202);
if (lean_is_scalar(x_226)) {
 x_231 = lean_alloc_ctor(0, 6, 0);
} else {
 x_231 = x_226;
}
lean_ctor_set(x_231, 0, x_221);
lean_ctor_set(x_231, 1, x_222);
lean_ctor_set(x_231, 2, x_230);
lean_ctor_set(x_231, 3, x_223);
lean_ctor_set(x_231, 4, x_224);
lean_ctor_set(x_231, 5, x_225);
if (lean_is_scalar(x_220)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_220;
}
lean_ctor_set(x_232, 0, x_219);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_233 = lean_ctor_get(x_216, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 2);
lean_inc(x_234);
x_235 = lean_ctor_get(x_216, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_236 = x_216;
} else {
 lean_dec_ref(x_216);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_233, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_233, 4);
lean_inc(x_240);
x_241 = lean_ctor_get(x_233, 5);
lean_inc(x_241);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 lean_ctor_release(x_233, 3);
 lean_ctor_release(x_233, 4);
 lean_ctor_release(x_233, 5);
 x_242 = x_233;
} else {
 lean_dec_ref(x_233);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_234, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_234, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 x_245 = x_234;
} else {
 lean_dec_ref(x_234);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 3, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
lean_ctor_set(x_246, 2, x_202);
if (lean_is_scalar(x_242)) {
 x_247 = lean_alloc_ctor(0, 6, 0);
} else {
 x_247 = x_242;
}
lean_ctor_set(x_247, 0, x_237);
lean_ctor_set(x_247, 1, x_238);
lean_ctor_set(x_247, 2, x_246);
lean_ctor_set(x_247, 3, x_239);
lean_ctor_set(x_247, 4, x_240);
lean_ctor_set(x_247, 5, x_241);
if (lean_is_scalar(x_236)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_236;
}
lean_ctor_set(x_248, 0, x_235);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
default: 
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_18, 1);
lean_inc(x_249);
lean_dec(x_18);
lean_inc(x_6);
x_250 = l_Lean_Meta_isClassExpensive___main(x_17, x_6, x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_13);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_nat_add(x_5, x_253);
lean_dec(x_5);
x_5 = x_254;
x_7 = x_252;
goto _start;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_256 = lean_ctor_get(x_250, 1);
lean_inc(x_256);
lean_dec(x_250);
x_257 = lean_ctor_get(x_251, 0);
lean_inc(x_257);
lean_dec(x_251);
x_258 = lean_unsigned_to_nat(1u);
x_259 = lean_nat_add(x_5, x_258);
lean_dec(x_5);
x_260 = !lean_is_exclusive(x_256);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_256, 2);
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_261, 2);
x_264 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_261, 2, x_264);
x_265 = !lean_is_exclusive(x_6);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_6, 2);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_13);
x_268 = lean_array_push(x_266, x_267);
lean_ctor_set(x_6, 2, x_268);
x_269 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_259, x_6, x_256);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_270, 2);
lean_inc(x_271);
x_272 = !lean_is_exclusive(x_269);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_269, 1);
lean_dec(x_273);
x_274 = !lean_is_exclusive(x_270);
if (x_274 == 0)
{
lean_object* x_275; uint8_t x_276; 
x_275 = lean_ctor_get(x_270, 2);
lean_dec(x_275);
x_276 = !lean_is_exclusive(x_271);
if (x_276 == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_271, 2);
lean_dec(x_277);
lean_ctor_set(x_271, 2, x_263);
return x_269;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_271, 0);
x_279 = lean_ctor_get(x_271, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_271);
x_280 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_263);
lean_ctor_set(x_270, 2, x_280);
return x_269;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_281 = lean_ctor_get(x_270, 0);
x_282 = lean_ctor_get(x_270, 1);
x_283 = lean_ctor_get(x_270, 3);
x_284 = lean_ctor_get(x_270, 4);
x_285 = lean_ctor_get(x_270, 5);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_270);
x_286 = lean_ctor_get(x_271, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_271, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 x_288 = x_271;
} else {
 lean_dec_ref(x_271);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 3, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
lean_ctor_set(x_289, 2, x_263);
x_290 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_290, 0, x_281);
lean_ctor_set(x_290, 1, x_282);
lean_ctor_set(x_290, 2, x_289);
lean_ctor_set(x_290, 3, x_283);
lean_ctor_set(x_290, 4, x_284);
lean_ctor_set(x_290, 5, x_285);
lean_ctor_set(x_269, 1, x_290);
return x_269;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_291 = lean_ctor_get(x_269, 0);
lean_inc(x_291);
lean_dec(x_269);
x_292 = lean_ctor_get(x_270, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_270, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_270, 3);
lean_inc(x_294);
x_295 = lean_ctor_get(x_270, 4);
lean_inc(x_295);
x_296 = lean_ctor_get(x_270, 5);
lean_inc(x_296);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 lean_ctor_release(x_270, 4);
 lean_ctor_release(x_270, 5);
 x_297 = x_270;
} else {
 lean_dec_ref(x_270);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_271, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_271, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 x_300 = x_271;
} else {
 lean_dec_ref(x_271);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(0, 3, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
lean_ctor_set(x_301, 2, x_263);
if (lean_is_scalar(x_297)) {
 x_302 = lean_alloc_ctor(0, 6, 0);
} else {
 x_302 = x_297;
}
lean_ctor_set(x_302, 0, x_292);
lean_ctor_set(x_302, 1, x_293);
lean_ctor_set(x_302, 2, x_301);
lean_ctor_set(x_302, 3, x_294);
lean_ctor_set(x_302, 4, x_295);
lean_ctor_set(x_302, 5, x_296);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_291);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_269, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 2);
lean_inc(x_305);
x_306 = !lean_is_exclusive(x_269);
if (x_306 == 0)
{
lean_object* x_307; uint8_t x_308; 
x_307 = lean_ctor_get(x_269, 1);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_304);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_304, 2);
lean_dec(x_309);
x_310 = !lean_is_exclusive(x_305);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_305, 2);
lean_dec(x_311);
lean_ctor_set(x_305, 2, x_263);
return x_269;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_305, 0);
x_313 = lean_ctor_get(x_305, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_305);
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
lean_ctor_set(x_314, 2, x_263);
lean_ctor_set(x_304, 2, x_314);
return x_269;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_315 = lean_ctor_get(x_304, 0);
x_316 = lean_ctor_get(x_304, 1);
x_317 = lean_ctor_get(x_304, 3);
x_318 = lean_ctor_get(x_304, 4);
x_319 = lean_ctor_get(x_304, 5);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_304);
x_320 = lean_ctor_get(x_305, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_305, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 x_322 = x_305;
} else {
 lean_dec_ref(x_305);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 3, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
lean_ctor_set(x_323, 2, x_263);
x_324 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_324, 0, x_315);
lean_ctor_set(x_324, 1, x_316);
lean_ctor_set(x_324, 2, x_323);
lean_ctor_set(x_324, 3, x_317);
lean_ctor_set(x_324, 4, x_318);
lean_ctor_set(x_324, 5, x_319);
lean_ctor_set(x_269, 1, x_324);
return x_269;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_269, 0);
lean_inc(x_325);
lean_dec(x_269);
x_326 = lean_ctor_get(x_304, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_304, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_304, 3);
lean_inc(x_328);
x_329 = lean_ctor_get(x_304, 4);
lean_inc(x_329);
x_330 = lean_ctor_get(x_304, 5);
lean_inc(x_330);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 lean_ctor_release(x_304, 2);
 lean_ctor_release(x_304, 3);
 lean_ctor_release(x_304, 4);
 lean_ctor_release(x_304, 5);
 x_331 = x_304;
} else {
 lean_dec_ref(x_304);
 x_331 = lean_box(0);
}
x_332 = lean_ctor_get(x_305, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_305, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 x_334 = x_305;
} else {
 lean_dec_ref(x_305);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(0, 3, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
lean_ctor_set(x_335, 2, x_263);
if (lean_is_scalar(x_331)) {
 x_336 = lean_alloc_ctor(0, 6, 0);
} else {
 x_336 = x_331;
}
lean_ctor_set(x_336, 0, x_326);
lean_ctor_set(x_336, 1, x_327);
lean_ctor_set(x_336, 2, x_335);
lean_ctor_set(x_336, 3, x_328);
lean_ctor_set(x_336, 4, x_329);
lean_ctor_set(x_336, 5, x_330);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_325);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_338 = lean_ctor_get(x_6, 0);
x_339 = lean_ctor_get(x_6, 1);
x_340 = lean_ctor_get(x_6, 2);
x_341 = lean_ctor_get(x_6, 3);
x_342 = lean_ctor_get(x_6, 4);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_6);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_257);
lean_ctor_set(x_343, 1, x_13);
x_344 = lean_array_push(x_340, x_343);
x_345 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_345, 0, x_338);
lean_ctor_set(x_345, 1, x_339);
lean_ctor_set(x_345, 2, x_344);
lean_ctor_set(x_345, 3, x_341);
lean_ctor_set(x_345, 4, x_342);
x_346 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_259, x_345, x_256);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_347, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_346, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_350 = x_346;
} else {
 lean_dec_ref(x_346);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_347, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_347, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_347, 4);
lean_inc(x_354);
x_355 = lean_ctor_get(x_347, 5);
lean_inc(x_355);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 lean_ctor_release(x_347, 4);
 lean_ctor_release(x_347, 5);
 x_356 = x_347;
} else {
 lean_dec_ref(x_347);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_348, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_348, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 x_359 = x_348;
} else {
 lean_dec_ref(x_348);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(0, 3, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
lean_ctor_set(x_360, 2, x_263);
if (lean_is_scalar(x_356)) {
 x_361 = lean_alloc_ctor(0, 6, 0);
} else {
 x_361 = x_356;
}
lean_ctor_set(x_361, 0, x_351);
lean_ctor_set(x_361, 1, x_352);
lean_ctor_set(x_361, 2, x_360);
lean_ctor_set(x_361, 3, x_353);
lean_ctor_set(x_361, 4, x_354);
lean_ctor_set(x_361, 5, x_355);
if (lean_is_scalar(x_350)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_350;
}
lean_ctor_set(x_362, 0, x_349);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_363 = lean_ctor_get(x_346, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_363, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_346, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_366 = x_346;
} else {
 lean_dec_ref(x_346);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_363, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_363, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_363, 3);
lean_inc(x_369);
x_370 = lean_ctor_get(x_363, 4);
lean_inc(x_370);
x_371 = lean_ctor_get(x_363, 5);
lean_inc(x_371);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 lean_ctor_release(x_363, 4);
 lean_ctor_release(x_363, 5);
 x_372 = x_363;
} else {
 lean_dec_ref(x_363);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_364, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_364, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 lean_ctor_release(x_364, 2);
 x_375 = x_364;
} else {
 lean_dec_ref(x_364);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(0, 3, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
lean_ctor_set(x_376, 2, x_263);
if (lean_is_scalar(x_372)) {
 x_377 = lean_alloc_ctor(0, 6, 0);
} else {
 x_377 = x_372;
}
lean_ctor_set(x_377, 0, x_367);
lean_ctor_set(x_377, 1, x_368);
lean_ctor_set(x_377, 2, x_376);
lean_ctor_set(x_377, 3, x_369);
lean_ctor_set(x_377, 4, x_370);
lean_ctor_set(x_377, 5, x_371);
if (lean_is_scalar(x_366)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_366;
}
lean_ctor_set(x_378, 0, x_365);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_379 = lean_ctor_get(x_261, 0);
x_380 = lean_ctor_get(x_261, 1);
x_381 = lean_ctor_get(x_261, 2);
lean_inc(x_381);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_261);
x_382 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_383 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_383, 0, x_379);
lean_ctor_set(x_383, 1, x_380);
lean_ctor_set(x_383, 2, x_382);
lean_ctor_set(x_256, 2, x_383);
x_384 = lean_ctor_get(x_6, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_6, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_6, 2);
lean_inc(x_386);
x_387 = lean_ctor_get(x_6, 3);
lean_inc(x_387);
x_388 = lean_ctor_get(x_6, 4);
lean_inc(x_388);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_389 = x_6;
} else {
 lean_dec_ref(x_6);
 x_389 = lean_box(0);
}
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_257);
lean_ctor_set(x_390, 1, x_13);
x_391 = lean_array_push(x_386, x_390);
if (lean_is_scalar(x_389)) {
 x_392 = lean_alloc_ctor(0, 5, 0);
} else {
 x_392 = x_389;
}
lean_ctor_set(x_392, 0, x_384);
lean_ctor_set(x_392, 1, x_385);
lean_ctor_set(x_392, 2, x_391);
lean_ctor_set(x_392, 3, x_387);
lean_ctor_set(x_392, 4, x_388);
x_393 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_259, x_392, x_256);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_394, 2);
lean_inc(x_395);
x_396 = lean_ctor_get(x_393, 0);
lean_inc(x_396);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_397 = x_393;
} else {
 lean_dec_ref(x_393);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_394, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_394, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_394, 3);
lean_inc(x_400);
x_401 = lean_ctor_get(x_394, 4);
lean_inc(x_401);
x_402 = lean_ctor_get(x_394, 5);
lean_inc(x_402);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 lean_ctor_release(x_394, 2);
 lean_ctor_release(x_394, 3);
 lean_ctor_release(x_394, 4);
 lean_ctor_release(x_394, 5);
 x_403 = x_394;
} else {
 lean_dec_ref(x_394);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_395, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_395, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 lean_ctor_release(x_395, 2);
 x_406 = x_395;
} else {
 lean_dec_ref(x_395);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(0, 3, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_405);
lean_ctor_set(x_407, 2, x_381);
if (lean_is_scalar(x_403)) {
 x_408 = lean_alloc_ctor(0, 6, 0);
} else {
 x_408 = x_403;
}
lean_ctor_set(x_408, 0, x_398);
lean_ctor_set(x_408, 1, x_399);
lean_ctor_set(x_408, 2, x_407);
lean_ctor_set(x_408, 3, x_400);
lean_ctor_set(x_408, 4, x_401);
lean_ctor_set(x_408, 5, x_402);
if (lean_is_scalar(x_397)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_397;
}
lean_ctor_set(x_409, 0, x_396);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_410 = lean_ctor_get(x_393, 1);
lean_inc(x_410);
x_411 = lean_ctor_get(x_410, 2);
lean_inc(x_411);
x_412 = lean_ctor_get(x_393, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_413 = x_393;
} else {
 lean_dec_ref(x_393);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_410, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_410, 1);
lean_inc(x_415);
x_416 = lean_ctor_get(x_410, 3);
lean_inc(x_416);
x_417 = lean_ctor_get(x_410, 4);
lean_inc(x_417);
x_418 = lean_ctor_get(x_410, 5);
lean_inc(x_418);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 lean_ctor_release(x_410, 5);
 x_419 = x_410;
} else {
 lean_dec_ref(x_410);
 x_419 = lean_box(0);
}
x_420 = lean_ctor_get(x_411, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_411, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 lean_ctor_release(x_411, 2);
 x_422 = x_411;
} else {
 lean_dec_ref(x_411);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(0, 3, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_421);
lean_ctor_set(x_423, 2, x_381);
if (lean_is_scalar(x_419)) {
 x_424 = lean_alloc_ctor(0, 6, 0);
} else {
 x_424 = x_419;
}
lean_ctor_set(x_424, 0, x_414);
lean_ctor_set(x_424, 1, x_415);
lean_ctor_set(x_424, 2, x_423);
lean_ctor_set(x_424, 3, x_416);
lean_ctor_set(x_424, 4, x_417);
lean_ctor_set(x_424, 5, x_418);
if (lean_is_scalar(x_413)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_413;
}
lean_ctor_set(x_425, 0, x_412);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_426 = lean_ctor_get(x_256, 2);
x_427 = lean_ctor_get(x_256, 0);
x_428 = lean_ctor_get(x_256, 1);
x_429 = lean_ctor_get(x_256, 3);
x_430 = lean_ctor_get(x_256, 4);
x_431 = lean_ctor_get(x_256, 5);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_426);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_256);
x_432 = lean_ctor_get(x_426, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_426, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_426, 2);
lean_inc(x_434);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 x_435 = x_426;
} else {
 lean_dec_ref(x_426);
 x_435 = lean_box(0);
}
x_436 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(0, 3, 0);
} else {
 x_437 = x_435;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_433);
lean_ctor_set(x_437, 2, x_436);
x_438 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_438, 0, x_427);
lean_ctor_set(x_438, 1, x_428);
lean_ctor_set(x_438, 2, x_437);
lean_ctor_set(x_438, 3, x_429);
lean_ctor_set(x_438, 4, x_430);
lean_ctor_set(x_438, 5, x_431);
x_439 = lean_ctor_get(x_6, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_6, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_6, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_6, 3);
lean_inc(x_442);
x_443 = lean_ctor_get(x_6, 4);
lean_inc(x_443);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_444 = x_6;
} else {
 lean_dec_ref(x_6);
 x_444 = lean_box(0);
}
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_257);
lean_ctor_set(x_445, 1, x_13);
x_446 = lean_array_push(x_441, x_445);
if (lean_is_scalar(x_444)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_444;
}
lean_ctor_set(x_447, 0, x_439);
lean_ctor_set(x_447, 1, x_440);
lean_ctor_set(x_447, 2, x_446);
lean_ctor_set(x_447, 3, x_442);
lean_ctor_set(x_447, 4, x_443);
x_448 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_259, x_447, x_438);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
x_450 = lean_ctor_get(x_449, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_448, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_452 = x_448;
} else {
 lean_dec_ref(x_448);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_449, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_449, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_449, 3);
lean_inc(x_455);
x_456 = lean_ctor_get(x_449, 4);
lean_inc(x_456);
x_457 = lean_ctor_get(x_449, 5);
lean_inc(x_457);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 lean_ctor_release(x_449, 2);
 lean_ctor_release(x_449, 3);
 lean_ctor_release(x_449, 4);
 lean_ctor_release(x_449, 5);
 x_458 = x_449;
} else {
 lean_dec_ref(x_449);
 x_458 = lean_box(0);
}
x_459 = lean_ctor_get(x_450, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_450, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 lean_ctor_release(x_450, 2);
 x_461 = x_450;
} else {
 lean_dec_ref(x_450);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(0, 3, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_460);
lean_ctor_set(x_462, 2, x_434);
if (lean_is_scalar(x_458)) {
 x_463 = lean_alloc_ctor(0, 6, 0);
} else {
 x_463 = x_458;
}
lean_ctor_set(x_463, 0, x_453);
lean_ctor_set(x_463, 1, x_454);
lean_ctor_set(x_463, 2, x_462);
lean_ctor_set(x_463, 3, x_455);
lean_ctor_set(x_463, 4, x_456);
lean_ctor_set(x_463, 5, x_457);
if (lean_is_scalar(x_452)) {
 x_464 = lean_alloc_ctor(0, 2, 0);
} else {
 x_464 = x_452;
}
lean_ctor_set(x_464, 0, x_451);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_465 = lean_ctor_get(x_448, 1);
lean_inc(x_465);
x_466 = lean_ctor_get(x_465, 2);
lean_inc(x_466);
x_467 = lean_ctor_get(x_448, 0);
lean_inc(x_467);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_468 = x_448;
} else {
 lean_dec_ref(x_448);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_465, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_465, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_465, 3);
lean_inc(x_471);
x_472 = lean_ctor_get(x_465, 4);
lean_inc(x_472);
x_473 = lean_ctor_get(x_465, 5);
lean_inc(x_473);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 lean_ctor_release(x_465, 4);
 lean_ctor_release(x_465, 5);
 x_474 = x_465;
} else {
 lean_dec_ref(x_465);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_466, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 x_477 = x_466;
} else {
 lean_dec_ref(x_466);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(0, 3, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_476);
lean_ctor_set(x_478, 2, x_434);
if (lean_is_scalar(x_474)) {
 x_479 = lean_alloc_ctor(0, 6, 0);
} else {
 x_479 = x_474;
}
lean_ctor_set(x_479, 0, x_469);
lean_ctor_set(x_479, 1, x_470);
lean_ctor_set(x_479, 2, x_478);
lean_ctor_set(x_479, 3, x_471);
lean_ctor_set(x_479, 4, x_472);
lean_ctor_set(x_479, 5, x_473);
if (lean_is_scalar(x_468)) {
 x_480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_480 = x_468;
}
lean_ctor_set(x_480, 0, x_467);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
}
}
else
{
uint8_t x_481; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_481 = !lean_is_exclusive(x_250);
if (x_481 == 0)
{
return x_250;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_250, 0);
x_483 = lean_ctor_get(x_250, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_250);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
}
}
else
{
uint8_t x_485; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_485 = !lean_is_exclusive(x_18);
if (x_485 == 0)
{
return x_18;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_18, 0);
x_487 = lean_ctor_get(x_18, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_18);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
}
else
{
uint8_t x_489; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_489 = !lean_is_exclusive(x_14);
if (x_489 == 0)
{
return x_14;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_14, 0);
x_491 = lean_ctor_get(x_14, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_14);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isForall(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_12 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__5;
x_13 = l_Lean_Meta_throwTacticEx___rarg(x_11, x_1, x_12, x_8, x_9);
lean_dec(x_8);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_expr_instantiate_rev_range(x_6, x_4, x_8, x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 3, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___lambda__1), 9, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_7);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_8);
lean_closure_set(x_15, 5, x_5);
x_16 = lean_array_get_size(x_9);
x_17 = lean_nat_dec_lt(x_10, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_14, x_15, x_11, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_19 = lean_array_fget(x_9, x_10);
lean_inc(x_11);
x_20 = l_Lean_Meta_getFVarLocalDecl(x_19, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_LocalDecl_type(x_21);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_23);
x_24 = l_Lean_Meta_isClassQuick___main(x_23, x_11, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_19);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_10, x_27);
lean_dec(x_10);
x_10 = x_28;
x_12 = x_26;
goto _start;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_10, x_32);
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_30, 2);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 2);
x_38 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_35, 2, x_38);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_11, 2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_19);
x_42 = lean_array_push(x_40, x_41);
lean_ctor_set(x_11, 2, x_42);
x_43 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_11, x_30);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_44, 2);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_45, 2);
lean_dec(x_51);
lean_ctor_set(x_45, 2, x_37);
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_37);
lean_ctor_set(x_44, 2, x_54);
return x_43;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_44, 0);
x_56 = lean_ctor_get(x_44, 1);
x_57 = lean_ctor_get(x_44, 3);
x_58 = lean_ctor_get(x_44, 4);
x_59 = lean_ctor_get(x_44, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_44);
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 x_62 = x_45;
} else {
 lean_dec_ref(x_45);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_37);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set(x_64, 4, x_58);
lean_ctor_set(x_64, 5, x_59);
lean_ctor_set(x_43, 1, x_64);
return x_43;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_43, 0);
lean_inc(x_65);
lean_dec(x_43);
x_66 = lean_ctor_get(x_44, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_44, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_44, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_44, 5);
lean_inc(x_70);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 lean_ctor_release(x_44, 5);
 x_71 = x_44;
} else {
 lean_dec_ref(x_44);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_45, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_45, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 x_74 = x_45;
} else {
 lean_dec_ref(x_45);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 3, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_37);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_68);
lean_ctor_set(x_76, 4, x_69);
lean_ctor_set(x_76, 5, x_70);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_43, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 2);
lean_inc(x_79);
x_80 = !lean_is_exclusive(x_43);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_43, 1);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_78);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_78, 2);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_79, 2);
lean_dec(x_85);
lean_ctor_set(x_79, 2, x_37);
return x_43;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_79);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_37);
lean_ctor_set(x_78, 2, x_88);
return x_43;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_78, 0);
x_90 = lean_ctor_get(x_78, 1);
x_91 = lean_ctor_get(x_78, 3);
x_92 = lean_ctor_get(x_78, 4);
x_93 = lean_ctor_get(x_78, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_78);
x_94 = lean_ctor_get(x_79, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 x_96 = x_79;
} else {
 lean_dec_ref(x_79);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 3, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_37);
x_98 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_91);
lean_ctor_set(x_98, 4, x_92);
lean_ctor_set(x_98, 5, x_93);
lean_ctor_set(x_43, 1, x_98);
return x_43;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_99 = lean_ctor_get(x_43, 0);
lean_inc(x_99);
lean_dec(x_43);
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_78, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_78, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_78, 5);
lean_inc(x_104);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 x_105 = x_78;
} else {
 lean_dec_ref(x_78);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_79, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_79, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 x_108 = x_79;
} else {
 lean_dec_ref(x_79);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 3, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_37);
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set(x_110, 4, x_103);
lean_ctor_set(x_110, 5, x_104);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_11, 0);
x_113 = lean_ctor_get(x_11, 1);
x_114 = lean_ctor_get(x_11, 2);
x_115 = lean_ctor_get(x_11, 3);
x_116 = lean_ctor_get(x_11, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_11);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_31);
lean_ctor_set(x_117, 1, x_19);
x_118 = lean_array_push(x_114, x_117);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_115);
lean_ctor_set(x_119, 4, x_116);
x_120 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_119, x_30);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
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
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 x_133 = x_122;
} else {
 lean_dec_ref(x_122);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 3, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_134, 2, x_37);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(0, 6, 0);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_126);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_127);
lean_ctor_set(x_135, 4, x_128);
lean_ctor_set(x_135, 5, x_129);
if (lean_is_scalar(x_124)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_124;
}
lean_ctor_set(x_136, 0, x_123);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_137 = lean_ctor_get(x_120, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_120, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_140 = x_120;
} else {
 lean_dec_ref(x_120);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 4);
lean_inc(x_144);
x_145 = lean_ctor_get(x_137, 5);
lean_inc(x_145);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 lean_ctor_release(x_137, 5);
 x_146 = x_137;
} else {
 lean_dec_ref(x_137);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 x_149 = x_138;
} else {
 lean_dec_ref(x_138);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 3, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
lean_ctor_set(x_150, 2, x_37);
if (lean_is_scalar(x_146)) {
 x_151 = lean_alloc_ctor(0, 6, 0);
} else {
 x_151 = x_146;
}
lean_ctor_set(x_151, 0, x_141);
lean_ctor_set(x_151, 1, x_142);
lean_ctor_set(x_151, 2, x_150);
lean_ctor_set(x_151, 3, x_143);
lean_ctor_set(x_151, 4, x_144);
lean_ctor_set(x_151, 5, x_145);
if (lean_is_scalar(x_140)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_140;
}
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_153 = lean_ctor_get(x_35, 0);
x_154 = lean_ctor_get(x_35, 1);
x_155 = lean_ctor_get(x_35, 2);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_35);
x_156 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_154);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_30, 2, x_157);
x_158 = lean_ctor_get(x_11, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_11, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_11, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_11, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_11, 4);
lean_inc(x_162);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_163 = x_11;
} else {
 lean_dec_ref(x_11);
 x_163 = lean_box(0);
}
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_31);
lean_ctor_set(x_164, 1, x_19);
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
x_167 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_166, x_30);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_168, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_168, 4);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 5);
lean_inc(x_176);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 lean_ctor_release(x_168, 5);
 x_177 = x_168;
} else {
 lean_dec_ref(x_168);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_169, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_169, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 x_180 = x_169;
} else {
 lean_dec_ref(x_169);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 3, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
lean_ctor_set(x_181, 2, x_155);
if (lean_is_scalar(x_177)) {
 x_182 = lean_alloc_ctor(0, 6, 0);
} else {
 x_182 = x_177;
}
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_173);
lean_ctor_set(x_182, 2, x_181);
lean_ctor_set(x_182, 3, x_174);
lean_ctor_set(x_182, 4, x_175);
lean_ctor_set(x_182, 5, x_176);
if (lean_is_scalar(x_171)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_171;
}
lean_ctor_set(x_183, 0, x_170);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_184 = lean_ctor_get(x_167, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_167, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_187 = x_167;
} else {
 lean_dec_ref(x_167);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 4);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 5);
lean_inc(x_192);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 x_193 = x_184;
} else {
 lean_dec_ref(x_184);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_185, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_185, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 x_196 = x_185;
} else {
 lean_dec_ref(x_185);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 3, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
lean_ctor_set(x_197, 2, x_155);
if (lean_is_scalar(x_193)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_193;
}
lean_ctor_set(x_198, 0, x_188);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_197);
lean_ctor_set(x_198, 3, x_190);
lean_ctor_set(x_198, 4, x_191);
lean_ctor_set(x_198, 5, x_192);
if (lean_is_scalar(x_187)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_187;
}
lean_ctor_set(x_199, 0, x_186);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_200 = lean_ctor_get(x_30, 2);
x_201 = lean_ctor_get(x_30, 0);
x_202 = lean_ctor_get(x_30, 1);
x_203 = lean_ctor_get(x_30, 3);
x_204 = lean_ctor_get(x_30, 4);
x_205 = lean_ctor_get(x_30, 5);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_200);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_30);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 2);
lean_inc(x_208);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 x_209 = x_200;
} else {
 lean_dec_ref(x_200);
 x_209 = lean_box(0);
}
x_210 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(0, 3, 0);
} else {
 x_211 = x_209;
}
lean_ctor_set(x_211, 0, x_206);
lean_ctor_set(x_211, 1, x_207);
lean_ctor_set(x_211, 2, x_210);
x_212 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_212, 0, x_201);
lean_ctor_set(x_212, 1, x_202);
lean_ctor_set(x_212, 2, x_211);
lean_ctor_set(x_212, 3, x_203);
lean_ctor_set(x_212, 4, x_204);
lean_ctor_set(x_212, 5, x_205);
x_213 = lean_ctor_get(x_11, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_11, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_11, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_11, 3);
lean_inc(x_216);
x_217 = lean_ctor_get(x_11, 4);
lean_inc(x_217);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_218 = x_11;
} else {
 lean_dec_ref(x_11);
 x_218 = lean_box(0);
}
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_31);
lean_ctor_set(x_219, 1, x_19);
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
x_222 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_221, x_212);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_223, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 3);
lean_inc(x_229);
x_230 = lean_ctor_get(x_223, 4);
lean_inc(x_230);
x_231 = lean_ctor_get(x_223, 5);
lean_inc(x_231);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 lean_ctor_release(x_223, 3);
 lean_ctor_release(x_223, 4);
 lean_ctor_release(x_223, 5);
 x_232 = x_223;
} else {
 lean_dec_ref(x_223);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_224, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_224, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 lean_ctor_release(x_224, 2);
 x_235 = x_224;
} else {
 lean_dec_ref(x_224);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(0, 3, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
lean_ctor_set(x_236, 2, x_208);
if (lean_is_scalar(x_232)) {
 x_237 = lean_alloc_ctor(0, 6, 0);
} else {
 x_237 = x_232;
}
lean_ctor_set(x_237, 0, x_227);
lean_ctor_set(x_237, 1, x_228);
lean_ctor_set(x_237, 2, x_236);
lean_ctor_set(x_237, 3, x_229);
lean_ctor_set(x_237, 4, x_230);
lean_ctor_set(x_237, 5, x_231);
if (lean_is_scalar(x_226)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_226;
}
lean_ctor_set(x_238, 0, x_225);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_239 = lean_ctor_get(x_222, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_239, 2);
lean_inc(x_240);
x_241 = lean_ctor_get(x_222, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_242 = x_222;
} else {
 lean_dec_ref(x_222);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_239, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_239, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_239, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_239, 5);
lean_inc(x_247);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 lean_ctor_release(x_239, 3);
 lean_ctor_release(x_239, 4);
 lean_ctor_release(x_239, 5);
 x_248 = x_239;
} else {
 lean_dec_ref(x_239);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_240, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_240, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_251 = x_240;
} else {
 lean_dec_ref(x_240);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(0, 3, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
lean_ctor_set(x_252, 2, x_208);
if (lean_is_scalar(x_248)) {
 x_253 = lean_alloc_ctor(0, 6, 0);
} else {
 x_253 = x_248;
}
lean_ctor_set(x_253, 0, x_243);
lean_ctor_set(x_253, 1, x_244);
lean_ctor_set(x_253, 2, x_252);
lean_ctor_set(x_253, 3, x_245);
lean_ctor_set(x_253, 4, x_246);
lean_ctor_set(x_253, 5, x_247);
if (lean_is_scalar(x_242)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_242;
}
lean_ctor_set(x_254, 0, x_241);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
default: 
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_24, 1);
lean_inc(x_255);
lean_dec(x_24);
lean_inc(x_11);
x_256 = l_Lean_Meta_isClassExpensive___main(x_23, x_11, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_19);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_nat_add(x_10, x_259);
lean_dec(x_10);
x_10 = x_260;
x_12 = x_258;
goto _start;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_256, 1);
lean_inc(x_262);
lean_dec(x_256);
x_263 = lean_ctor_get(x_257, 0);
lean_inc(x_263);
lean_dec(x_257);
x_264 = lean_unsigned_to_nat(1u);
x_265 = lean_nat_add(x_10, x_264);
lean_dec(x_10);
x_266 = !lean_is_exclusive(x_262);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_262, 2);
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_269 = lean_ctor_get(x_267, 2);
x_270 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_267, 2, x_270);
x_271 = !lean_is_exclusive(x_11);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_11, 2);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_263);
lean_ctor_set(x_273, 1, x_19);
x_274 = lean_array_push(x_272, x_273);
lean_ctor_set(x_11, 2, x_274);
x_275 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_265, x_11, x_262);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_276, 2);
lean_inc(x_277);
x_278 = !lean_is_exclusive(x_275);
if (x_278 == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_275, 1);
lean_dec(x_279);
x_280 = !lean_is_exclusive(x_276);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_276, 2);
lean_dec(x_281);
x_282 = !lean_is_exclusive(x_277);
if (x_282 == 0)
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_277, 2);
lean_dec(x_283);
lean_ctor_set(x_277, 2, x_269);
return x_275;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_277, 0);
x_285 = lean_ctor_get(x_277, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_277);
x_286 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
lean_ctor_set(x_286, 2, x_269);
lean_ctor_set(x_276, 2, x_286);
return x_275;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_287 = lean_ctor_get(x_276, 0);
x_288 = lean_ctor_get(x_276, 1);
x_289 = lean_ctor_get(x_276, 3);
x_290 = lean_ctor_get(x_276, 4);
x_291 = lean_ctor_get(x_276, 5);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_276);
x_292 = lean_ctor_get(x_277, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_277, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 x_294 = x_277;
} else {
 lean_dec_ref(x_277);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(0, 3, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
lean_ctor_set(x_295, 2, x_269);
x_296 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_296, 0, x_287);
lean_ctor_set(x_296, 1, x_288);
lean_ctor_set(x_296, 2, x_295);
lean_ctor_set(x_296, 3, x_289);
lean_ctor_set(x_296, 4, x_290);
lean_ctor_set(x_296, 5, x_291);
lean_ctor_set(x_275, 1, x_296);
return x_275;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_297 = lean_ctor_get(x_275, 0);
lean_inc(x_297);
lean_dec(x_275);
x_298 = lean_ctor_get(x_276, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_276, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_276, 3);
lean_inc(x_300);
x_301 = lean_ctor_get(x_276, 4);
lean_inc(x_301);
x_302 = lean_ctor_get(x_276, 5);
lean_inc(x_302);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 lean_ctor_release(x_276, 4);
 lean_ctor_release(x_276, 5);
 x_303 = x_276;
} else {
 lean_dec_ref(x_276);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_277, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_277, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 x_306 = x_277;
} else {
 lean_dec_ref(x_277);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(0, 3, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
lean_ctor_set(x_307, 2, x_269);
if (lean_is_scalar(x_303)) {
 x_308 = lean_alloc_ctor(0, 6, 0);
} else {
 x_308 = x_303;
}
lean_ctor_set(x_308, 0, x_298);
lean_ctor_set(x_308, 1, x_299);
lean_ctor_set(x_308, 2, x_307);
lean_ctor_set(x_308, 3, x_300);
lean_ctor_set(x_308, 4, x_301);
lean_ctor_set(x_308, 5, x_302);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_297);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_310 = lean_ctor_get(x_275, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_310, 2);
lean_inc(x_311);
x_312 = !lean_is_exclusive(x_275);
if (x_312 == 0)
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_ctor_get(x_275, 1);
lean_dec(x_313);
x_314 = !lean_is_exclusive(x_310);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_310, 2);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_311);
if (x_316 == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_311, 2);
lean_dec(x_317);
lean_ctor_set(x_311, 2, x_269);
return x_275;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_311, 0);
x_319 = lean_ctor_get(x_311, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_311);
x_320 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
lean_ctor_set(x_320, 2, x_269);
lean_ctor_set(x_310, 2, x_320);
return x_275;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_321 = lean_ctor_get(x_310, 0);
x_322 = lean_ctor_get(x_310, 1);
x_323 = lean_ctor_get(x_310, 3);
x_324 = lean_ctor_get(x_310, 4);
x_325 = lean_ctor_get(x_310, 5);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_310);
x_326 = lean_ctor_get(x_311, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_311, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 lean_ctor_release(x_311, 2);
 x_328 = x_311;
} else {
 lean_dec_ref(x_311);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 3, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
lean_ctor_set(x_329, 2, x_269);
x_330 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_330, 0, x_321);
lean_ctor_set(x_330, 1, x_322);
lean_ctor_set(x_330, 2, x_329);
lean_ctor_set(x_330, 3, x_323);
lean_ctor_set(x_330, 4, x_324);
lean_ctor_set(x_330, 5, x_325);
lean_ctor_set(x_275, 1, x_330);
return x_275;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_331 = lean_ctor_get(x_275, 0);
lean_inc(x_331);
lean_dec(x_275);
x_332 = lean_ctor_get(x_310, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_310, 1);
lean_inc(x_333);
x_334 = lean_ctor_get(x_310, 3);
lean_inc(x_334);
x_335 = lean_ctor_get(x_310, 4);
lean_inc(x_335);
x_336 = lean_ctor_get(x_310, 5);
lean_inc(x_336);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 lean_ctor_release(x_310, 2);
 lean_ctor_release(x_310, 3);
 lean_ctor_release(x_310, 4);
 lean_ctor_release(x_310, 5);
 x_337 = x_310;
} else {
 lean_dec_ref(x_310);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_311, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_311, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 lean_ctor_release(x_311, 2);
 x_340 = x_311;
} else {
 lean_dec_ref(x_311);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(0, 3, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
lean_ctor_set(x_341, 2, x_269);
if (lean_is_scalar(x_337)) {
 x_342 = lean_alloc_ctor(0, 6, 0);
} else {
 x_342 = x_337;
}
lean_ctor_set(x_342, 0, x_332);
lean_ctor_set(x_342, 1, x_333);
lean_ctor_set(x_342, 2, x_341);
lean_ctor_set(x_342, 3, x_334);
lean_ctor_set(x_342, 4, x_335);
lean_ctor_set(x_342, 5, x_336);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_331);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_344 = lean_ctor_get(x_11, 0);
x_345 = lean_ctor_get(x_11, 1);
x_346 = lean_ctor_get(x_11, 2);
x_347 = lean_ctor_get(x_11, 3);
x_348 = lean_ctor_get(x_11, 4);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_11);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_263);
lean_ctor_set(x_349, 1, x_19);
x_350 = lean_array_push(x_346, x_349);
x_351 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_351, 0, x_344);
lean_ctor_set(x_351, 1, x_345);
lean_ctor_set(x_351, 2, x_350);
lean_ctor_set(x_351, 3, x_347);
lean_ctor_set(x_351, 4, x_348);
x_352 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_265, x_351, x_262);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_353, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_356 = x_352;
} else {
 lean_dec_ref(x_352);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_353, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_353, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_353, 3);
lean_inc(x_359);
x_360 = lean_ctor_get(x_353, 4);
lean_inc(x_360);
x_361 = lean_ctor_get(x_353, 5);
lean_inc(x_361);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 lean_ctor_release(x_353, 4);
 lean_ctor_release(x_353, 5);
 x_362 = x_353;
} else {
 lean_dec_ref(x_353);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_354, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_354, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 x_365 = x_354;
} else {
 lean_dec_ref(x_354);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(0, 3, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
lean_ctor_set(x_366, 2, x_269);
if (lean_is_scalar(x_362)) {
 x_367 = lean_alloc_ctor(0, 6, 0);
} else {
 x_367 = x_362;
}
lean_ctor_set(x_367, 0, x_357);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_366);
lean_ctor_set(x_367, 3, x_359);
lean_ctor_set(x_367, 4, x_360);
lean_ctor_set(x_367, 5, x_361);
if (lean_is_scalar(x_356)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_356;
}
lean_ctor_set(x_368, 0, x_355);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_369 = lean_ctor_get(x_352, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_369, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_352, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_372 = x_352;
} else {
 lean_dec_ref(x_352);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_369, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_369, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_369, 4);
lean_inc(x_376);
x_377 = lean_ctor_get(x_369, 5);
lean_inc(x_377);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 lean_ctor_release(x_369, 4);
 lean_ctor_release(x_369, 5);
 x_378 = x_369;
} else {
 lean_dec_ref(x_369);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_370, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_370, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 lean_ctor_release(x_370, 2);
 x_381 = x_370;
} else {
 lean_dec_ref(x_370);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(0, 3, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
lean_ctor_set(x_382, 2, x_269);
if (lean_is_scalar(x_378)) {
 x_383 = lean_alloc_ctor(0, 6, 0);
} else {
 x_383 = x_378;
}
lean_ctor_set(x_383, 0, x_373);
lean_ctor_set(x_383, 1, x_374);
lean_ctor_set(x_383, 2, x_382);
lean_ctor_set(x_383, 3, x_375);
lean_ctor_set(x_383, 4, x_376);
lean_ctor_set(x_383, 5, x_377);
if (lean_is_scalar(x_372)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_372;
}
lean_ctor_set(x_384, 0, x_371);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_385 = lean_ctor_get(x_267, 0);
x_386 = lean_ctor_get(x_267, 1);
x_387 = lean_ctor_get(x_267, 2);
lean_inc(x_387);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_267);
x_388 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_389 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_389, 0, x_385);
lean_ctor_set(x_389, 1, x_386);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_262, 2, x_389);
x_390 = lean_ctor_get(x_11, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_11, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_11, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_11, 3);
lean_inc(x_393);
x_394 = lean_ctor_get(x_11, 4);
lean_inc(x_394);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_395 = x_11;
} else {
 lean_dec_ref(x_11);
 x_395 = lean_box(0);
}
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_263);
lean_ctor_set(x_396, 1, x_19);
x_397 = lean_array_push(x_392, x_396);
if (lean_is_scalar(x_395)) {
 x_398 = lean_alloc_ctor(0, 5, 0);
} else {
 x_398 = x_395;
}
lean_ctor_set(x_398, 0, x_390);
lean_ctor_set(x_398, 1, x_391);
lean_ctor_set(x_398, 2, x_397);
lean_ctor_set(x_398, 3, x_393);
lean_ctor_set(x_398, 4, x_394);
x_399 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_265, x_398, x_262);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_400, 2);
lean_inc(x_401);
x_402 = lean_ctor_get(x_399, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_403 = x_399;
} else {
 lean_dec_ref(x_399);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_400, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_400, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_400, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_400, 4);
lean_inc(x_407);
x_408 = lean_ctor_get(x_400, 5);
lean_inc(x_408);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 lean_ctor_release(x_400, 2);
 lean_ctor_release(x_400, 3);
 lean_ctor_release(x_400, 4);
 lean_ctor_release(x_400, 5);
 x_409 = x_400;
} else {
 lean_dec_ref(x_400);
 x_409 = lean_box(0);
}
x_410 = lean_ctor_get(x_401, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_401, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 lean_ctor_release(x_401, 2);
 x_412 = x_401;
} else {
 lean_dec_ref(x_401);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(0, 3, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
lean_ctor_set(x_413, 2, x_387);
if (lean_is_scalar(x_409)) {
 x_414 = lean_alloc_ctor(0, 6, 0);
} else {
 x_414 = x_409;
}
lean_ctor_set(x_414, 0, x_404);
lean_ctor_set(x_414, 1, x_405);
lean_ctor_set(x_414, 2, x_413);
lean_ctor_set(x_414, 3, x_406);
lean_ctor_set(x_414, 4, x_407);
lean_ctor_set(x_414, 5, x_408);
if (lean_is_scalar(x_403)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_403;
}
lean_ctor_set(x_415, 0, x_402);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_416 = lean_ctor_get(x_399, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_416, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_399, 0);
lean_inc(x_418);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_419 = x_399;
} else {
 lean_dec_ref(x_399);
 x_419 = lean_box(0);
}
x_420 = lean_ctor_get(x_416, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_416, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_416, 3);
lean_inc(x_422);
x_423 = lean_ctor_get(x_416, 4);
lean_inc(x_423);
x_424 = lean_ctor_get(x_416, 5);
lean_inc(x_424);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 lean_ctor_release(x_416, 4);
 lean_ctor_release(x_416, 5);
 x_425 = x_416;
} else {
 lean_dec_ref(x_416);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_417, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_417, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 x_428 = x_417;
} else {
 lean_dec_ref(x_417);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(0, 3, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
lean_ctor_set(x_429, 2, x_387);
if (lean_is_scalar(x_425)) {
 x_430 = lean_alloc_ctor(0, 6, 0);
} else {
 x_430 = x_425;
}
lean_ctor_set(x_430, 0, x_420);
lean_ctor_set(x_430, 1, x_421);
lean_ctor_set(x_430, 2, x_429);
lean_ctor_set(x_430, 3, x_422);
lean_ctor_set(x_430, 4, x_423);
lean_ctor_set(x_430, 5, x_424);
if (lean_is_scalar(x_419)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_419;
}
lean_ctor_set(x_431, 0, x_418);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_432 = lean_ctor_get(x_262, 2);
x_433 = lean_ctor_get(x_262, 0);
x_434 = lean_ctor_get(x_262, 1);
x_435 = lean_ctor_get(x_262, 3);
x_436 = lean_ctor_get(x_262, 4);
x_437 = lean_ctor_get(x_262, 5);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
lean_inc(x_432);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_262);
x_438 = lean_ctor_get(x_432, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_432, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_432, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 x_441 = x_432;
} else {
 lean_dec_ref(x_432);
 x_441 = lean_box(0);
}
x_442 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(0, 3, 0);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_438);
lean_ctor_set(x_443, 1, x_439);
lean_ctor_set(x_443, 2, x_442);
x_444 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_444, 0, x_433);
lean_ctor_set(x_444, 1, x_434);
lean_ctor_set(x_444, 2, x_443);
lean_ctor_set(x_444, 3, x_435);
lean_ctor_set(x_444, 4, x_436);
lean_ctor_set(x_444, 5, x_437);
x_445 = lean_ctor_get(x_11, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_11, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_11, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_11, 3);
lean_inc(x_448);
x_449 = lean_ctor_get(x_11, 4);
lean_inc(x_449);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_450 = x_11;
} else {
 lean_dec_ref(x_11);
 x_450 = lean_box(0);
}
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_263);
lean_ctor_set(x_451, 1, x_19);
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
x_454 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_265, x_453, x_444);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_455 = lean_ctor_get(x_454, 1);
lean_inc(x_455);
x_456 = lean_ctor_get(x_455, 2);
lean_inc(x_456);
x_457 = lean_ctor_get(x_454, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 x_458 = x_454;
} else {
 lean_dec_ref(x_454);
 x_458 = lean_box(0);
}
x_459 = lean_ctor_get(x_455, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_455, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_455, 3);
lean_inc(x_461);
x_462 = lean_ctor_get(x_455, 4);
lean_inc(x_462);
x_463 = lean_ctor_get(x_455, 5);
lean_inc(x_463);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 lean_ctor_release(x_455, 2);
 lean_ctor_release(x_455, 3);
 lean_ctor_release(x_455, 4);
 lean_ctor_release(x_455, 5);
 x_464 = x_455;
} else {
 lean_dec_ref(x_455);
 x_464 = lean_box(0);
}
x_465 = lean_ctor_get(x_456, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_456, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 lean_ctor_release(x_456, 2);
 x_467 = x_456;
} else {
 lean_dec_ref(x_456);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(0, 3, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_466);
lean_ctor_set(x_468, 2, x_440);
if (lean_is_scalar(x_464)) {
 x_469 = lean_alloc_ctor(0, 6, 0);
} else {
 x_469 = x_464;
}
lean_ctor_set(x_469, 0, x_459);
lean_ctor_set(x_469, 1, x_460);
lean_ctor_set(x_469, 2, x_468);
lean_ctor_set(x_469, 3, x_461);
lean_ctor_set(x_469, 4, x_462);
lean_ctor_set(x_469, 5, x_463);
if (lean_is_scalar(x_458)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_458;
}
lean_ctor_set(x_470, 0, x_457);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_471 = lean_ctor_get(x_454, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_471, 2);
lean_inc(x_472);
x_473 = lean_ctor_get(x_454, 0);
lean_inc(x_473);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 x_474 = x_454;
} else {
 lean_dec_ref(x_454);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_471, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_471, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_471, 3);
lean_inc(x_477);
x_478 = lean_ctor_get(x_471, 4);
lean_inc(x_478);
x_479 = lean_ctor_get(x_471, 5);
lean_inc(x_479);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 lean_ctor_release(x_471, 2);
 lean_ctor_release(x_471, 3);
 lean_ctor_release(x_471, 4);
 lean_ctor_release(x_471, 5);
 x_480 = x_471;
} else {
 lean_dec_ref(x_471);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_472, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_472, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 lean_ctor_release(x_472, 2);
 x_483 = x_472;
} else {
 lean_dec_ref(x_472);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(0, 3, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_482);
lean_ctor_set(x_484, 2, x_440);
if (lean_is_scalar(x_480)) {
 x_485 = lean_alloc_ctor(0, 6, 0);
} else {
 x_485 = x_480;
}
lean_ctor_set(x_485, 0, x_475);
lean_ctor_set(x_485, 1, x_476);
lean_ctor_set(x_485, 2, x_484);
lean_ctor_set(x_485, 3, x_477);
lean_ctor_set(x_485, 4, x_478);
lean_ctor_set(x_485, 5, x_479);
if (lean_is_scalar(x_474)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_474;
}
lean_ctor_set(x_486, 0, x_473);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_487 = !lean_is_exclusive(x_256);
if (x_487 == 0)
{
return x_256;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_256, 0);
x_489 = lean_ctor_get(x_256, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_256);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
}
}
else
{
uint8_t x_491; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_491 = !lean_is_exclusive(x_24);
if (x_491 == 0)
{
return x_24;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_24, 0);
x_493 = lean_ctor_get(x_24, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_24);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
else
{
uint8_t x_495; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_20);
if (x_495 == 0)
{
return x_20;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_20, 0);
x_497 = lean_ctor_get(x_20, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_20);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
switch (lean_obj_tag(x_7)) {
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_30 = lean_array_get_size(x_4);
x_31 = lean_expr_instantiate_rev_range(x_27, x_5, x_30, x_4);
lean_dec(x_30);
lean_dec(x_27);
x_32 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_3);
x_35 = l_Lean_Meta_mkAuxName(x_3, x_26, x_6);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = (uint8_t)((x_29 << 24) >> 61);
lean_inc(x_33);
x_39 = lean_local_ctx_mk_local_decl(x_3, x_33, x_36, x_31, x_38);
x_40 = l_Lean_mkFVar(x_33);
x_41 = lean_array_push(x_4, x_40);
x_2 = x_13;
x_3 = x_39;
x_4 = x_41;
x_6 = x_37;
x_7 = x_28;
x_9 = x_34;
goto _start;
}
case 8:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 3);
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_array_get_size(x_4);
x_48 = lean_expr_instantiate_rev_range(x_44, x_5, x_47, x_4);
lean_dec(x_44);
x_49 = lean_expr_instantiate_rev_range(x_45, x_5, x_47, x_4);
lean_dec(x_47);
lean_dec(x_45);
x_50 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_3);
x_53 = l_Lean_Meta_mkAuxName(x_3, x_43, x_6);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_51);
x_56 = lean_local_ctx_mk_let_decl(x_3, x_51, x_54, x_48, x_49);
x_57 = l_Lean_mkFVar(x_51);
x_58 = lean_array_push(x_4, x_57);
x_2 = x_13;
x_3 = x_56;
x_4 = x_58;
x_6 = x_55;
x_7 = x_46;
x_9 = x_52;
goto _start;
}
default: 
{
lean_object* x_60; 
x_60 = lean_box(0);
x_14 = x_60;
goto block_25;
}
}
block_25:
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_14);
x_15 = lean_array_get_size(x_4);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_dec(x_17);
lean_inc(x_3);
lean_ctor_set(x_8, 1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_3, x_4, x_5, x_6, x_7, x_13, x_15, x_4, x_5, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
lean_inc(x_3);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_3, x_4, x_5, x_6, x_7, x_13, x_15, x_4, x_5, x_23, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_6);
lean_dec(x_2);
x_61 = lean_array_get_size(x_4);
x_62 = lean_expr_instantiate_rev_range(x_7, x_5, x_61, x_4);
lean_dec(x_61);
lean_dec(x_7);
x_63 = !lean_is_exclusive(x_8);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_8, 1);
lean_dec(x_64);
lean_ctor_set(x_8, 1, x_3);
lean_inc(x_4);
x_65 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_4, x_62, x_4, x_5, x_8, x_9);
lean_dec(x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_8, 0);
x_67 = lean_ctor_get(x_8, 2);
x_68 = lean_ctor_get(x_8, 3);
x_69 = lean_ctor_get(x_8, 4);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_8);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_3);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_68);
lean_ctor_set(x_70, 4, x_69);
lean_inc(x_4);
x_71 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_4, x_62, x_4, x_5, x_70, x_9);
lean_dec(x_4);
return x_71;
}
}
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_Meta_getMVarDecl(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 4);
lean_inc(x_15);
x_16 = lean_array_get_size(x_11);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_10);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_13);
if (x_18 == 0)
{
lean_object* x_212; 
lean_dec(x_15);
lean_dec(x_7);
x_212 = lean_box(0);
x_20 = x_212;
goto block_211;
}
else
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_unsigned_to_nat(0u);
x_214 = l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5(x_4, x_7, lean_box(0), x_11, x_15, x_213);
lean_dec(x_15);
lean_dec(x_7);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_box(0);
x_20 = x_215;
goto block_211;
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_9);
x_216 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_217 = l_Lean_Meta_checkNotAssigned(x_1, x_216, x_19, x_8);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
lean_inc(x_1);
x_219 = l_Lean_Meta_getMVarType(x_1, x_19, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = l_Array_empty___closed__1;
x_223 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_14, x_222, x_213, x_3, x_220, x_19, x_221);
return x_223;
}
else
{
uint8_t x_224; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_219);
if (x_224 == 0)
{
return x_219;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_219, 0);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_219);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_217);
if (x_228 == 0)
{
return x_217;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_217, 0);
x_230 = lean_ctor_get(x_217, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_217);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
block_211:
{
uint8_t x_21; 
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_8, 2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_24 = lean_ctor_get(x_22, 2);
x_49 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_22, 2, x_49);
x_50 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_51 = l_Lean_Meta_checkNotAssigned(x_1, x_50, x_19, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_1);
x_53 = l_Lean_Meta_getMVarType(x_1, x_19, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Array_empty___closed__1;
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_14, x_56, x_57, x_3, x_54, x_19, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_9);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 2);
lean_inc(x_60);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_58, 1);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_59, 2);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 2);
lean_dec(x_66);
lean_ctor_set(x_60, 2, x_24);
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_24);
lean_ctor_set(x_59, 2, x_69);
return x_58;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_59, 0);
x_71 = lean_ctor_get(x_59, 1);
x_72 = lean_ctor_get(x_59, 3);
x_73 = lean_ctor_get(x_59, 4);
x_74 = lean_ctor_get(x_59, 5);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_59);
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 x_77 = x_60;
} else {
 lean_dec_ref(x_60);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 3, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_24);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_72);
lean_ctor_set(x_79, 4, x_73);
lean_ctor_set(x_79, 5, x_74);
lean_ctor_set(x_58, 1, x_79);
return x_58;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_80 = lean_ctor_get(x_58, 0);
lean_inc(x_80);
lean_dec(x_58);
x_81 = lean_ctor_get(x_59, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_59, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_59, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_59, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_59, 5);
lean_inc(x_85);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_86 = x_59;
} else {
 lean_dec_ref(x_59);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_60, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_60, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 x_89 = x_60;
} else {
 lean_dec_ref(x_60);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_90, 2, x_24);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(0, 6, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_82);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set(x_91, 3, x_83);
lean_ctor_set(x_91, 4, x_84);
lean_ctor_set(x_91, 5, x_85);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_80);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_58, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_58, 1);
lean_inc(x_94);
lean_dec(x_58);
x_25 = x_93;
x_26 = x_94;
goto block_48;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_53, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_53, 1);
lean_inc(x_96);
lean_dec(x_53);
x_25 = x_95;
x_26 = x_96;
goto block_48;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_51, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_51, 1);
lean_inc(x_98);
lean_dec(x_51);
x_25 = x_97;
x_26 = x_98;
goto block_48;
}
block_48:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 2);
lean_dec(x_30);
lean_ctor_set(x_28, 2, x_24);
if (lean_is_scalar(x_9)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_9;
 lean_ctor_set_tag(x_31, 1);
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_26, 2, x_34);
if (lean_is_scalar(x_9)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_9;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_26, 2);
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
x_39 = lean_ctor_get(x_26, 3);
x_40 = lean_ctor_get(x_26, 4);
x_41 = lean_ctor_get(x_26, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_36);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 3, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_24);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_41);
if (lean_is_scalar(x_9)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_9;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_25);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_99 = lean_ctor_get(x_22, 0);
x_100 = lean_ctor_get(x_22, 1);
x_101 = lean_ctor_get(x_22, 2);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_22);
x_118 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_99);
lean_ctor_set(x_119, 1, x_100);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_8, 2, x_119);
x_120 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_121 = l_Lean_Meta_checkNotAssigned(x_1, x_120, x_19, x_8);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
lean_inc(x_1);
x_123 = l_Lean_Meta_getMVarType(x_1, x_19, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Array_empty___closed__1;
x_127 = lean_unsigned_to_nat(0u);
x_128 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_14, x_126, x_127, x_3, x_124, x_19, x_125);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_9);
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
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 x_141 = x_130;
} else {
 lean_dec_ref(x_130);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 3, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_101);
if (lean_is_scalar(x_138)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_138;
}
lean_ctor_set(x_143, 0, x_133);
lean_ctor_set(x_143, 1, x_134);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set(x_143, 3, x_135);
lean_ctor_set(x_143, 4, x_136);
lean_ctor_set(x_143, 5, x_137);
if (lean_is_scalar(x_132)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_132;
}
lean_ctor_set(x_144, 0, x_131);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_128, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_128, 1);
lean_inc(x_146);
lean_dec(x_128);
x_102 = x_145;
x_103 = x_146;
goto block_117;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_ctor_get(x_123, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_123, 1);
lean_inc(x_148);
lean_dec(x_123);
x_102 = x_147;
x_103 = x_148;
goto block_117;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_121, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_121, 1);
lean_inc(x_150);
lean_dec(x_121);
x_102 = x_149;
x_103 = x_150;
goto block_117;
}
block_117:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_104 = lean_ctor_get(x_103, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 5);
lean_inc(x_109);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 x_110 = x_103;
} else {
 lean_dec_ref(x_103);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_104, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_104, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 x_113 = x_104;
} else {
 lean_dec_ref(x_104);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 3, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_101);
if (lean_is_scalar(x_110)) {
 x_115 = lean_alloc_ctor(0, 6, 0);
} else {
 x_115 = x_110;
}
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_106);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_107);
lean_ctor_set(x_115, 4, x_108);
lean_ctor_set(x_115, 5, x_109);
if (lean_is_scalar(x_9)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_9;
 lean_ctor_set_tag(x_116, 1);
}
lean_ctor_set(x_116, 0, x_102);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_151 = lean_ctor_get(x_8, 2);
x_152 = lean_ctor_get(x_8, 0);
x_153 = lean_ctor_get(x_8, 1);
x_154 = lean_ctor_get(x_8, 3);
x_155 = lean_ctor_get(x_8, 4);
x_156 = lean_ctor_get(x_8, 5);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_151);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_8);
x_157 = lean_ctor_get(x_151, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_151, 2);
lean_inc(x_159);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 x_160 = x_151;
} else {
 lean_dec_ref(x_151);
 x_160 = lean_box(0);
}
x_177 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_160)) {
 x_178 = lean_alloc_ctor(0, 3, 0);
} else {
 x_178 = x_160;
}
lean_ctor_set(x_178, 0, x_157);
lean_ctor_set(x_178, 1, x_158);
lean_ctor_set(x_178, 2, x_177);
x_179 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_179, 0, x_152);
lean_ctor_set(x_179, 1, x_153);
lean_ctor_set(x_179, 2, x_178);
lean_ctor_set(x_179, 3, x_154);
lean_ctor_set(x_179, 4, x_155);
lean_ctor_set(x_179, 5, x_156);
x_180 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_181 = l_Lean_Meta_checkNotAssigned(x_1, x_180, x_19, x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
lean_inc(x_1);
x_183 = l_Lean_Meta_getMVarType(x_1, x_19, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l_Array_empty___closed__1;
x_187 = lean_unsigned_to_nat(0u);
x_188 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_14, x_186, x_187, x_3, x_184, x_19, x_185);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_9);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_189, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_192 = x_188;
} else {
 lean_dec_ref(x_188);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_189, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_189, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 5);
lean_inc(x_197);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 x_198 = x_189;
} else {
 lean_dec_ref(x_189);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_190, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_190, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 lean_ctor_release(x_190, 2);
 x_201 = x_190;
} else {
 lean_dec_ref(x_190);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 3, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_159);
if (lean_is_scalar(x_198)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_198;
}
lean_ctor_set(x_203, 0, x_193);
lean_ctor_set(x_203, 1, x_194);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_195);
lean_ctor_set(x_203, 4, x_196);
lean_ctor_set(x_203, 5, x_197);
if (lean_is_scalar(x_192)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_192;
}
lean_ctor_set(x_204, 0, x_191);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_188, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_188, 1);
lean_inc(x_206);
lean_dec(x_188);
x_161 = x_205;
x_162 = x_206;
goto block_176;
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_183, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_183, 1);
lean_inc(x_208);
lean_dec(x_183);
x_161 = x_207;
x_162 = x_208;
goto block_176;
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_181, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_181, 1);
lean_inc(x_210);
lean_dec(x_181);
x_161 = x_209;
x_162 = x_210;
goto block_176;
}
block_176:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_162, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 4);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 5);
lean_inc(x_168);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 lean_ctor_release(x_162, 4);
 lean_ctor_release(x_162, 5);
 x_169 = x_162;
} else {
 lean_dec_ref(x_162);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_163, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_163, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 x_172 = x_163;
} else {
 lean_dec_ref(x_163);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 3, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
lean_ctor_set(x_173, 2, x_159);
if (lean_is_scalar(x_169)) {
 x_174 = lean_alloc_ctor(0, 6, 0);
} else {
 x_174 = x_169;
}
lean_ctor_set(x_174, 0, x_164);
lean_ctor_set(x_174, 1, x_165);
lean_ctor_set(x_174, 2, x_173);
lean_ctor_set(x_174, 3, x_166);
lean_ctor_set(x_174, 4, x_167);
lean_ctor_set(x_174, 5, x_168);
if (lean_is_scalar(x_9)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_9;
 lean_ctor_set_tag(x_175, 1);
}
lean_ctor_set(x_175, 0, x_161);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_232 = !lean_is_exclusive(x_6);
if (x_232 == 0)
{
return x_6;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_6, 0);
x_234 = lean_ctor_get(x_6, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_6);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
}
lean_object* l_Lean_Meta_introN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_introN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_introN(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_intro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1, x_7, x_6, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Expr_Inhabited;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_12, x_14);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = l_Lean_Expr_Inhabited;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get(x_18, x_16, x_19);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Expr_Inhabited;
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get(x_27, x_24, x_28);
lean_dec(x_24);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
lean_object* l_Lean_Meta_intro1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1, x_5, x_4, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_Inhabited;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_10, x_12);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lean_Expr_Inhabited;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_16, x_14, x_17);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_25 = l_Lean_Expr_Inhabited;
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get(x_25, x_22, x_26);
lean_dec(x_22);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_intro1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_intro1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
l_Lean_Meta_mkAuxName___closed__1 = _init_l_Lean_Meta_mkAuxName___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxName___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
