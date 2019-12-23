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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1;
lean_object* lean_metavar_ctx_assign_delayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_appendIndexAfter___closed__1;
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_introNCore___rarg___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalInstance_hasBeq___closed__1;
lean_object* l_Lean_Meta_intro1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_introNCoreAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCoreAux___main(lean_object*);
lean_object* l_Lean_Meta_introNCoreAux(lean_object*);
lean_object* l_Lean_Meta_intro1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`introN` failed, insufficient number of binders");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(19, 1, 0);
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
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
lean_object* l_Lean_Meta_introNCoreAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_metavar_ctx_assign_delayed(x_8, x_1, x_6, x_2, x_3);
lean_ctor_set(x_5, 1, x_9);
x_10 = l_Lean_Expr_mvarId_x21(x_3);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 4);
x_18 = lean_ctor_get(x_5, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_metavar_ctx_assign_delayed(x_14, x_1, x_6, x_2, x_3);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
x_21 = l_Lean_Expr_mvarId_x21(x_3);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_36 = lean_array_get_size(x_5);
x_37 = lean_expr_instantiate_rev_range(x_33, x_6, x_36, x_5);
lean_dec(x_36);
lean_dec(x_33);
x_38 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_2);
lean_inc(x_4);
x_41 = lean_apply_3(x_2, x_4, x_32, x_7);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = (uint8_t)((x_35 << 24) >> 61);
lean_inc(x_39);
x_45 = lean_local_ctx_mk_local_decl(x_4, x_39, x_42, x_37, x_44);
x_46 = l_Lean_mkFVar(x_39);
x_47 = lean_array_push(x_5, x_46);
x_3 = x_14;
x_4 = x_45;
x_5 = x_47;
x_7 = x_43;
x_8 = x_34;
x_10 = x_40;
goto _start;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_49 = lean_ctor_get(x_8, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_8, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_8, 3);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_array_get_size(x_5);
x_54 = lean_expr_instantiate_rev_range(x_50, x_6, x_53, x_5);
lean_dec(x_50);
x_55 = lean_expr_instantiate_rev_range(x_51, x_6, x_53, x_5);
lean_dec(x_53);
lean_dec(x_51);
x_56 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_2);
lean_inc(x_4);
x_59 = lean_apply_3(x_2, x_4, x_49, x_7);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_57);
x_62 = lean_local_ctx_mk_let_decl(x_4, x_57, x_60, x_54, x_55);
x_63 = l_Lean_mkFVar(x_57);
x_64 = lean_array_push(x_5, x_63);
x_3 = x_14;
x_4 = x_62;
x_5 = x_64;
x_7 = x_61;
x_8 = x_52;
x_10 = x_58;
goto _start;
}
default: 
{
lean_object* x_66; 
x_66 = lean_box(0);
x_15 = x_66;
goto block_31;
}
}
block_31:
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_30 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_29, x_5, x_6, x_21, x_28, x_10);
lean_dec(x_5);
return x_30;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_array_get_size(x_5);
x_68 = lean_expr_instantiate_rev_range(x_8, x_6, x_67, x_5);
lean_dec(x_67);
lean_dec(x_8);
x_69 = lean_box(0);
x_70 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar), 4, 2);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_69);
lean_inc(x_5);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__2), 5, 2);
lean_closure_set(x_71, 0, x_1);
lean_closure_set(x_71, 1, x_5);
x_72 = l_EIO_Monad___closed__1;
x_73 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_73, 0, x_72);
lean_closure_set(x_73, 1, lean_box(0));
lean_closure_set(x_73, 2, lean_box(0));
lean_closure_set(x_73, 3, x_70);
lean_closure_set(x_73, 4, x_71);
x_74 = !lean_is_exclusive(x_9);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_9, 1);
lean_dec(x_75);
lean_ctor_set(x_9, 1, x_4);
x_76 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_77 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_76, x_5, x_6, x_73, x_9, x_10);
lean_dec(x_5);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_9, 0);
x_79 = lean_ctor_get(x_9, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_9);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_4);
lean_ctor_set(x_80, 2, x_79);
x_81 = l_Lean_Meta_introNCoreAux___main___rarg___closed__1;
x_82 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_81, x_5, x_6, x_73, x_80, x_10);
lean_dec(x_5);
return x_82;
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
lean_object* _init_l_Lean_Meta_introNCore___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("introN");
return x_1;
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
x_216 = l_Lean_Meta_introNCore___rarg___closed__1;
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
x_49 = l_Lean_Meta_introNCore___rarg___closed__1;
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
x_119 = l_Lean_Meta_introNCore___rarg___closed__1;
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
x_179 = l_Lean_Meta_introNCore___rarg___closed__1;
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
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; 
x_232 = lean_ctor_get(x_5, 0);
x_233 = lean_ctor_get(x_5, 2);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_5);
x_234 = lean_ctor_get(x_8, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_8, 4);
lean_inc(x_235);
lean_dec(x_8);
x_236 = lean_array_get_size(x_233);
x_237 = lean_array_get_size(x_235);
x_238 = lean_nat_dec_eq(x_236, x_237);
lean_dec(x_237);
lean_dec(x_236);
lean_inc(x_235);
lean_inc(x_234);
x_239 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_239, 0, x_232);
lean_ctor_set(x_239, 1, x_234);
lean_ctor_set(x_239, 2, x_235);
if (x_238 == 0)
{
lean_object* x_303; 
lean_dec(x_235);
lean_dec(x_233);
x_303 = lean_box(0);
x_240 = x_303;
goto block_302;
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = l_Lean_LocalInstance_hasBeq___closed__1;
x_305 = lean_unsigned_to_nat(0u);
x_306 = l_Array_isEqvAux___main___rarg(x_233, x_235, lean_box(0), x_304, x_305);
lean_dec(x_235);
lean_dec(x_233);
if (x_306 == 0)
{
lean_object* x_307; 
x_307 = lean_box(0);
x_240 = x_307;
goto block_302;
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_10);
x_308 = l_Lean_Meta_introNCore___rarg___closed__1;
lean_inc(x_1);
x_309 = l_Lean_Meta_checkNotAssigned(x_1, x_308, x_239, x_9);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec(x_309);
lean_inc(x_1);
x_311 = l_Lean_Meta_getMVarType(x_1, x_239, x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = l_Array_empty___closed__1;
x_315 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_2, x_234, x_314, x_305, x_4, x_312, x_239, x_313);
return x_315;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_239);
lean_dec(x_234);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_316 = lean_ctor_get(x_311, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_311, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_318 = x_311;
} else {
 lean_dec_ref(x_311);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_239);
lean_dec(x_234);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_320 = lean_ctor_get(x_309, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_309, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_322 = x_309;
} else {
 lean_dec_ref(x_309);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
}
block_302:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_240);
x_241 = lean_ctor_get(x_9, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_9, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_9, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_9, 3);
lean_inc(x_244);
x_245 = lean_ctor_get(x_9, 4);
lean_inc(x_245);
x_246 = lean_ctor_get(x_9, 5);
lean_inc(x_246);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 x_247 = x_9;
} else {
 lean_dec_ref(x_9);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_241, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_241, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_241, 2);
lean_inc(x_250);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 x_251 = x_241;
} else {
 lean_dec_ref(x_241);
 x_251 = lean_box(0);
}
x_268 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_251)) {
 x_269 = lean_alloc_ctor(0, 3, 0);
} else {
 x_269 = x_251;
}
lean_ctor_set(x_269, 0, x_248);
lean_ctor_set(x_269, 1, x_249);
lean_ctor_set(x_269, 2, x_268);
if (lean_is_scalar(x_247)) {
 x_270 = lean_alloc_ctor(0, 6, 0);
} else {
 x_270 = x_247;
}
lean_ctor_set(x_270, 0, x_242);
lean_ctor_set(x_270, 1, x_243);
lean_ctor_set(x_270, 2, x_269);
lean_ctor_set(x_270, 3, x_244);
lean_ctor_set(x_270, 4, x_245);
lean_ctor_set(x_270, 5, x_246);
x_271 = l_Lean_Meta_introNCore___rarg___closed__1;
lean_inc(x_1);
x_272 = l_Lean_Meta_checkNotAssigned(x_1, x_271, x_239, x_270);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec(x_272);
lean_inc(x_1);
x_274 = l_Lean_Meta_getMVarType(x_1, x_239, x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = l_Array_empty___closed__1;
x_278 = lean_unsigned_to_nat(0u);
x_279 = l_Lean_Meta_introNCoreAux___main___rarg(x_1, x_3, x_2, x_234, x_277, x_278, x_4, x_275, x_239, x_276);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_10);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_280, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_279, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_283 = x_279;
} else {
 lean_dec_ref(x_279);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_280, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_280, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_280, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_280, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_280, 5);
lean_inc(x_288);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 lean_ctor_release(x_280, 5);
 x_289 = x_280;
} else {
 lean_dec_ref(x_280);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_281, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_281, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 x_292 = x_281;
} else {
 lean_dec_ref(x_281);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 3, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
lean_ctor_set(x_293, 2, x_250);
if (lean_is_scalar(x_289)) {
 x_294 = lean_alloc_ctor(0, 6, 0);
} else {
 x_294 = x_289;
}
lean_ctor_set(x_294, 0, x_284);
lean_ctor_set(x_294, 1, x_285);
lean_ctor_set(x_294, 2, x_293);
lean_ctor_set(x_294, 3, x_286);
lean_ctor_set(x_294, 4, x_287);
lean_ctor_set(x_294, 5, x_288);
if (lean_is_scalar(x_283)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_283;
}
lean_ctor_set(x_295, 0, x_282);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_279, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_279, 1);
lean_inc(x_297);
lean_dec(x_279);
x_252 = x_296;
x_253 = x_297;
goto block_267;
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_239);
lean_dec(x_234);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_298 = lean_ctor_get(x_274, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_274, 1);
lean_inc(x_299);
lean_dec(x_274);
x_252 = x_298;
x_253 = x_299;
goto block_267;
}
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_239);
lean_dec(x_234);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = lean_ctor_get(x_272, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_272, 1);
lean_inc(x_301);
lean_dec(x_272);
x_252 = x_300;
x_253 = x_301;
goto block_267;
}
block_267:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_254 = lean_ctor_get(x_253, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 3);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 4);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 5);
lean_inc(x_259);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 lean_ctor_release(x_253, 4);
 lean_ctor_release(x_253, 5);
 x_260 = x_253;
} else {
 lean_dec_ref(x_253);
 x_260 = lean_box(0);
}
x_261 = lean_ctor_get(x_254, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_254, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 lean_ctor_release(x_254, 2);
 x_263 = x_254;
} else {
 lean_dec_ref(x_254);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 3, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
lean_ctor_set(x_264, 2, x_250);
if (lean_is_scalar(x_260)) {
 x_265 = lean_alloc_ctor(0, 6, 0);
} else {
 x_265 = x_260;
}
lean_ctor_set(x_265, 0, x_255);
lean_ctor_set(x_265, 1, x_256);
lean_ctor_set(x_265, 2, x_264);
lean_ctor_set(x_265, 3, x_257);
lean_ctor_set(x_265, 4, x_258);
lean_ctor_set(x_265, 5, x_259);
if (lean_is_scalar(x_10)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_10;
 lean_ctor_set_tag(x_266, 1);
}
lean_ctor_set(x_266, 0, x_252);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_7);
if (x_324 == 0)
{
return x_7;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_7, 0);
x_326 = lean_ctor_get(x_7, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_7);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
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
x_2 = l_Lean_Name_appendIndexAfter___closed__1;
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
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_expr_instantiate_rev_range(x_4, x_3, x_9, x_2);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar), 4, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_introNCoreAux___main___rarg___lambda__2), 5, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_6, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_12, x_13, x_7, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
x_17 = lean_array_fget(x_5, x_6);
lean_inc(x_7);
x_18 = l_Lean_Meta_getFVarLocalDecl(x_17, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_21);
x_22 = l_Lean_Meta_isClassQuick___main(x_21, x_7, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_6, x_25);
lean_dec(x_6);
x_6 = x_26;
x_8 = x_24;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 2);
x_36 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_33, 2, x_36);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_7, 2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_17);
x_40 = lean_array_push(x_38, x_39);
lean_ctor_set(x_7, 2, x_40);
x_41 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_31, x_7, x_28);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_41, 1);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_42, 2);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_43, 2);
lean_dec(x_49);
lean_ctor_set(x_43, 2, x_35);
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_35);
lean_ctor_set(x_42, 2, x_52);
return x_41;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
x_55 = lean_ctor_get(x_42, 3);
x_56 = lean_ctor_get(x_42, 4);
x_57 = lean_ctor_get(x_42, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_58 = lean_ctor_get(x_43, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 3, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_35);
x_62 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_55);
lean_ctor_set(x_62, 4, x_56);
lean_ctor_set(x_62, 5, x_57);
lean_ctor_set(x_41, 1, x_62);
return x_41;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_63 = lean_ctor_get(x_41, 0);
lean_inc(x_63);
lean_dec(x_41);
x_64 = lean_ctor_get(x_42, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_42, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_42, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_42, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_42, 5);
lean_inc(x_68);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 lean_ctor_release(x_42, 5);
 x_69 = x_42;
} else {
 lean_dec_ref(x_42);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_43, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_43, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 x_72 = x_43;
} else {
 lean_dec_ref(x_43);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 3, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_35);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 6, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_65);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_66);
lean_ctor_set(x_74, 4, x_67);
lean_ctor_set(x_74, 5, x_68);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_63);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_41, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 2);
lean_inc(x_77);
x_78 = !lean_is_exclusive(x_41);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_41, 1);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_76, 2);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_77, 2);
lean_dec(x_83);
lean_ctor_set(x_77, 2, x_35);
return x_41;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_77);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_35);
lean_ctor_set(x_76, 2, x_86);
return x_41;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
x_89 = lean_ctor_get(x_76, 3);
x_90 = lean_ctor_get(x_76, 4);
x_91 = lean_ctor_get(x_76, 5);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_76);
x_92 = lean_ctor_get(x_77, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_77, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 x_94 = x_77;
} else {
 lean_dec_ref(x_77);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 3, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_35);
x_96 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_88);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_89);
lean_ctor_set(x_96, 4, x_90);
lean_ctor_set(x_96, 5, x_91);
lean_ctor_set(x_41, 1, x_96);
return x_41;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_41, 0);
lean_inc(x_97);
lean_dec(x_41);
x_98 = lean_ctor_get(x_76, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_76, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_76, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_76, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_76, 5);
lean_inc(x_102);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 lean_ctor_release(x_76, 4);
 lean_ctor_release(x_76, 5);
 x_103 = x_76;
} else {
 lean_dec_ref(x_76);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_77, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_77, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 x_106 = x_77;
} else {
 lean_dec_ref(x_77);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 3, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
lean_ctor_set(x_107, 2, x_35);
if (lean_is_scalar(x_103)) {
 x_108 = lean_alloc_ctor(0, 6, 0);
} else {
 x_108 = x_103;
}
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_99);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_100);
lean_ctor_set(x_108, 4, x_101);
lean_ctor_set(x_108, 5, x_102);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_97);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
x_112 = lean_ctor_get(x_7, 2);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_7);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_29);
lean_ctor_set(x_113, 1, x_17);
x_114 = lean_array_push(x_112, x_113);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_31, x_115, x_28);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_117, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_117, 5);
lean_inc(x_125);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 x_126 = x_117;
} else {
 lean_dec_ref(x_117);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_118, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 x_129 = x_118;
} else {
 lean_dec_ref(x_118);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 3, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_35);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(0, 6, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_130);
lean_ctor_set(x_131, 3, x_123);
lean_ctor_set(x_131, 4, x_124);
lean_ctor_set(x_131, 5, x_125);
if (lean_is_scalar(x_120)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_120;
}
lean_ctor_set(x_132, 0, x_119);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_133 = lean_ctor_get(x_116, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_116, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_136 = x_116;
} else {
 lean_dec_ref(x_116);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_133, 5);
lean_inc(x_141);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 lean_ctor_release(x_133, 5);
 x_142 = x_133;
} else {
 lean_dec_ref(x_133);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_134, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_134, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 x_145 = x_134;
} else {
 lean_dec_ref(x_134);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 3, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
lean_ctor_set(x_146, 2, x_35);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(0, 6, 0);
} else {
 x_147 = x_142;
}
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set(x_147, 1, x_138);
lean_ctor_set(x_147, 2, x_146);
lean_ctor_set(x_147, 3, x_139);
lean_ctor_set(x_147, 4, x_140);
lean_ctor_set(x_147, 5, x_141);
if (lean_is_scalar(x_136)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_136;
}
lean_ctor_set(x_148, 0, x_135);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_149 = lean_ctor_get(x_33, 0);
x_150 = lean_ctor_get(x_33, 1);
x_151 = lean_ctor_get(x_33, 2);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_33);
x_152 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_153 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_28, 2, x_153);
x_154 = lean_ctor_get(x_7, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_7, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_7, 2);
lean_inc(x_156);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_157 = x_7;
} else {
 lean_dec_ref(x_7);
 x_157 = lean_box(0);
}
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_29);
lean_ctor_set(x_158, 1, x_17);
x_159 = lean_array_push(x_156, x_158);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 3, 0);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_155);
lean_ctor_set(x_160, 2, x_159);
x_161 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_31, x_160, x_28);
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
lean_ctor_set(x_175, 2, x_151);
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
lean_ctor_set(x_191, 2, x_151);
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
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_194 = lean_ctor_get(x_28, 2);
x_195 = lean_ctor_get(x_28, 0);
x_196 = lean_ctor_get(x_28, 1);
x_197 = lean_ctor_get(x_28, 3);
x_198 = lean_ctor_get(x_28, 4);
x_199 = lean_ctor_get(x_28, 5);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_194);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_28);
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
x_207 = lean_ctor_get(x_7, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_7, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_7, 2);
lean_inc(x_209);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_210 = x_7;
} else {
 lean_dec_ref(x_7);
 x_210 = lean_box(0);
}
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_29);
lean_ctor_set(x_211, 1, x_17);
x_212 = lean_array_push(x_209, x_211);
if (lean_is_scalar(x_210)) {
 x_213 = lean_alloc_ctor(0, 3, 0);
} else {
 x_213 = x_210;
}
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_208);
lean_ctor_set(x_213, 2, x_212);
x_214 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_31, x_213, x_206);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_215, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_218 = x_214;
} else {
 lean_dec_ref(x_214);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_215, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_215, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_215, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_215, 4);
lean_inc(x_222);
x_223 = lean_ctor_get(x_215, 5);
lean_inc(x_223);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 lean_ctor_release(x_215, 3);
 lean_ctor_release(x_215, 4);
 lean_ctor_release(x_215, 5);
 x_224 = x_215;
} else {
 lean_dec_ref(x_215);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_216, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_216, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 x_227 = x_216;
} else {
 lean_dec_ref(x_216);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 3, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_202);
if (lean_is_scalar(x_224)) {
 x_229 = lean_alloc_ctor(0, 6, 0);
} else {
 x_229 = x_224;
}
lean_ctor_set(x_229, 0, x_219);
lean_ctor_set(x_229, 1, x_220);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_221);
lean_ctor_set(x_229, 4, x_222);
lean_ctor_set(x_229, 5, x_223);
if (lean_is_scalar(x_218)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_218;
}
lean_ctor_set(x_230, 0, x_217);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_231 = lean_ctor_get(x_214, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_231, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_214, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_234 = x_214;
} else {
 lean_dec_ref(x_214);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_231, 3);
lean_inc(x_237);
x_238 = lean_ctor_get(x_231, 4);
lean_inc(x_238);
x_239 = lean_ctor_get(x_231, 5);
lean_inc(x_239);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 lean_ctor_release(x_231, 2);
 lean_ctor_release(x_231, 3);
 lean_ctor_release(x_231, 4);
 lean_ctor_release(x_231, 5);
 x_240 = x_231;
} else {
 lean_dec_ref(x_231);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_232, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_232, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 lean_ctor_release(x_232, 2);
 x_243 = x_232;
} else {
 lean_dec_ref(x_232);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 3, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
lean_ctor_set(x_244, 2, x_202);
if (lean_is_scalar(x_240)) {
 x_245 = lean_alloc_ctor(0, 6, 0);
} else {
 x_245 = x_240;
}
lean_ctor_set(x_245, 0, x_235);
lean_ctor_set(x_245, 1, x_236);
lean_ctor_set(x_245, 2, x_244);
lean_ctor_set(x_245, 3, x_237);
lean_ctor_set(x_245, 4, x_238);
lean_ctor_set(x_245, 5, x_239);
if (lean_is_scalar(x_234)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_234;
}
lean_ctor_set(x_246, 0, x_233);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
default: 
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_22, 1);
lean_inc(x_247);
lean_dec(x_22);
lean_inc(x_7);
x_248 = l_Lean_Meta_isClassExpensive___main(x_21, x_7, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_17);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_nat_add(x_6, x_251);
lean_dec(x_6);
x_6 = x_252;
x_8 = x_250;
goto _start;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_254 = lean_ctor_get(x_248, 1);
lean_inc(x_254);
lean_dec(x_248);
x_255 = lean_ctor_get(x_249, 0);
lean_inc(x_255);
lean_dec(x_249);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_6, x_256);
lean_dec(x_6);
x_258 = !lean_is_exclusive(x_254);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_254, 2);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_261 = lean_ctor_get(x_259, 2);
x_262 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_259, 2, x_262);
x_263 = !lean_is_exclusive(x_7);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_7, 2);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_255);
lean_ctor_set(x_265, 1, x_17);
x_266 = lean_array_push(x_264, x_265);
lean_ctor_set(x_7, 2, x_266);
x_267 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_257, x_7, x_254);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_268, 2);
lean_inc(x_269);
x_270 = !lean_is_exclusive(x_267);
if (x_270 == 0)
{
lean_object* x_271; uint8_t x_272; 
x_271 = lean_ctor_get(x_267, 1);
lean_dec(x_271);
x_272 = !lean_is_exclusive(x_268);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_268, 2);
lean_dec(x_273);
x_274 = !lean_is_exclusive(x_269);
if (x_274 == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_269, 2);
lean_dec(x_275);
lean_ctor_set(x_269, 2, x_261);
return x_267;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_269, 0);
x_277 = lean_ctor_get(x_269, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_269);
x_278 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set(x_278, 2, x_261);
lean_ctor_set(x_268, 2, x_278);
return x_267;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_279 = lean_ctor_get(x_268, 0);
x_280 = lean_ctor_get(x_268, 1);
x_281 = lean_ctor_get(x_268, 3);
x_282 = lean_ctor_get(x_268, 4);
x_283 = lean_ctor_get(x_268, 5);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_268);
x_284 = lean_ctor_get(x_269, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_269, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 x_286 = x_269;
} else {
 lean_dec_ref(x_269);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 3, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
lean_ctor_set(x_287, 2, x_261);
x_288 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_288, 0, x_279);
lean_ctor_set(x_288, 1, x_280);
lean_ctor_set(x_288, 2, x_287);
lean_ctor_set(x_288, 3, x_281);
lean_ctor_set(x_288, 4, x_282);
lean_ctor_set(x_288, 5, x_283);
lean_ctor_set(x_267, 1, x_288);
return x_267;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_289 = lean_ctor_get(x_267, 0);
lean_inc(x_289);
lean_dec(x_267);
x_290 = lean_ctor_get(x_268, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_268, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_268, 3);
lean_inc(x_292);
x_293 = lean_ctor_get(x_268, 4);
lean_inc(x_293);
x_294 = lean_ctor_get(x_268, 5);
lean_inc(x_294);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 lean_ctor_release(x_268, 4);
 lean_ctor_release(x_268, 5);
 x_295 = x_268;
} else {
 lean_dec_ref(x_268);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_269, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_269, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 x_298 = x_269;
} else {
 lean_dec_ref(x_269);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(0, 3, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
lean_ctor_set(x_299, 2, x_261);
if (lean_is_scalar(x_295)) {
 x_300 = lean_alloc_ctor(0, 6, 0);
} else {
 x_300 = x_295;
}
lean_ctor_set(x_300, 0, x_290);
lean_ctor_set(x_300, 1, x_291);
lean_ctor_set(x_300, 2, x_299);
lean_ctor_set(x_300, 3, x_292);
lean_ctor_set(x_300, 4, x_293);
lean_ctor_set(x_300, 5, x_294);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_289);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_302 = lean_ctor_get(x_267, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_302, 2);
lean_inc(x_303);
x_304 = !lean_is_exclusive(x_267);
if (x_304 == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = lean_ctor_get(x_267, 1);
lean_dec(x_305);
x_306 = !lean_is_exclusive(x_302);
if (x_306 == 0)
{
lean_object* x_307; uint8_t x_308; 
x_307 = lean_ctor_get(x_302, 2);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_303);
if (x_308 == 0)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_303, 2);
lean_dec(x_309);
lean_ctor_set(x_303, 2, x_261);
return x_267;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_303, 0);
x_311 = lean_ctor_get(x_303, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_303);
x_312 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
lean_ctor_set(x_312, 2, x_261);
lean_ctor_set(x_302, 2, x_312);
return x_267;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_313 = lean_ctor_get(x_302, 0);
x_314 = lean_ctor_get(x_302, 1);
x_315 = lean_ctor_get(x_302, 3);
x_316 = lean_ctor_get(x_302, 4);
x_317 = lean_ctor_get(x_302, 5);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_302);
x_318 = lean_ctor_get(x_303, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_303, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 lean_ctor_release(x_303, 2);
 x_320 = x_303;
} else {
 lean_dec_ref(x_303);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 3, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
lean_ctor_set(x_321, 2, x_261);
x_322 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_322, 0, x_313);
lean_ctor_set(x_322, 1, x_314);
lean_ctor_set(x_322, 2, x_321);
lean_ctor_set(x_322, 3, x_315);
lean_ctor_set(x_322, 4, x_316);
lean_ctor_set(x_322, 5, x_317);
lean_ctor_set(x_267, 1, x_322);
return x_267;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_323 = lean_ctor_get(x_267, 0);
lean_inc(x_323);
lean_dec(x_267);
x_324 = lean_ctor_get(x_302, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_302, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_302, 3);
lean_inc(x_326);
x_327 = lean_ctor_get(x_302, 4);
lean_inc(x_327);
x_328 = lean_ctor_get(x_302, 5);
lean_inc(x_328);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 lean_ctor_release(x_302, 2);
 lean_ctor_release(x_302, 3);
 lean_ctor_release(x_302, 4);
 lean_ctor_release(x_302, 5);
 x_329 = x_302;
} else {
 lean_dec_ref(x_302);
 x_329 = lean_box(0);
}
x_330 = lean_ctor_get(x_303, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_303, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 lean_ctor_release(x_303, 2);
 x_332 = x_303;
} else {
 lean_dec_ref(x_303);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 3, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_331);
lean_ctor_set(x_333, 2, x_261);
if (lean_is_scalar(x_329)) {
 x_334 = lean_alloc_ctor(0, 6, 0);
} else {
 x_334 = x_329;
}
lean_ctor_set(x_334, 0, x_324);
lean_ctor_set(x_334, 1, x_325);
lean_ctor_set(x_334, 2, x_333);
lean_ctor_set(x_334, 3, x_326);
lean_ctor_set(x_334, 4, x_327);
lean_ctor_set(x_334, 5, x_328);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_323);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_336 = lean_ctor_get(x_7, 0);
x_337 = lean_ctor_get(x_7, 1);
x_338 = lean_ctor_get(x_7, 2);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_7);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_255);
lean_ctor_set(x_339, 1, x_17);
x_340 = lean_array_push(x_338, x_339);
x_341 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_341, 0, x_336);
lean_ctor_set(x_341, 1, x_337);
lean_ctor_set(x_341, 2, x_340);
x_342 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_257, x_341, x_254);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_343, 2);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_346 = x_342;
} else {
 lean_dec_ref(x_342);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_343, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_343, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_343, 3);
lean_inc(x_349);
x_350 = lean_ctor_get(x_343, 4);
lean_inc(x_350);
x_351 = lean_ctor_get(x_343, 5);
lean_inc(x_351);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 lean_ctor_release(x_343, 4);
 lean_ctor_release(x_343, 5);
 x_352 = x_343;
} else {
 lean_dec_ref(x_343);
 x_352 = lean_box(0);
}
x_353 = lean_ctor_get(x_344, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_344, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 lean_ctor_release(x_344, 2);
 x_355 = x_344;
} else {
 lean_dec_ref(x_344);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(0, 3, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
lean_ctor_set(x_356, 2, x_261);
if (lean_is_scalar(x_352)) {
 x_357 = lean_alloc_ctor(0, 6, 0);
} else {
 x_357 = x_352;
}
lean_ctor_set(x_357, 0, x_347);
lean_ctor_set(x_357, 1, x_348);
lean_ctor_set(x_357, 2, x_356);
lean_ctor_set(x_357, 3, x_349);
lean_ctor_set(x_357, 4, x_350);
lean_ctor_set(x_357, 5, x_351);
if (lean_is_scalar(x_346)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_346;
}
lean_ctor_set(x_358, 0, x_345);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_359 = lean_ctor_get(x_342, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_359, 2);
lean_inc(x_360);
x_361 = lean_ctor_get(x_342, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_362 = x_342;
} else {
 lean_dec_ref(x_342);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_359, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_359, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_359, 3);
lean_inc(x_365);
x_366 = lean_ctor_get(x_359, 4);
lean_inc(x_366);
x_367 = lean_ctor_get(x_359, 5);
lean_inc(x_367);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 lean_ctor_release(x_359, 2);
 lean_ctor_release(x_359, 3);
 lean_ctor_release(x_359, 4);
 lean_ctor_release(x_359, 5);
 x_368 = x_359;
} else {
 lean_dec_ref(x_359);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_360, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_360, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 lean_ctor_release(x_360, 2);
 x_371 = x_360;
} else {
 lean_dec_ref(x_360);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(0, 3, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
lean_ctor_set(x_372, 2, x_261);
if (lean_is_scalar(x_368)) {
 x_373 = lean_alloc_ctor(0, 6, 0);
} else {
 x_373 = x_368;
}
lean_ctor_set(x_373, 0, x_363);
lean_ctor_set(x_373, 1, x_364);
lean_ctor_set(x_373, 2, x_372);
lean_ctor_set(x_373, 3, x_365);
lean_ctor_set(x_373, 4, x_366);
lean_ctor_set(x_373, 5, x_367);
if (lean_is_scalar(x_362)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_362;
}
lean_ctor_set(x_374, 0, x_361);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_375 = lean_ctor_get(x_259, 0);
x_376 = lean_ctor_get(x_259, 1);
x_377 = lean_ctor_get(x_259, 2);
lean_inc(x_377);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_259);
x_378 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_379 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_379, 0, x_375);
lean_ctor_set(x_379, 1, x_376);
lean_ctor_set(x_379, 2, x_378);
lean_ctor_set(x_254, 2, x_379);
x_380 = lean_ctor_get(x_7, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_7, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_7, 2);
lean_inc(x_382);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_383 = x_7;
} else {
 lean_dec_ref(x_7);
 x_383 = lean_box(0);
}
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_255);
lean_ctor_set(x_384, 1, x_17);
x_385 = lean_array_push(x_382, x_384);
if (lean_is_scalar(x_383)) {
 x_386 = lean_alloc_ctor(0, 3, 0);
} else {
 x_386 = x_383;
}
lean_ctor_set(x_386, 0, x_380);
lean_ctor_set(x_386, 1, x_381);
lean_ctor_set(x_386, 2, x_385);
x_387 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_257, x_386, x_254);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_388, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_387, 0);
lean_inc(x_390);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_391 = x_387;
} else {
 lean_dec_ref(x_387);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_388, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_388, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_388, 3);
lean_inc(x_394);
x_395 = lean_ctor_get(x_388, 4);
lean_inc(x_395);
x_396 = lean_ctor_get(x_388, 5);
lean_inc(x_396);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 lean_ctor_release(x_388, 2);
 lean_ctor_release(x_388, 3);
 lean_ctor_release(x_388, 4);
 lean_ctor_release(x_388, 5);
 x_397 = x_388;
} else {
 lean_dec_ref(x_388);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_389, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 x_400 = x_389;
} else {
 lean_dec_ref(x_389);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(0, 3, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
lean_ctor_set(x_401, 2, x_377);
if (lean_is_scalar(x_397)) {
 x_402 = lean_alloc_ctor(0, 6, 0);
} else {
 x_402 = x_397;
}
lean_ctor_set(x_402, 0, x_392);
lean_ctor_set(x_402, 1, x_393);
lean_ctor_set(x_402, 2, x_401);
lean_ctor_set(x_402, 3, x_394);
lean_ctor_set(x_402, 4, x_395);
lean_ctor_set(x_402, 5, x_396);
if (lean_is_scalar(x_391)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_391;
}
lean_ctor_set(x_403, 0, x_390);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_404 = lean_ctor_get(x_387, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_404, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_387, 0);
lean_inc(x_406);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_407 = x_387;
} else {
 lean_dec_ref(x_387);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_404, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_404, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_404, 3);
lean_inc(x_410);
x_411 = lean_ctor_get(x_404, 4);
lean_inc(x_411);
x_412 = lean_ctor_get(x_404, 5);
lean_inc(x_412);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 lean_ctor_release(x_404, 4);
 lean_ctor_release(x_404, 5);
 x_413 = x_404;
} else {
 lean_dec_ref(x_404);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_405, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_405, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 x_416 = x_405;
} else {
 lean_dec_ref(x_405);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 3, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
lean_ctor_set(x_417, 2, x_377);
if (lean_is_scalar(x_413)) {
 x_418 = lean_alloc_ctor(0, 6, 0);
} else {
 x_418 = x_413;
}
lean_ctor_set(x_418, 0, x_408);
lean_ctor_set(x_418, 1, x_409);
lean_ctor_set(x_418, 2, x_417);
lean_ctor_set(x_418, 3, x_410);
lean_ctor_set(x_418, 4, x_411);
lean_ctor_set(x_418, 5, x_412);
if (lean_is_scalar(x_407)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_407;
}
lean_ctor_set(x_419, 0, x_406);
lean_ctor_set(x_419, 1, x_418);
return x_419;
}
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_420 = lean_ctor_get(x_254, 2);
x_421 = lean_ctor_get(x_254, 0);
x_422 = lean_ctor_get(x_254, 1);
x_423 = lean_ctor_get(x_254, 3);
x_424 = lean_ctor_get(x_254, 4);
x_425 = lean_ctor_get(x_254, 5);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_420);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_254);
x_426 = lean_ctor_get(x_420, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_420, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_420, 2);
lean_inc(x_428);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 x_429 = x_420;
} else {
 lean_dec_ref(x_420);
 x_429 = lean_box(0);
}
x_430 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_429)) {
 x_431 = lean_alloc_ctor(0, 3, 0);
} else {
 x_431 = x_429;
}
lean_ctor_set(x_431, 0, x_426);
lean_ctor_set(x_431, 1, x_427);
lean_ctor_set(x_431, 2, x_430);
x_432 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_432, 0, x_421);
lean_ctor_set(x_432, 1, x_422);
lean_ctor_set(x_432, 2, x_431);
lean_ctor_set(x_432, 3, x_423);
lean_ctor_set(x_432, 4, x_424);
lean_ctor_set(x_432, 5, x_425);
x_433 = lean_ctor_get(x_7, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_7, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_7, 2);
lean_inc(x_435);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_436 = x_7;
} else {
 lean_dec_ref(x_7);
 x_436 = lean_box(0);
}
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_255);
lean_ctor_set(x_437, 1, x_17);
x_438 = lean_array_push(x_435, x_437);
if (lean_is_scalar(x_436)) {
 x_439 = lean_alloc_ctor(0, 3, 0);
} else {
 x_439 = x_436;
}
lean_ctor_set(x_439, 0, x_433);
lean_ctor_set(x_439, 1, x_434);
lean_ctor_set(x_439, 2, x_438);
x_440 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_257, x_439, x_432);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
x_442 = lean_ctor_get(x_441, 2);
lean_inc(x_442);
x_443 = lean_ctor_get(x_440, 0);
lean_inc(x_443);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_444 = x_440;
} else {
 lean_dec_ref(x_440);
 x_444 = lean_box(0);
}
x_445 = lean_ctor_get(x_441, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_441, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_441, 3);
lean_inc(x_447);
x_448 = lean_ctor_get(x_441, 4);
lean_inc(x_448);
x_449 = lean_ctor_get(x_441, 5);
lean_inc(x_449);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 lean_ctor_release(x_441, 3);
 lean_ctor_release(x_441, 4);
 lean_ctor_release(x_441, 5);
 x_450 = x_441;
} else {
 lean_dec_ref(x_441);
 x_450 = lean_box(0);
}
x_451 = lean_ctor_get(x_442, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_442, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 lean_ctor_release(x_442, 2);
 x_453 = x_442;
} else {
 lean_dec_ref(x_442);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(0, 3, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
lean_ctor_set(x_454, 2, x_428);
if (lean_is_scalar(x_450)) {
 x_455 = lean_alloc_ctor(0, 6, 0);
} else {
 x_455 = x_450;
}
lean_ctor_set(x_455, 0, x_445);
lean_ctor_set(x_455, 1, x_446);
lean_ctor_set(x_455, 2, x_454);
lean_ctor_set(x_455, 3, x_447);
lean_ctor_set(x_455, 4, x_448);
lean_ctor_set(x_455, 5, x_449);
if (lean_is_scalar(x_444)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_444;
}
lean_ctor_set(x_456, 0, x_443);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_457 = lean_ctor_get(x_440, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_457, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_440, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_460 = x_440;
} else {
 lean_dec_ref(x_440);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_457, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_457, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_457, 3);
lean_inc(x_463);
x_464 = lean_ctor_get(x_457, 4);
lean_inc(x_464);
x_465 = lean_ctor_get(x_457, 5);
lean_inc(x_465);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 lean_ctor_release(x_457, 2);
 lean_ctor_release(x_457, 3);
 lean_ctor_release(x_457, 4);
 lean_ctor_release(x_457, 5);
 x_466 = x_457;
} else {
 lean_dec_ref(x_457);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_458, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_458, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 lean_ctor_release(x_458, 2);
 x_469 = x_458;
} else {
 lean_dec_ref(x_458);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(0, 3, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_468);
lean_ctor_set(x_470, 2, x_428);
if (lean_is_scalar(x_466)) {
 x_471 = lean_alloc_ctor(0, 6, 0);
} else {
 x_471 = x_466;
}
lean_ctor_set(x_471, 0, x_461);
lean_ctor_set(x_471, 1, x_462);
lean_ctor_set(x_471, 2, x_470);
lean_ctor_set(x_471, 3, x_463);
lean_ctor_set(x_471, 4, x_464);
lean_ctor_set(x_471, 5, x_465);
if (lean_is_scalar(x_460)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_460;
}
lean_ctor_set(x_472, 0, x_459);
lean_ctor_set(x_472, 1, x_471);
return x_472;
}
}
}
}
else
{
uint8_t x_473; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_473 = !lean_is_exclusive(x_248);
if (x_473 == 0)
{
return x_248;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_248, 0);
x_475 = lean_ctor_get(x_248, 1);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_248);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_475);
return x_476;
}
}
}
}
}
else
{
uint8_t x_477; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_481; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_481 = !lean_is_exclusive(x_18);
if (x_481 == 0)
{
return x_18;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_18, 0);
x_483 = lean_ctor_get(x_18, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_18);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
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
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Meta_introNCoreAux___main___rarg___lambda__1___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
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
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_11, 0);
x_113 = lean_ctor_get(x_11, 1);
x_114 = lean_ctor_get(x_11, 2);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_11);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_31);
lean_ctor_set(x_115, 1, x_19);
x_116 = lean_array_push(x_114, x_115);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_113);
lean_ctor_set(x_117, 2, x_116);
x_118 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_117, x_30);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 4);
lean_inc(x_126);
x_127 = lean_ctor_get(x_119, 5);
lean_inc(x_127);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 x_128 = x_119;
} else {
 lean_dec_ref(x_119);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_120, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_120, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 x_131 = x_120;
} else {
 lean_dec_ref(x_120);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
lean_ctor_set(x_132, 2, x_37);
if (lean_is_scalar(x_128)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_128;
}
lean_ctor_set(x_133, 0, x_123);
lean_ctor_set(x_133, 1, x_124);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_125);
lean_ctor_set(x_133, 4, x_126);
lean_ctor_set(x_133, 5, x_127);
if (lean_is_scalar(x_122)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_122;
}
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_135 = lean_ctor_get(x_118, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_118, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_138 = x_118;
} else {
 lean_dec_ref(x_118);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 5);
lean_inc(x_143);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 x_144 = x_135;
} else {
 lean_dec_ref(x_135);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_136, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 x_147 = x_136;
} else {
 lean_dec_ref(x_136);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 3, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
lean_ctor_set(x_148, 2, x_37);
if (lean_is_scalar(x_144)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_144;
}
lean_ctor_set(x_149, 0, x_139);
lean_ctor_set(x_149, 1, x_140);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_141);
lean_ctor_set(x_149, 4, x_142);
lean_ctor_set(x_149, 5, x_143);
if (lean_is_scalar(x_138)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_138;
}
lean_ctor_set(x_150, 0, x_137);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_151 = lean_ctor_get(x_35, 0);
x_152 = lean_ctor_get(x_35, 1);
x_153 = lean_ctor_get(x_35, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_35);
x_154 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_155 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_152);
lean_ctor_set(x_155, 2, x_154);
lean_ctor_set(x_30, 2, x_155);
x_156 = lean_ctor_get(x_11, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_11, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_11, 2);
lean_inc(x_158);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_159 = x_11;
} else {
 lean_dec_ref(x_11);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_31);
lean_ctor_set(x_160, 1, x_19);
x_161 = lean_array_push(x_158, x_160);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 3, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_157);
lean_ctor_set(x_162, 2, x_161);
x_163 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_162, x_30);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_167 = x_163;
} else {
 lean_dec_ref(x_163);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_164, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_164, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_164, 5);
lean_inc(x_172);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 lean_ctor_release(x_164, 4);
 lean_ctor_release(x_164, 5);
 x_173 = x_164;
} else {
 lean_dec_ref(x_164);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_165, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_165, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 x_176 = x_165;
} else {
 lean_dec_ref(x_165);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 3, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_153);
if (lean_is_scalar(x_173)) {
 x_178 = lean_alloc_ctor(0, 6, 0);
} else {
 x_178 = x_173;
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_178, 3, x_170);
lean_ctor_set(x_178, 4, x_171);
lean_ctor_set(x_178, 5, x_172);
if (lean_is_scalar(x_167)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_167;
}
lean_ctor_set(x_179, 0, x_166);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_180 = lean_ctor_get(x_163, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 2);
lean_inc(x_181);
x_182 = lean_ctor_get(x_163, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_183 = x_163;
} else {
 lean_dec_ref(x_163);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 5);
lean_inc(x_188);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 lean_ctor_release(x_180, 5);
 x_189 = x_180;
} else {
 lean_dec_ref(x_180);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_181, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_181, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 x_192 = x_181;
} else {
 lean_dec_ref(x_181);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 3, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
lean_ctor_set(x_193, 2, x_153);
if (lean_is_scalar(x_189)) {
 x_194 = lean_alloc_ctor(0, 6, 0);
} else {
 x_194 = x_189;
}
lean_ctor_set(x_194, 0, x_184);
lean_ctor_set(x_194, 1, x_185);
lean_ctor_set(x_194, 2, x_193);
lean_ctor_set(x_194, 3, x_186);
lean_ctor_set(x_194, 4, x_187);
lean_ctor_set(x_194, 5, x_188);
if (lean_is_scalar(x_183)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_183;
}
lean_ctor_set(x_195, 0, x_182);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_196 = lean_ctor_get(x_30, 2);
x_197 = lean_ctor_get(x_30, 0);
x_198 = lean_ctor_get(x_30, 1);
x_199 = lean_ctor_get(x_30, 3);
x_200 = lean_ctor_get(x_30, 4);
x_201 = lean_ctor_get(x_30, 5);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_196);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_30);
x_202 = lean_ctor_get(x_196, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_196, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_196, 2);
lean_inc(x_204);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 x_205 = x_196;
} else {
 lean_dec_ref(x_196);
 x_205 = lean_box(0);
}
x_206 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 3, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_206);
x_208 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_208, 0, x_197);
lean_ctor_set(x_208, 1, x_198);
lean_ctor_set(x_208, 2, x_207);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set(x_208, 4, x_200);
lean_ctor_set(x_208, 5, x_201);
x_209 = lean_ctor_get(x_11, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_11, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_11, 2);
lean_inc(x_211);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_212 = x_11;
} else {
 lean_dec_ref(x_11);
 x_212 = lean_box(0);
}
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_31);
lean_ctor_set(x_213, 1, x_19);
x_214 = lean_array_push(x_211, x_213);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_209);
lean_ctor_set(x_215, 1, x_210);
lean_ctor_set(x_215, 2, x_214);
x_216 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_215, x_208);
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
lean_ctor_set(x_230, 2, x_204);
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
lean_ctor_set(x_246, 2, x_204);
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
x_249 = lean_ctor_get(x_24, 1);
lean_inc(x_249);
lean_dec(x_24);
lean_inc(x_11);
x_250 = l_Lean_Meta_isClassExpensive___main(x_23, x_11, x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_19);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_nat_add(x_10, x_253);
lean_dec(x_10);
x_10 = x_254;
x_12 = x_252;
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
x_259 = lean_nat_add(x_10, x_258);
lean_dec(x_10);
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
x_265 = !lean_is_exclusive(x_11);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_11, 2);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_19);
x_268 = lean_array_push(x_266, x_267);
lean_ctor_set(x_11, 2, x_268);
x_269 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259, x_11, x_256);
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
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_338 = lean_ctor_get(x_11, 0);
x_339 = lean_ctor_get(x_11, 1);
x_340 = lean_ctor_get(x_11, 2);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_11);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_257);
lean_ctor_set(x_341, 1, x_19);
x_342 = lean_array_push(x_340, x_341);
x_343 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_339);
lean_ctor_set(x_343, 2, x_342);
x_344 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259, x_343, x_256);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_348 = x_344;
} else {
 lean_dec_ref(x_344);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_345, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_345, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_345, 3);
lean_inc(x_351);
x_352 = lean_ctor_get(x_345, 4);
lean_inc(x_352);
x_353 = lean_ctor_get(x_345, 5);
lean_inc(x_353);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_354 = x_345;
} else {
 lean_dec_ref(x_345);
 x_354 = lean_box(0);
}
x_355 = lean_ctor_get(x_346, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_346, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 lean_ctor_release(x_346, 2);
 x_357 = x_346;
} else {
 lean_dec_ref(x_346);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(0, 3, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
lean_ctor_set(x_358, 2, x_263);
if (lean_is_scalar(x_354)) {
 x_359 = lean_alloc_ctor(0, 6, 0);
} else {
 x_359 = x_354;
}
lean_ctor_set(x_359, 0, x_349);
lean_ctor_set(x_359, 1, x_350);
lean_ctor_set(x_359, 2, x_358);
lean_ctor_set(x_359, 3, x_351);
lean_ctor_set(x_359, 4, x_352);
lean_ctor_set(x_359, 5, x_353);
if (lean_is_scalar(x_348)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_348;
}
lean_ctor_set(x_360, 0, x_347);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_361 = lean_ctor_get(x_344, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_361, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_344, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_364 = x_344;
} else {
 lean_dec_ref(x_344);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_361, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_361, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_361, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_361, 4);
lean_inc(x_368);
x_369 = lean_ctor_get(x_361, 5);
lean_inc(x_369);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 lean_ctor_release(x_361, 2);
 lean_ctor_release(x_361, 3);
 lean_ctor_release(x_361, 4);
 lean_ctor_release(x_361, 5);
 x_370 = x_361;
} else {
 lean_dec_ref(x_361);
 x_370 = lean_box(0);
}
x_371 = lean_ctor_get(x_362, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_362, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 x_373 = x_362;
} else {
 lean_dec_ref(x_362);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 3, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
lean_ctor_set(x_374, 2, x_263);
if (lean_is_scalar(x_370)) {
 x_375 = lean_alloc_ctor(0, 6, 0);
} else {
 x_375 = x_370;
}
lean_ctor_set(x_375, 0, x_365);
lean_ctor_set(x_375, 1, x_366);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_367);
lean_ctor_set(x_375, 4, x_368);
lean_ctor_set(x_375, 5, x_369);
if (lean_is_scalar(x_364)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_364;
}
lean_ctor_set(x_376, 0, x_363);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_377 = lean_ctor_get(x_261, 0);
x_378 = lean_ctor_get(x_261, 1);
x_379 = lean_ctor_get(x_261, 2);
lean_inc(x_379);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_261);
x_380 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_381 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_378);
lean_ctor_set(x_381, 2, x_380);
lean_ctor_set(x_256, 2, x_381);
x_382 = lean_ctor_get(x_11, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_11, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_11, 2);
lean_inc(x_384);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_385 = x_11;
} else {
 lean_dec_ref(x_11);
 x_385 = lean_box(0);
}
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_257);
lean_ctor_set(x_386, 1, x_19);
x_387 = lean_array_push(x_384, x_386);
if (lean_is_scalar(x_385)) {
 x_388 = lean_alloc_ctor(0, 3, 0);
} else {
 x_388 = x_385;
}
lean_ctor_set(x_388, 0, x_382);
lean_ctor_set(x_388, 1, x_383);
lean_ctor_set(x_388, 2, x_387);
x_389 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259, x_388, x_256);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_390, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_389, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_393 = x_389;
} else {
 lean_dec_ref(x_389);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_390, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_390, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_390, 3);
lean_inc(x_396);
x_397 = lean_ctor_get(x_390, 4);
lean_inc(x_397);
x_398 = lean_ctor_get(x_390, 5);
lean_inc(x_398);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 lean_ctor_release(x_390, 2);
 lean_ctor_release(x_390, 3);
 lean_ctor_release(x_390, 4);
 lean_ctor_release(x_390, 5);
 x_399 = x_390;
} else {
 lean_dec_ref(x_390);
 x_399 = lean_box(0);
}
x_400 = lean_ctor_get(x_391, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_391, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 lean_ctor_release(x_391, 2);
 x_402 = x_391;
} else {
 lean_dec_ref(x_391);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(0, 3, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
lean_ctor_set(x_403, 2, x_379);
if (lean_is_scalar(x_399)) {
 x_404 = lean_alloc_ctor(0, 6, 0);
} else {
 x_404 = x_399;
}
lean_ctor_set(x_404, 0, x_394);
lean_ctor_set(x_404, 1, x_395);
lean_ctor_set(x_404, 2, x_403);
lean_ctor_set(x_404, 3, x_396);
lean_ctor_set(x_404, 4, x_397);
lean_ctor_set(x_404, 5, x_398);
if (lean_is_scalar(x_393)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_393;
}
lean_ctor_set(x_405, 0, x_392);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_406 = lean_ctor_get(x_389, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_406, 2);
lean_inc(x_407);
x_408 = lean_ctor_get(x_389, 0);
lean_inc(x_408);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_409 = x_389;
} else {
 lean_dec_ref(x_389);
 x_409 = lean_box(0);
}
x_410 = lean_ctor_get(x_406, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_406, 1);
lean_inc(x_411);
x_412 = lean_ctor_get(x_406, 3);
lean_inc(x_412);
x_413 = lean_ctor_get(x_406, 4);
lean_inc(x_413);
x_414 = lean_ctor_get(x_406, 5);
lean_inc(x_414);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 lean_ctor_release(x_406, 2);
 lean_ctor_release(x_406, 3);
 lean_ctor_release(x_406, 4);
 lean_ctor_release(x_406, 5);
 x_415 = x_406;
} else {
 lean_dec_ref(x_406);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_407, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_407, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 lean_ctor_release(x_407, 2);
 x_418 = x_407;
} else {
 lean_dec_ref(x_407);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 3, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
lean_ctor_set(x_419, 2, x_379);
if (lean_is_scalar(x_415)) {
 x_420 = lean_alloc_ctor(0, 6, 0);
} else {
 x_420 = x_415;
}
lean_ctor_set(x_420, 0, x_410);
lean_ctor_set(x_420, 1, x_411);
lean_ctor_set(x_420, 2, x_419);
lean_ctor_set(x_420, 3, x_412);
lean_ctor_set(x_420, 4, x_413);
lean_ctor_set(x_420, 5, x_414);
if (lean_is_scalar(x_409)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_409;
}
lean_ctor_set(x_421, 0, x_408);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_422 = lean_ctor_get(x_256, 2);
x_423 = lean_ctor_get(x_256, 0);
x_424 = lean_ctor_get(x_256, 1);
x_425 = lean_ctor_get(x_256, 3);
x_426 = lean_ctor_get(x_256, 4);
x_427 = lean_ctor_get(x_256, 5);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_422);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_256);
x_428 = lean_ctor_get(x_422, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_422, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_422, 2);
lean_inc(x_430);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 x_431 = x_422;
} else {
 lean_dec_ref(x_422);
 x_431 = lean_box(0);
}
x_432 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_431)) {
 x_433 = lean_alloc_ctor(0, 3, 0);
} else {
 x_433 = x_431;
}
lean_ctor_set(x_433, 0, x_428);
lean_ctor_set(x_433, 1, x_429);
lean_ctor_set(x_433, 2, x_432);
x_434 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_434, 0, x_423);
lean_ctor_set(x_434, 1, x_424);
lean_ctor_set(x_434, 2, x_433);
lean_ctor_set(x_434, 3, x_425);
lean_ctor_set(x_434, 4, x_426);
lean_ctor_set(x_434, 5, x_427);
x_435 = lean_ctor_get(x_11, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_11, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_11, 2);
lean_inc(x_437);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_438 = x_11;
} else {
 lean_dec_ref(x_11);
 x_438 = lean_box(0);
}
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_257);
lean_ctor_set(x_439, 1, x_19);
x_440 = lean_array_push(x_437, x_439);
if (lean_is_scalar(x_438)) {
 x_441 = lean_alloc_ctor(0, 3, 0);
} else {
 x_441 = x_438;
}
lean_ctor_set(x_441, 0, x_435);
lean_ctor_set(x_441, 1, x_436);
lean_ctor_set(x_441, 2, x_440);
x_442 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259, x_441, x_434);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_443, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_442, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_446 = x_442;
} else {
 lean_dec_ref(x_442);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_443, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_443, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_443, 3);
lean_inc(x_449);
x_450 = lean_ctor_get(x_443, 4);
lean_inc(x_450);
x_451 = lean_ctor_get(x_443, 5);
lean_inc(x_451);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 lean_ctor_release(x_443, 2);
 lean_ctor_release(x_443, 3);
 lean_ctor_release(x_443, 4);
 lean_ctor_release(x_443, 5);
 x_452 = x_443;
} else {
 lean_dec_ref(x_443);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_444, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_444, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 x_455 = x_444;
} else {
 lean_dec_ref(x_444);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 3, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_453);
lean_ctor_set(x_456, 1, x_454);
lean_ctor_set(x_456, 2, x_430);
if (lean_is_scalar(x_452)) {
 x_457 = lean_alloc_ctor(0, 6, 0);
} else {
 x_457 = x_452;
}
lean_ctor_set(x_457, 0, x_447);
lean_ctor_set(x_457, 1, x_448);
lean_ctor_set(x_457, 2, x_456);
lean_ctor_set(x_457, 3, x_449);
lean_ctor_set(x_457, 4, x_450);
lean_ctor_set(x_457, 5, x_451);
if (lean_is_scalar(x_446)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_446;
}
lean_ctor_set(x_458, 0, x_445);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_459 = lean_ctor_get(x_442, 1);
lean_inc(x_459);
x_460 = lean_ctor_get(x_459, 2);
lean_inc(x_460);
x_461 = lean_ctor_get(x_442, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_462 = x_442;
} else {
 lean_dec_ref(x_442);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_459, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_459, 1);
lean_inc(x_464);
x_465 = lean_ctor_get(x_459, 3);
lean_inc(x_465);
x_466 = lean_ctor_get(x_459, 4);
lean_inc(x_466);
x_467 = lean_ctor_get(x_459, 5);
lean_inc(x_467);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 lean_ctor_release(x_459, 4);
 lean_ctor_release(x_459, 5);
 x_468 = x_459;
} else {
 lean_dec_ref(x_459);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_460, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_460, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 x_471 = x_460;
} else {
 lean_dec_ref(x_460);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(0, 3, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
lean_ctor_set(x_472, 2, x_430);
if (lean_is_scalar(x_468)) {
 x_473 = lean_alloc_ctor(0, 6, 0);
} else {
 x_473 = x_468;
}
lean_ctor_set(x_473, 0, x_463);
lean_ctor_set(x_473, 1, x_464);
lean_ctor_set(x_473, 2, x_472);
lean_ctor_set(x_473, 3, x_465);
lean_ctor_set(x_473, 4, x_466);
lean_ctor_set(x_473, 5, x_467);
if (lean_is_scalar(x_462)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_462;
}
lean_ctor_set(x_474, 0, x_461);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
}
else
{
uint8_t x_475; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_475 = !lean_is_exclusive(x_250);
if (x_475 == 0)
{
return x_250;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_250, 0);
x_477 = lean_ctor_get(x_250, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_250);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
}
}
else
{
uint8_t x_479; 
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
x_479 = !lean_is_exclusive(x_24);
if (x_479 == 0)
{
return x_24;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_24, 0);
x_481 = lean_ctor_get(x_24, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_24);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
else
{
uint8_t x_483; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_483 = !lean_is_exclusive(x_20);
if (x_483 == 0)
{
return x_20;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_20, 0);
x_485 = lean_ctor_get(x_20, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_20);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 2);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_28 = lean_array_get_size(x_4);
x_29 = lean_expr_instantiate_rev_range(x_25, x_5, x_28, x_4);
lean_dec(x_28);
lean_dec(x_25);
x_30 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_3);
x_33 = l_Lean_Meta_mkAuxName(x_3, x_24, x_6);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = (uint8_t)((x_27 << 24) >> 61);
lean_inc(x_31);
x_37 = lean_local_ctx_mk_local_decl(x_3, x_31, x_34, x_29, x_36);
x_38 = l_Lean_mkFVar(x_31);
x_39 = lean_array_push(x_4, x_38);
x_2 = x_13;
x_3 = x_37;
x_4 = x_39;
x_6 = x_35;
x_7 = x_26;
x_9 = x_32;
goto _start;
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_7, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 3);
lean_inc(x_44);
lean_dec(x_7);
x_45 = lean_array_get_size(x_4);
x_46 = lean_expr_instantiate_rev_range(x_42, x_5, x_45, x_4);
lean_dec(x_42);
x_47 = lean_expr_instantiate_rev_range(x_43, x_5, x_45, x_4);
lean_dec(x_45);
lean_dec(x_43);
x_48 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_3);
x_51 = l_Lean_Meta_mkAuxName(x_3, x_41, x_6);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_49);
x_54 = lean_local_ctx_mk_let_decl(x_3, x_49, x_52, x_46, x_47);
x_55 = l_Lean_mkFVar(x_49);
x_56 = lean_array_push(x_4, x_55);
x_2 = x_13;
x_3 = x_54;
x_4 = x_56;
x_6 = x_53;
x_7 = x_44;
x_9 = x_50;
goto _start;
}
default: 
{
lean_object* x_58; 
x_58 = lean_box(0);
x_14 = x_58;
goto block_23;
}
}
block_23:
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
lean_inc(x_3);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__4(x_1, x_3, x_4, x_5, x_6, x_7, x_13, x_15, x_4, x_5, x_21, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_6);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_8);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_8, 1);
lean_dec(x_60);
lean_ctor_set(x_8, 1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_4, x_5, x_7, x_4, x_5, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_8, 0);
x_63 = lean_ctor_get(x_8, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_8);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_63);
lean_inc(x_5);
lean_inc(x_4);
x_65 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_4, x_5, x_7, x_4, x_5, x_64, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_65;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
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
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 4);
lean_inc(x_13);
x_14 = lean_array_get_size(x_11);
x_15 = lean_array_get_size(x_13);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
if (x_16 == 0)
{
lean_object* x_210; 
lean_dec(x_13);
lean_dec(x_7);
x_210 = lean_box(0);
x_18 = x_210;
goto block_209;
}
else
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_unsigned_to_nat(0u);
x_212 = l_Array_isEqvAux___main___at_Lean_Meta_introN___spec__5(x_4, x_7, lean_box(0), x_11, x_13, x_211);
lean_dec(x_13);
lean_dec(x_7);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_box(0);
x_18 = x_213;
goto block_209;
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_9);
x_214 = l_Lean_Meta_introNCore___rarg___closed__1;
lean_inc(x_1);
x_215 = l_Lean_Meta_checkNotAssigned(x_1, x_214, x_17, x_8);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
lean_inc(x_1);
x_217 = l_Lean_Meta_getMVarType(x_1, x_17, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Array_empty___closed__1;
x_221 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_12, x_220, x_211, x_3, x_218, x_17, x_219);
return x_221;
}
else
{
uint8_t x_222; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_217);
if (x_222 == 0)
{
return x_217;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_217, 0);
x_224 = lean_ctor_get(x_217, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_217);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_215);
if (x_226 == 0)
{
return x_215;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_215, 0);
x_228 = lean_ctor_get(x_215, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_215);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
}
block_209:
{
uint8_t x_19; 
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_8, 2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_22 = lean_ctor_get(x_20, 2);
x_47 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_20, 2, x_47);
x_48 = l_Lean_Meta_introNCore___rarg___closed__1;
lean_inc(x_1);
x_49 = l_Lean_Meta_checkNotAssigned(x_1, x_48, x_17, x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_1);
x_51 = l_Lean_Meta_getMVarType(x_1, x_17, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Array_empty___closed__1;
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_12, x_54, x_55, x_3, x_52, x_17, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_9);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 2);
lean_inc(x_58);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_56, 1);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_57, 2);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_58, 2);
lean_dec(x_64);
lean_ctor_set(x_58, 2, x_22);
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_58);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_22);
lean_ctor_set(x_57, 2, x_67);
return x_56;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_57, 1);
x_70 = lean_ctor_get(x_57, 3);
x_71 = lean_ctor_get(x_57, 4);
x_72 = lean_ctor_get(x_57, 5);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_73 = lean_ctor_get(x_58, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_58, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 x_75 = x_58;
} else {
 lean_dec_ref(x_58);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 3, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_22);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_70);
lean_ctor_set(x_77, 4, x_71);
lean_ctor_set(x_77, 5, x_72);
lean_ctor_set(x_56, 1, x_77);
return x_56;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_56, 0);
lean_inc(x_78);
lean_dec(x_56);
x_79 = lean_ctor_get(x_57, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_57, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_57, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_57, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_57, 5);
lean_inc(x_83);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 x_84 = x_57;
} else {
 lean_dec_ref(x_57);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_58, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_58, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 x_87 = x_58;
} else {
 lean_dec_ref(x_58);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 3, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_22);
if (lean_is_scalar(x_84)) {
 x_89 = lean_alloc_ctor(0, 6, 0);
} else {
 x_89 = x_84;
}
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_81);
lean_ctor_set(x_89, 4, x_82);
lean_ctor_set(x_89, 5, x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_56, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_56, 1);
lean_inc(x_92);
lean_dec(x_56);
x_23 = x_91;
x_24 = x_92;
goto block_46;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_51, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_51, 1);
lean_inc(x_94);
lean_dec(x_51);
x_23 = x_93;
x_24 = x_94;
goto block_46;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_49, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_49, 1);
lean_inc(x_96);
lean_dec(x_49);
x_23 = x_95;
x_24 = x_96;
goto block_46;
}
block_46:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 2);
lean_dec(x_28);
lean_ctor_set(x_26, 2, x_22);
if (lean_is_scalar(x_9)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_9;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_24, 2, x_32);
if (lean_is_scalar(x_9)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_9;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_24, 2);
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
x_37 = lean_ctor_get(x_24, 3);
x_38 = lean_ctor_get(x_24, 4);
x_39 = lean_ctor_get(x_24, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_34);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 3, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_22);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_38);
lean_ctor_set(x_44, 5, x_39);
if (lean_is_scalar(x_9)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_9;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_97 = lean_ctor_get(x_20, 0);
x_98 = lean_ctor_get(x_20, 1);
x_99 = lean_ctor_get(x_20, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_20);
x_116 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_97);
lean_ctor_set(x_117, 1, x_98);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_8, 2, x_117);
x_118 = l_Lean_Meta_introNCore___rarg___closed__1;
lean_inc(x_1);
x_119 = l_Lean_Meta_checkNotAssigned(x_1, x_118, x_17, x_8);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
lean_inc(x_1);
x_121 = l_Lean_Meta_getMVarType(x_1, x_17, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Array_empty___closed__1;
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_12, x_124, x_125, x_3, x_122, x_17, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_9);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 5);
lean_inc(x_135);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_136 = x_127;
} else {
 lean_dec_ref(x_127);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_128, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 x_139 = x_128;
} else {
 lean_dec_ref(x_128);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 3, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_99);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(0, 6, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_132);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_141, 3, x_133);
lean_ctor_set(x_141, 4, x_134);
lean_ctor_set(x_141, 5, x_135);
if (lean_is_scalar(x_130)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_130;
}
lean_ctor_set(x_142, 0, x_129);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_126, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_126, 1);
lean_inc(x_144);
lean_dec(x_126);
x_100 = x_143;
x_101 = x_144;
goto block_115;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_121, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_121, 1);
lean_inc(x_146);
lean_dec(x_121);
x_100 = x_145;
x_101 = x_146;
goto block_115;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_ctor_get(x_119, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_119, 1);
lean_inc(x_148);
lean_dec(x_119);
x_100 = x_147;
x_101 = x_148;
goto block_115;
}
block_115:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_102 = lean_ctor_get(x_101, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 5);
lean_inc(x_107);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 x_108 = x_101;
} else {
 lean_dec_ref(x_101);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_102, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_102, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 x_111 = x_102;
} else {
 lean_dec_ref(x_102);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 3, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_99);
if (lean_is_scalar(x_108)) {
 x_113 = lean_alloc_ctor(0, 6, 0);
} else {
 x_113 = x_108;
}
lean_ctor_set(x_113, 0, x_103);
lean_ctor_set(x_113, 1, x_104);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_105);
lean_ctor_set(x_113, 4, x_106);
lean_ctor_set(x_113, 5, x_107);
if (lean_is_scalar(x_9)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_9;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_100);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_149 = lean_ctor_get(x_8, 2);
x_150 = lean_ctor_get(x_8, 0);
x_151 = lean_ctor_get(x_8, 1);
x_152 = lean_ctor_get(x_8, 3);
x_153 = lean_ctor_get(x_8, 4);
x_154 = lean_ctor_get(x_8, 5);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_149);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_8);
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_149, 2);
lean_inc(x_157);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 x_158 = x_149;
} else {
 lean_dec_ref(x_149);
 x_158 = lean_box(0);
}
x_175 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_158)) {
 x_176 = lean_alloc_ctor(0, 3, 0);
} else {
 x_176 = x_158;
}
lean_ctor_set(x_176, 0, x_155);
lean_ctor_set(x_176, 1, x_156);
lean_ctor_set(x_176, 2, x_175);
x_177 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_177, 0, x_150);
lean_ctor_set(x_177, 1, x_151);
lean_ctor_set(x_177, 2, x_176);
lean_ctor_set(x_177, 3, x_152);
lean_ctor_set(x_177, 4, x_153);
lean_ctor_set(x_177, 5, x_154);
x_178 = l_Lean_Meta_introNCore___rarg___closed__1;
lean_inc(x_1);
x_179 = l_Lean_Meta_checkNotAssigned(x_1, x_178, x_17, x_177);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
lean_inc(x_1);
x_181 = l_Lean_Meta_getMVarType(x_1, x_17, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Array_empty___closed__1;
x_185 = lean_unsigned_to_nat(0u);
x_186 = l_Lean_Meta_introNCoreAux___main___at_Lean_Meta_introN___spec__2(x_1, x_2, x_12, x_184, x_185, x_3, x_182, x_17, x_183);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_9);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_190 = x_186;
} else {
 lean_dec_ref(x_186);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_187, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_187, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_187, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_187, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 lean_ctor_release(x_187, 4);
 lean_ctor_release(x_187, 5);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_188, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_188, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 x_199 = x_188;
} else {
 lean_dec_ref(x_188);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 3, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
lean_ctor_set(x_200, 2, x_157);
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(0, 6, 0);
} else {
 x_201 = x_196;
}
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_193);
lean_ctor_set(x_201, 4, x_194);
lean_ctor_set(x_201, 5, x_195);
if (lean_is_scalar(x_190)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_190;
}
lean_ctor_set(x_202, 0, x_189);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_186, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_186, 1);
lean_inc(x_204);
lean_dec(x_186);
x_159 = x_203;
x_160 = x_204;
goto block_174;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_ctor_get(x_181, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_181, 1);
lean_inc(x_206);
lean_dec(x_181);
x_159 = x_205;
x_160 = x_206;
goto block_174;
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_179, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_179, 1);
lean_inc(x_208);
lean_dec(x_179);
x_159 = x_207;
x_160 = x_208;
goto block_174;
}
block_174:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_161 = lean_ctor_get(x_160, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 5);
lean_inc(x_166);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 x_167 = x_160;
} else {
 lean_dec_ref(x_160);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_161, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_161, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 x_170 = x_161;
} else {
 lean_dec_ref(x_161);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 3, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_171, 2, x_157);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 6, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_162);
lean_ctor_set(x_172, 1, x_163);
lean_ctor_set(x_172, 2, x_171);
lean_ctor_set(x_172, 3, x_164);
lean_ctor_set(x_172, 4, x_165);
lean_ctor_set(x_172, 5, x_166);
if (lean_is_scalar(x_9)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_9;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_159);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_6);
if (x_230 == 0)
{
return x_6;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_6, 0);
x_232 = lean_ctor_get(x_6, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_6);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
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
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_introN___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
lean_inc(x_1);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = l_Lean_Expr_Inhabited;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_Expr_Inhabited;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get(x_18, x_17, x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = l_Lean_Expr_Inhabited;
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get(x_26, x_24, x_27);
lean_dec(x_24);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
lean_inc(x_1);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = l_Lean_Expr_Inhabited;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get(x_12, x_10, x_13);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Expr_Inhabited;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_16, x_15, x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = l_Lean_Expr_Inhabited;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get(x_24, x_22, x_25);
lean_dec(x_22);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
return x_6;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
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
l_Lean_Meta_introNCoreAux___main___rarg___closed__1 = _init_l_Lean_Meta_introNCoreAux___main___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_introNCoreAux___main___rarg___closed__1);
l_Lean_Meta_introNCore___rarg___closed__1 = _init_l_Lean_Meta_introNCore___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_introNCore___rarg___closed__1);
l_Lean_Meta_mkAuxName___closed__1 = _init_l_Lean_Meta_mkAuxName___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxName___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
