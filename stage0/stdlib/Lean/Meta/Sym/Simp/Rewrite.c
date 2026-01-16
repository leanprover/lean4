// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Rewrite
// Imports: public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.Simp.Simproc public import Lean.Meta.Sym.Simp.Theorems public import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.Simp.DiscrTree
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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0;
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_3);
x_14 = l_Lean_mkConst(x_11, x_12);
x_15 = l_Lean_mkAppN(x_14, x_13);
lean_dec_ref(x_13);
return x_15;
}
else
{
goto block_9;
}
}
else
{
goto block_9;
}
block_9:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = l_Lean_Expr_instantiateLevelParams(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_8 = l_Lean_mkAppN(x_7, x_6);
lean_dec_ref(x_6);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = 1;
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_10);
x_13 = l_Lean_Meta_Sym_Pattern_match_x3f(x_10, x_2, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_inc(x_17);
x_20 = l_Lean_Expr_instantiateLevelParams(x_11, x_17, x_18);
lean_dec_ref(x_11);
x_21 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_20, x_3);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(x_22, x_19, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_25);
lean_dec_ref(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(x_9, x_10, x_16);
x_28 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_29 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0;
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_30);
lean_dec_ref(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(x_9, x_10, x_16);
x_33 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_35 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0;
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_16);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_15);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0;
lean_ctor_set(x_13, 0, x_43);
return x_13;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_13, 0);
lean_inc(x_44);
lean_dec(x_13);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_ctor_get(x_10, 0);
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_inc(x_46);
x_49 = l_Lean_Expr_instantiateLevelParams(x_11, x_46, x_47);
lean_dec_ref(x_11);
x_50 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_49, x_3);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(x_51, x_48, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_53);
lean_dec_ref(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(x_9, x_10, x_45);
x_57 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_55);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_53);
lean_dec(x_45);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_59 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0;
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_45);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_61 = lean_ctor_get(x_52, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_62 = x_52;
} else {
 lean_dec_ref(x_52);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_45);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_65 = x_50;
} else {
 lean_dec_ref(x_50);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_44);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_67 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0;
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_69 = !lean_is_exclusive(x_13);
if (x_69 == 0)
{
return x_13;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_13, 0);
lean_inc(x_70);
lean_dec(x_13);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_Theorem_rewrite(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; uint8_t x_30; 
x_30 = lean_usize_dec_lt(x_6, x_5);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_7);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec_ref(x_7);
x_32 = lean_array_uget(x_4, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed), 11, 1);
lean_closure_set(x_37, 0, x_33);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_3);
x_38 = l_Lean_Meta_Sym_Simp_simpOverApplied(x_3, x_34, x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_23 = x_39;
x_24 = lean_box(0);
goto block_29;
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_34);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_3);
x_43 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg(x_33, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_23 = x_44;
x_24 = lean_box(0);
goto block_29;
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
block_29:
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_25; 
x_25 = lean_ctor_get_uint8(x_23, 0);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
lean_dec_ref(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
lean_inc_ref(x_2);
{
size_t _tmp_5 = x_27;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_4);
return x_19;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
lean_inc_ref(x_2);
x_12 = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(x_1, x_2);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0;
x_15 = lean_array_size(x_12);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(x_13, x_14, x_2, x_12, x_15, x_16, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0;
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0;
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_Theorems_rewrite(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0 = _init_l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_Theorem_rewrite___redArg___closed__0);
l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0 = _init_l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
