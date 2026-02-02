// Lean compiler output
// Module: Lean.Compiler.LCNF.DeclHash
// Imports: public import Lean.Compiler.LCNF.Basic
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
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instHashableParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instHashableParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instHashableParam___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t, lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(uint8_t, lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(uint8_t, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t, lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object*);
uint64_t l_Lean_instHashableExternAttrData_hash(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Compiler_instHashableInlineAttributeKind_hash(uint8_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_instHashableFVarId_hash(x_2);
x_5 = l_Lean_Expr_hash(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableParam___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_instHashableParam___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instHashableParam(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = l_Lean_instHashableFVarId_hash(x_7);
lean_dec(x_7);
x_10 = l_Lean_Expr_hash(x_8);
lean_dec_ref(x_8);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_uint64_mix_hash(x_4, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams___redArg(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 7;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; uint64_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; uint64_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashParams___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(uint8_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l_Lean_Compiler_LCNF_hashParams___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_hashParams(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(x_6);
lean_dec(x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(uint8_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = 7;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
if (x_6 == 0)
{
return x_3;
}
else
{
size_t x_8; size_t x_9; uint64_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(x_1, x_2, x_8, x_9, x_3);
return x_10;
}
}
else
{
size_t x_11; size_t x_12; uint64_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(x_1, x_2, x_11, x_12, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = l_Lean_instHashableFVarId_hash(x_5);
x_9 = l_Lean_Expr_hash(x_6);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = l_Lean_Compiler_LCNF_instHashableLetValue_hash(x_1, x_7);
x_12 = l_Lean_Compiler_LCNF_hashCode(x_1, x_4);
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_mix_hash(x_10, x_13);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = l_Lean_instHashableFVarId_hash(x_15);
x_18 = 7;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_16);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
uint64_t x_22; 
x_22 = lean_uint64_mix_hash(x_17, x_18);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_20, x_20);
if (x_23 == 0)
{
if (x_21 == 0)
{
uint64_t x_24; 
x_24 = lean_uint64_mix_hash(x_17, x_18);
return x_24;
}
else
{
size_t x_25; size_t x_26; uint64_t x_27; uint64_t x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_20);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(x_16, x_25, x_26, x_18);
x_28 = lean_uint64_mix_hash(x_17, x_27);
return x_28;
}
}
else
{
size_t x_29; size_t x_30; uint64_t x_31; uint64_t x_32; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_20);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(x_16, x_29, x_30, x_18);
x_32 = lean_uint64_mix_hash(x_17, x_31);
return x_32;
}
}
}
case 4:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_33, 1);
x_35 = lean_ctor_get(x_33, 2);
x_36 = lean_ctor_get(x_33, 3);
x_37 = l_Lean_instHashableFVarId_hash(x_35);
x_38 = l_Lean_Expr_hash(x_34);
x_39 = lean_uint64_mix_hash(x_37, x_38);
x_40 = l_Lean_Compiler_LCNF_hashAlts(x_1, x_36);
x_41 = lean_uint64_mix_hash(x_39, x_40);
return x_41;
}
case 5:
{
lean_object* x_42; uint64_t x_43; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = l_Lean_instHashableFVarId_hash(x_42);
return x_43;
}
case 6:
{
lean_object* x_44; uint64_t x_45; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = l_Lean_Expr_hash(x_44);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 2);
x_50 = lean_ctor_get(x_46, 3);
x_51 = lean_ctor_get(x_46, 4);
x_52 = l_Lean_instHashableFVarId_hash(x_48);
x_53 = l_Lean_Expr_hash(x_50);
x_54 = lean_uint64_mix_hash(x_52, x_53);
x_55 = l_Lean_Compiler_LCNF_hashCode(x_1, x_51);
x_56 = l_Lean_Compiler_LCNF_hashCode(x_1, x_47);
x_57 = lean_uint64_mix_hash(x_55, x_56);
x_58 = lean_uint64_mix_hash(x_54, x_57);
x_59 = 7;
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get_size(x_49);
x_62 = lean_nat_dec_lt(x_60, x_61);
if (x_62 == 0)
{
uint64_t x_63; 
x_63 = lean_uint64_mix_hash(x_58, x_59);
return x_63;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_61, x_61);
if (x_64 == 0)
{
if (x_62 == 0)
{
uint64_t x_65; 
x_65 = lean_uint64_mix_hash(x_58, x_59);
return x_65;
}
else
{
size_t x_66; size_t x_67; uint64_t x_68; uint64_t x_69; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_61);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_49, x_66, x_67, x_59);
x_69 = lean_uint64_mix_hash(x_58, x_68);
return x_69;
}
}
else
{
size_t x_70; size_t x_71; uint64_t x_72; uint64_t x_73; 
x_70 = 0;
x_71 = lean_usize_of_nat(x_61);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_49, x_70, x_71, x_59);
x_73 = lean_uint64_mix_hash(x_58, x_72);
return x_73;
}
}
}
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Name_hash___override(x_3);
x_12 = 7;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_4);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
x_7 = x_12;
goto block_11;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
if (x_15 == 0)
{
x_7 = x_12;
goto block_11;
}
else
{
size_t x_17; size_t x_18; uint64_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_4, x_17, x_18, x_12);
x_7 = x_19;
goto block_11;
}
}
else
{
size_t x_20; size_t x_21; uint64_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_4, x_20, x_21, x_12);
x_7 = x_22;
goto block_11;
}
}
block_11:
{
uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = l_Lean_Compiler_LCNF_hashCode(x_1, x_5);
x_10 = lean_uint64_mix_hash(x_8, x_9);
return x_10;
}
}
else
{
lean_object* x_23; uint64_t x_24; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = l_Lean_Compiler_LCNF_hashCode(x_1, x_23);
return x_24;
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, uint64_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint64_t x_8; uint64_t x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Compiler_LCNF_hashAlt(x_1, x_7);
lean_dec(x_7);
x_9 = lean_uint64_mix_hash(x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(x_6, x_2, x_7, x_8, x_9);
lean_dec_ref(x_2);
x_11 = lean_box_uint64(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_hashAlts(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_hashAlt(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_hashCode(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, uint64_t x_5) {
_start:
{
uint64_t x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(x_6, x_2, x_7, x_8, x_9);
lean_dec_ref(x_2);
x_11 = lean_box_uint64(x_10);
return x_11;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l_Lean_Compiler_LCNF_hashCode(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_instHashableCode___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instHashableCode(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = 0;
x_5 = l_Lean_Compiler_LCNF_hashCode(x_1, x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = 1;
x_9 = l_Lean_instHashableExternAttrData_hash(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instHashableDeclValue(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Name_hash___override(x_3);
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_23; uint64_t x_24; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_10 = lean_ctor_get(x_2, 5);
x_29 = 0;
x_30 = l_Lean_Name_hash___override(x_3);
x_31 = lean_uint64_mix_hash(x_29, x_30);
x_32 = 7;
x_33 = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0(x_32, x_4);
x_34 = lean_uint64_mix_hash(x_31, x_33);
x_35 = l_Lean_Expr_hash(x_5);
x_36 = lean_uint64_mix_hash(x_34, x_35);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_6);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
x_37 = x_32;
goto block_43;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
if (x_46 == 0)
{
x_37 = x_32;
goto block_43;
}
else
{
size_t x_48; size_t x_49; uint64_t x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_45);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_6, x_48, x_49, x_32);
x_37 = x_50;
goto block_43;
}
}
else
{
size_t x_51; size_t x_52; uint64_t x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_45);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_6, x_51, x_52, x_32);
x_37 = x_53;
goto block_43;
}
}
block_22:
{
uint64_t x_13; 
x_13 = lean_uint64_mix_hash(x_11, x_12);
if (lean_obj_tag(x_10) == 0)
{
uint64_t x_14; uint64_t x_15; 
x_14 = 11;
x_15 = lean_uint64_mix_hash(x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Compiler_instHashableInlineAttributeKind_hash(x_17);
x_19 = 13;
x_20 = lean_uint64_mix_hash(x_18, x_19);
x_21 = lean_uint64_mix_hash(x_13, x_20);
return x_21;
}
}
block_28:
{
uint64_t x_25; 
x_25 = lean_uint64_mix_hash(x_23, x_24);
if (x_9 == 0)
{
uint64_t x_26; 
x_26 = 13;
x_11 = x_25;
x_12 = x_26;
goto block_22;
}
else
{
uint64_t x_27; 
x_27 = 11;
x_11 = x_25;
x_12 = x_27;
goto block_22;
}
}
block_43:
{
uint64_t x_38; uint64_t x_39; uint64_t x_40; 
x_38 = lean_uint64_mix_hash(x_36, x_37);
x_39 = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(x_1, x_7);
x_40 = lean_uint64_mix_hash(x_38, x_39);
if (x_8 == 0)
{
uint64_t x_41; 
x_41 = 13;
x_23 = x_40;
x_24 = x_41;
goto block_28;
}
else
{
uint64_t x_42; 
x_42 = 11;
x_23 = x_40;
x_24 = x_42;
goto block_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_instHashableDecl_hash(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instHashableDecl(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
