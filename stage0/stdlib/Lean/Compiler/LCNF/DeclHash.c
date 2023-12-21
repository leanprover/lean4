// Lean compiler output
// Module: Lean.Compiler.LCNF.DeclHash
// Imports: Init Lean.Compiler.LCNF.Basic
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instHashableDecl___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____spec__1(uint64_t, lean_object*);
uint64_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_31_(uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1088_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashAlts___spec__1(lean_object*, size_t, size_t, uint64_t);
uint64_t l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1088____spec__1(lean_object*, size_t, size_t, uint64_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Expr_hash(x_4);
x_6 = lean_uint64_mix_hash(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableParam(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Expr_hash(x_9);
lean_dec(x_9);
x_11 = lean_uint64_mix_hash(x_8, x_10);
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 7;
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
size_t x_7; size_t x_8; uint64_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashParams(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint64_t x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 7;
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
x_10 = l_Lean_Compiler_LCNF_hashCode(x_4);
if (x_9 == 0)
{
uint64_t x_11; uint64_t x_12; 
lean_dec(x_7);
x_11 = lean_uint64_mix_hash(x_5, x_6);
x_12 = lean_uint64_mix_hash(x_11, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
uint64_t x_14; uint64_t x_15; 
lean_dec(x_7);
x_14 = lean_uint64_mix_hash(x_5, x_6);
x_15 = lean_uint64_mix_hash(x_14, x_10);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1(x_3, x_16, x_17, x_6);
x_19 = lean_uint64_mix_hash(x_5, x_18);
x_20 = lean_uint64_mix_hash(x_19, x_10);
return x_20;
}
}
}
else
{
lean_object* x_21; uint64_t x_22; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = l_Lean_Compiler_LCNF_hashCode(x_21);
return x_22;
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_4);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_Expr_hash(x_6);
x_8 = lean_uint64_mix_hash(x_5, x_7);
x_9 = lean_ctor_get(x_2, 3);
x_10 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1088_(x_9);
x_11 = l_Lean_Compiler_LCNF_hashCode(x_3);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = lean_uint64_mix_hash(x_8, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_14);
x_17 = 7;
x_18 = lean_array_get_size(x_15);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint64_t x_21; 
lean_dec(x_18);
x_21 = lean_uint64_mix_hash(x_16, x_17);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
uint64_t x_23; 
lean_dec(x_18);
x_23 = lean_uint64_mix_hash(x_16, x_17);
return x_23;
}
else
{
size_t x_24; size_t x_25; uint64_t x_26; uint64_t x_27; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1088____spec__1(x_15, x_24, x_25, x_17);
x_27 = lean_uint64_mix_hash(x_16, x_26);
return x_27;
}
}
}
case 4:
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_28, 2);
x_30 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_29);
x_31 = lean_ctor_get(x_28, 1);
x_32 = l_Lean_Expr_hash(x_31);
x_33 = lean_uint64_mix_hash(x_30, x_32);
x_34 = lean_ctor_get(x_28, 3);
x_35 = l_Lean_Compiler_LCNF_hashAlts(x_34);
x_36 = lean_uint64_mix_hash(x_33, x_35);
return x_36;
}
case 5:
{
lean_object* x_37; uint64_t x_38; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_37);
return x_38;
}
case 6:
{
lean_object* x_39; uint64_t x_40; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = l_Lean_Expr_hash(x_39);
return x_40;
}
default: 
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_41, 0);
x_44 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_43);
x_45 = lean_ctor_get(x_41, 3);
x_46 = l_Lean_Expr_hash(x_45);
x_47 = lean_uint64_mix_hash(x_44, x_46);
x_48 = lean_ctor_get(x_41, 4);
x_49 = l_Lean_Compiler_LCNF_hashCode(x_48);
x_50 = l_Lean_Compiler_LCNF_hashCode(x_42);
x_51 = lean_uint64_mix_hash(x_49, x_50);
x_52 = lean_uint64_mix_hash(x_47, x_51);
x_53 = lean_ctor_get(x_41, 2);
x_54 = 7;
x_55 = lean_array_get_size(x_53);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_lt(x_56, x_55);
if (x_57 == 0)
{
uint64_t x_58; 
lean_dec(x_55);
x_58 = lean_uint64_mix_hash(x_52, x_54);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_55, x_55);
if (x_59 == 0)
{
uint64_t x_60; 
lean_dec(x_55);
x_60 = lean_uint64_mix_hash(x_52, x_54);
return x_60;
}
else
{
size_t x_61; size_t x_62; uint64_t x_63; uint64_t x_64; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_63 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1(x_53, x_61, x_62, x_54);
x_64 = lean_uint64_mix_hash(x_52, x_63);
return x_64;
}
}
}
}
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashAlts___spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_hashAlt(x_6);
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 7;
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
size_t x_7; size_t x_8; uint64_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashAlts___spec__1(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashAlt(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashCode(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashAlts___spec__1(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashAlts(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Compiler_LCNF_hashCode(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableCode(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____spec__1(uint64_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint64_t x_21; uint64_t x_22; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_dec(x_1);
x_10 = 0;
x_11 = l_Lean_Name_hash___override(x_2);
lean_dec(x_2);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 7;
x_14 = l_List_foldl___at___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____spec__1(x_13, x_3);
lean_dec(x_3);
x_15 = lean_uint64_mix_hash(x_12, x_14);
x_16 = l_Lean_Expr_hash(x_4);
lean_dec(x_4);
x_17 = lean_uint64_mix_hash(x_15, x_16);
x_18 = lean_array_get_size(x_5);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
x_21 = l_Lean_Compiler_LCNF_hashCode(x_6);
lean_dec(x_6);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_5);
x_22 = x_13;
goto block_61;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_18, x_18);
if (x_62 == 0)
{
lean_dec(x_18);
lean_dec(x_5);
x_22 = x_13;
goto block_61;
}
else
{
size_t x_63; size_t x_64; uint64_t x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_hashParams___spec__1(x_5, x_63, x_64, x_13);
lean_dec(x_5);
x_22 = x_65;
goto block_61;
}
}
block_61:
{
uint64_t x_23; uint64_t x_24; 
x_23 = lean_uint64_mix_hash(x_17, x_22);
x_24 = lean_uint64_mix_hash(x_23, x_21);
if (x_7 == 0)
{
uint64_t x_25; uint64_t x_26; 
x_25 = 13;
x_26 = lean_uint64_mix_hash(x_24, x_25);
if (x_8 == 0)
{
uint64_t x_27; 
x_27 = lean_uint64_mix_hash(x_26, x_25);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_28; uint64_t x_29; 
x_28 = 11;
x_29 = lean_uint64_mix_hash(x_27, x_28);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; 
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_31_(x_31);
x_33 = lean_uint64_mix_hash(x_32, x_25);
x_34 = lean_uint64_mix_hash(x_27, x_33);
return x_34;
}
}
else
{
uint64_t x_35; uint64_t x_36; 
x_35 = 11;
x_36 = lean_uint64_mix_hash(x_26, x_35);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_37; 
x_37 = lean_uint64_mix_hash(x_36, x_35);
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; 
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
x_40 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_31_(x_39);
x_41 = lean_uint64_mix_hash(x_40, x_25);
x_42 = lean_uint64_mix_hash(x_36, x_41);
return x_42;
}
}
}
else
{
uint64_t x_43; uint64_t x_44; 
x_43 = 11;
x_44 = lean_uint64_mix_hash(x_24, x_43);
if (x_8 == 0)
{
uint64_t x_45; uint64_t x_46; 
x_45 = 13;
x_46 = lean_uint64_mix_hash(x_44, x_45);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_47; 
x_47 = lean_uint64_mix_hash(x_46, x_43);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; 
x_48 = lean_ctor_get(x_9, 0);
lean_inc(x_48);
lean_dec(x_9);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
x_50 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_31_(x_49);
x_51 = lean_uint64_mix_hash(x_50, x_45);
x_52 = lean_uint64_mix_hash(x_46, x_51);
return x_52;
}
}
else
{
uint64_t x_53; 
x_53 = lean_uint64_mix_hash(x_44, x_43);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_54; 
x_54 = lean_uint64_mix_hash(x_53, x_43);
return x_54;
}
else
{
lean_object* x_55; uint8_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; 
x_55 = lean_ctor_get(x_9, 0);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
x_57 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_31_(x_56);
x_58 = 13;
x_59 = lean_uint64_mix_hash(x_57, x_58);
x_60 = lean_uint64_mix_hash(x_53, x_59);
return x_60;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266_(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instHashableDecl___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instHashableDecl___closed__1 = _init_l_Lean_Compiler_LCNF_instHashableDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableDecl___closed__1);
l_Lean_Compiler_LCNF_instHashableDecl = _init_l_Lean_Compiler_LCNF_instHashableDecl();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableDecl);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
