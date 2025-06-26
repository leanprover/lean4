// Lean compiler output
// Module: Lean.Compiler.LCNF.DeclHash
// Imports: Lean.Compiler.LCNF.Basic
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0(uint64_t, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273____boxed(lean_object*);
uint64_t l_Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36_(uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0(lean_object*, size_t, size_t, uint64_t);
uint64_t l_Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477_(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319_(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl;
static lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___closed__0;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1448_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273_(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam;
uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1448__spec__0(lean_object*, size_t, size_t, uint64_t);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instHashableDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319____boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_5 = l_Lean_Expr_hash(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableParam() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableParam___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
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
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_7);
lean_dec(x_7);
x_10 = l_Lean_Expr_hash(x_8);
lean_dec(x_8);
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 7;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; uint64_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_1, x_5, x_6, x_7);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Name_hash___override(x_2);
x_11 = 7;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_3);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
x_6 = x_11;
goto block_10;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
x_6 = x_11;
goto block_10;
}
else
{
size_t x_16; size_t x_17; uint64_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_3, x_16, x_17, x_11);
x_6 = x_18;
goto block_10;
}
}
block_10:
{
uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = l_Lean_Compiler_LCNF_hashCode(x_4);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
}
else
{
lean_object* x_19; uint64_t x_20; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_Lean_Compiler_LCNF_hashCode(x_19);
return x_20;
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 2);
x_31 = lean_ctor_get(x_27, 3);
x_32 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_29);
x_33 = l_Lean_Expr_hash(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = l_Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1448_(x_31);
x_36 = l_Lean_Compiler_LCNF_hashCode(x_28);
x_37 = lean_uint64_mix_hash(x_35, x_36);
x_38 = lean_uint64_mix_hash(x_34, x_37);
return x_38;
}
case 3:
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_39);
x_42 = 7;
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_40);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
uint64_t x_46; 
lean_dec(x_44);
x_46 = lean_uint64_mix_hash(x_41, x_42);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_44, x_44);
if (x_47 == 0)
{
uint64_t x_48; 
lean_dec(x_44);
x_48 = lean_uint64_mix_hash(x_41, x_42);
return x_48;
}
else
{
size_t x_49; size_t x_50; uint64_t x_51; uint64_t x_52; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_51 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1448__spec__0(x_40, x_49, x_50, x_42);
x_52 = lean_uint64_mix_hash(x_41, x_51);
return x_52;
}
}
}
case 4:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; 
x_53 = lean_ctor_get(x_1, 0);
x_54 = lean_ctor_get(x_53, 1);
x_55 = lean_ctor_get(x_53, 2);
x_56 = lean_ctor_get(x_53, 3);
x_57 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_55);
x_58 = l_Lean_Expr_hash(x_54);
x_59 = lean_uint64_mix_hash(x_57, x_58);
x_60 = l_Lean_Compiler_LCNF_hashAlts(x_56);
x_61 = lean_uint64_mix_hash(x_59, x_60);
return x_61;
}
case 5:
{
lean_object* x_62; uint64_t x_63; 
x_62 = lean_ctor_get(x_1, 0);
x_63 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_62);
return x_63;
}
case 6:
{
lean_object* x_64; uint64_t x_65; 
x_64 = lean_ctor_get(x_1, 0);
x_65 = l_Lean_Expr_hash(x_64);
return x_65;
}
default: 
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = lean_ctor_get(x_1, 1);
x_2 = x_66;
x_3 = x_67;
goto block_26;
}
}
block_26:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_4);
x_9 = l_Lean_Expr_hash(x_6);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = l_Lean_Compiler_LCNF_hashCode(x_7);
x_12 = l_Lean_Compiler_LCNF_hashCode(x_3);
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_mix_hash(x_10, x_13);
x_15 = 7;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_5);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
uint64_t x_19; 
lean_dec(x_17);
x_19 = lean_uint64_mix_hash(x_14, x_15);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
uint64_t x_21; 
lean_dec(x_17);
x_21 = lean_uint64_mix_hash(x_14, x_15);
return x_21;
}
else
{
size_t x_22; size_t x_23; uint64_t x_24; uint64_t x_25; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_22, x_23, x_15);
x_25 = lean_uint64_mix_hash(x_14, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
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
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; uint64_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0(x_1, x_7, x_8, x_2);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0(x_1, x_5, x_6, x_7);
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Compiler_LCNF_hashCode(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableCode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableCode___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_Compiler_LCNF_hashCode(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 1;
x_8 = l_Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477_(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDeclValue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDeclValue() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instHashableDeclValue___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0(uint64_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_22; uint64_t x_23; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
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
x_28 = 0;
x_29 = l_Lean_Name_hash___override(x_2);
lean_dec(x_2);
x_30 = lean_uint64_mix_hash(x_28, x_29);
x_31 = 7;
x_32 = l_List_foldl___at___Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0(x_31, x_3);
lean_dec(x_3);
x_33 = lean_uint64_mix_hash(x_30, x_32);
x_34 = l_Lean_Expr_hash(x_4);
lean_dec(x_4);
x_35 = lean_uint64_mix_hash(x_33, x_34);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_5);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_5);
x_36 = x_31;
goto block_42;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_5);
x_36 = x_31;
goto block_42;
}
else
{
size_t x_47; size_t x_48; uint64_t x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_49 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_47, x_48, x_31);
lean_dec(x_5);
x_36 = x_49;
goto block_42;
}
}
block_21:
{
uint64_t x_12; 
x_12 = lean_uint64_mix_hash(x_10, x_11);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_13; uint64_t x_14; 
x_13 = 11;
x_14 = lean_uint64_mix_hash(x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
x_17 = l_Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36_(x_16);
x_18 = 13;
x_19 = lean_uint64_mix_hash(x_17, x_18);
x_20 = lean_uint64_mix_hash(x_12, x_19);
return x_20;
}
}
block_27:
{
uint64_t x_24; 
x_24 = lean_uint64_mix_hash(x_22, x_23);
if (x_8 == 0)
{
uint64_t x_25; 
x_25 = 13;
x_10 = x_24;
x_11 = x_25;
goto block_21;
}
else
{
uint64_t x_26; 
x_26 = 11;
x_10 = x_24;
x_11 = x_26;
goto block_21;
}
}
block_42:
{
uint64_t x_37; uint64_t x_38; uint64_t x_39; 
x_37 = lean_uint64_mix_hash(x_35, x_36);
x_38 = l_Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273_(x_6);
lean_dec(x_6);
x_39 = lean_uint64_mix_hash(x_37, x_38);
if (x_7 == 0)
{
uint64_t x_40; 
x_40 = 13;
x_22 = x_39;
x_23 = x_40;
goto block_27;
}
else
{
uint64_t x_41; 
x_41 = 11;
x_22 = x_39;
x_23 = x_41;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at___Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319_(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instHashableDecl___closed__0;
return x_1;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instHashableParam = _init_l_Lean_Compiler_LCNF_instHashableParam();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableParam);
l_Lean_Compiler_LCNF_instHashableCode = _init_l_Lean_Compiler_LCNF_instHashableCode();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableCode);
l_Lean_Compiler_LCNF_instHashableDeclValue___closed__0 = _init_l_Lean_Compiler_LCNF_instHashableDeclValue___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableDeclValue___closed__0);
l_Lean_Compiler_LCNF_instHashableDeclValue = _init_l_Lean_Compiler_LCNF_instHashableDeclValue();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableDeclValue);
l_Lean_Compiler_LCNF_instHashableDecl___closed__0 = _init_l_Lean_Compiler_LCNF_instHashableDecl___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableDecl___closed__0);
l_Lean_Compiler_LCNF_instHashableDecl = _init_l_Lean_Compiler_LCNF_instHashableDecl();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableDecl);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
