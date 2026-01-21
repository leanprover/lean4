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
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(lean_object*, size_t, size_t, uint64_t);
uint64_t l_Lean_instHashableExternAttrData_hash(lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(lean_object*, size_t, size_t, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object*);
uint64_t l_Lean_Compiler_instHashableInlineAttributeKind_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue___closed__0;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instHashableCode___closed__0;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(lean_object*, size_t, size_t, uint64_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam;
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instHashableParam___closed__0;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instHashableDecl___closed__0;
uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(lean_object*);
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
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableParam___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instHashableParam___closed__0;
return x_1;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashParams(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_instHashableArg_hash(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; uint64_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(x_1, x_10, x_11, x_2);
return x_12;
}
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 2);
x_35 = lean_ctor_get(x_31, 3);
x_36 = l_Lean_instHashableFVarId_hash(x_33);
x_37 = l_Lean_Expr_hash(x_34);
x_38 = lean_uint64_mix_hash(x_36, x_37);
x_39 = l_Lean_Compiler_LCNF_instHashableLetValue_hash(x_35);
x_40 = l_Lean_Compiler_LCNF_hashCode(x_32);
x_41 = lean_uint64_mix_hash(x_39, x_40);
x_42 = lean_uint64_mix_hash(x_38, x_41);
return x_42;
}
case 3:
{
lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = l_Lean_instHashableFVarId_hash(x_43);
x_46 = 7;
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_44);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
uint64_t x_50; 
x_50 = lean_uint64_mix_hash(x_45, x_46);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
if (x_49 == 0)
{
uint64_t x_52; 
x_52 = lean_uint64_mix_hash(x_45, x_46);
return x_52;
}
else
{
size_t x_53; size_t x_54; uint64_t x_55; uint64_t x_56; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_48);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(x_44, x_53, x_54, x_46);
x_56 = lean_uint64_mix_hash(x_45, x_55);
return x_56;
}
}
else
{
size_t x_57; size_t x_58; uint64_t x_59; uint64_t x_60; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_48);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1(x_44, x_57, x_58, x_46);
x_60 = lean_uint64_mix_hash(x_45, x_59);
return x_60;
}
}
}
case 4:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; 
x_61 = lean_ctor_get(x_1, 0);
x_62 = lean_ctor_get(x_61, 1);
x_63 = lean_ctor_get(x_61, 2);
x_64 = lean_ctor_get(x_61, 3);
x_65 = l_Lean_instHashableFVarId_hash(x_63);
x_66 = l_Lean_Expr_hash(x_62);
x_67 = lean_uint64_mix_hash(x_65, x_66);
x_68 = l_Lean_Compiler_LCNF_hashAlts(x_64);
x_69 = lean_uint64_mix_hash(x_67, x_68);
return x_69;
}
case 5:
{
lean_object* x_70; uint64_t x_71; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = l_Lean_instHashableFVarId_hash(x_70);
return x_71;
}
case 6:
{
lean_object* x_72; uint64_t x_73; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = l_Lean_Expr_hash(x_72);
return x_73;
}
default: 
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get(x_1, 1);
x_2 = x_74;
x_3 = x_75;
goto block_30;
}
}
block_30:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = l_Lean_instHashableFVarId_hash(x_4);
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
x_19 = lean_uint64_mix_hash(x_14, x_15);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
if (x_18 == 0)
{
uint64_t x_21; 
x_21 = lean_uint64_mix_hash(x_14, x_15);
return x_21;
}
else
{
size_t x_22; size_t x_23; uint64_t x_24; uint64_t x_25; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_17);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_22, x_23, x_15);
x_25 = lean_uint64_mix_hash(x_14, x_24);
return x_25;
}
}
else
{
size_t x_26; size_t x_27; uint64_t x_28; uint64_t x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_17);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_26, x_27, x_15);
x_29 = lean_uint64_mix_hash(x_14, x_28);
return x_29;
}
}
}
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
x_6 = x_11;
goto block_10;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
if (x_14 == 0)
{
x_6 = x_11;
goto block_10;
}
else
{
size_t x_16; size_t x_17; uint64_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_3, x_16, x_17, x_11);
x_6 = x_18;
goto block_10;
}
}
else
{
size_t x_19; size_t x_20; uint64_t x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_3, x_19, x_20, x_11);
x_6 = x_21;
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
lean_object* x_22; uint64_t x_23; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = l_Lean_Compiler_LCNF_hashCode(x_22);
return x_23;
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashAlts_spec__3(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashAlts(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashAlt(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashCode(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_hashCode___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableCode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instHashableCode___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDeclValue_hash(lean_object* x_1) {
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
x_8 = l_Lean_instHashableExternAttrData_hash(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDeclValue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDeclValue_hash___boxed), 1, 0);
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_22; uint64_t x_23; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_9 = lean_ctor_get(x_1, 5);
x_28 = 0;
x_29 = l_Lean_Name_hash___override(x_2);
x_30 = lean_uint64_mix_hash(x_28, x_29);
x_31 = 7;
x_32 = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableDecl_hash_spec__0(x_31, x_3);
x_33 = lean_uint64_mix_hash(x_30, x_32);
x_34 = l_Lean_Expr_hash(x_4);
x_35 = lean_uint64_mix_hash(x_33, x_34);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_5);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
x_36 = x_31;
goto block_42;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
if (x_45 == 0)
{
x_36 = x_31;
goto block_42;
}
else
{
size_t x_47; size_t x_48; uint64_t x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_44);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_47, x_48, x_31);
x_36 = x_49;
goto block_42;
}
}
else
{
size_t x_50; size_t x_51; uint64_t x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_44);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_50, x_51, x_31);
x_36 = x_52;
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
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Compiler_instHashableInlineAttributeKind_hash(x_16);
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
x_38 = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableDecl_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableDecl_hash___boxed), 1, 0);
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
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instHashableParam___closed__0 = _init_l_Lean_Compiler_LCNF_instHashableParam___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableParam___closed__0);
l_Lean_Compiler_LCNF_instHashableParam = _init_l_Lean_Compiler_LCNF_instHashableParam();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableParam);
l_Lean_Compiler_LCNF_instHashableCode___closed__0 = _init_l_Lean_Compiler_LCNF_instHashableCode___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableCode___closed__0);
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
