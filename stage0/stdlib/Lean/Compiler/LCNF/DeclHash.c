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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(uint8_t, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(uint8_t, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_hashAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_hashAlt___closed__0;
uint64_t l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(lean_object*);
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
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature___boxed(lean_object*);
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
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 2);
x_9 = l_Lean_instHashableFVarId_hash(x_7);
x_10 = l_Lean_Expr_hash(x_8);
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
lean_dec_ref(x_4);
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
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(x_6);
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
lean_dec_ref(x_4);
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
uint64_t x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; lean_object* x_12; uint64_t x_13; uint8_t x_14; uint64_t x_15; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 2);
x_34 = lean_ctor_get(x_30, 3);
x_35 = l_Lean_instHashableFVarId_hash(x_32);
x_36 = l_Lean_Expr_hash(x_33);
x_37 = lean_uint64_mix_hash(x_35, x_36);
x_38 = l_Lean_Compiler_LCNF_instHashableLetValue_hash(x_1, x_34);
x_39 = l_Lean_Compiler_LCNF_hashCode(x_1, x_31);
x_40 = lean_uint64_mix_hash(x_38, x_39);
x_41 = lean_uint64_mix_hash(x_37, x_40);
return x_41;
}
case 3:
{
lean_object* x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = l_Lean_instHashableFVarId_hash(x_42);
x_45 = 7;
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_43);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
uint64_t x_49; 
x_49 = lean_uint64_mix_hash(x_44, x_45);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_47, x_47);
if (x_50 == 0)
{
if (x_48 == 0)
{
uint64_t x_51; 
x_51 = lean_uint64_mix_hash(x_44, x_45);
return x_51;
}
else
{
size_t x_52; size_t x_53; uint64_t x_54; uint64_t x_55; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_47);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(x_43, x_52, x_53, x_45);
x_55 = lean_uint64_mix_hash(x_44, x_54);
return x_55;
}
}
else
{
size_t x_56; size_t x_57; uint64_t x_58; uint64_t x_59; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_47);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashCode_spec__1___redArg(x_43, x_56, x_57, x_45);
x_59 = lean_uint64_mix_hash(x_44, x_58);
return x_59;
}
}
}
case 4:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_60, 1);
x_62 = lean_ctor_get(x_60, 2);
x_63 = lean_ctor_get(x_60, 3);
x_64 = l_Lean_instHashableFVarId_hash(x_62);
x_65 = l_Lean_Expr_hash(x_61);
x_66 = lean_uint64_mix_hash(x_64, x_65);
x_67 = l_Lean_Compiler_LCNF_hashAlts(x_1, x_63);
x_68 = lean_uint64_mix_hash(x_66, x_67);
return x_68;
}
case 5:
{
lean_object* x_69; uint64_t x_70; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = l_Lean_instHashableFVarId_hash(x_69);
return x_70;
}
case 6:
{
lean_object* x_71; uint64_t x_72; 
x_71 = lean_ctor_get(x_2, 0);
x_72 = l_Lean_Expr_hash(x_71);
return x_72;
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get(x_2, 2);
x_76 = lean_ctor_get(x_2, 3);
x_77 = l_Lean_instHashableFVarId_hash(x_73);
x_78 = lean_uint64_of_nat(x_74);
x_79 = lean_uint64_mix_hash(x_77, x_78);
x_80 = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(x_75);
x_81 = l_Lean_Compiler_LCNF_hashCode(x_1, x_76);
x_82 = lean_uint64_mix_hash(x_80, x_81);
x_83 = lean_uint64_mix_hash(x_79, x_82);
return x_83;
}
case 8:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; 
x_84 = lean_ctor_get(x_2, 0);
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_ctor_get(x_2, 2);
x_87 = lean_ctor_get(x_2, 3);
x_88 = l_Lean_instHashableFVarId_hash(x_84);
x_89 = lean_uint64_of_nat(x_85);
x_90 = lean_uint64_mix_hash(x_88, x_89);
x_91 = l_Lean_instHashableFVarId_hash(x_86);
x_92 = l_Lean_Compiler_LCNF_hashCode(x_1, x_87);
x_93 = lean_uint64_mix_hash(x_91, x_92);
x_94 = lean_uint64_mix_hash(x_90, x_93);
return x_94;
}
case 9:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
x_97 = lean_ctor_get(x_2, 2);
x_98 = lean_ctor_get(x_2, 3);
x_99 = lean_ctor_get(x_2, 4);
x_100 = lean_ctor_get(x_2, 5);
x_101 = l_Lean_instHashableFVarId_hash(x_95);
x_102 = lean_uint64_of_nat(x_96);
x_103 = lean_uint64_mix_hash(x_101, x_102);
x_104 = lean_uint64_of_nat(x_97);
x_105 = l_Lean_instHashableFVarId_hash(x_98);
x_106 = lean_uint64_mix_hash(x_104, x_105);
x_107 = l_Lean_Expr_hash(x_99);
x_108 = l_Lean_Compiler_LCNF_hashCode(x_1, x_100);
x_109 = lean_uint64_mix_hash(x_107, x_108);
x_110 = lean_uint64_mix_hash(x_106, x_109);
x_111 = lean_uint64_mix_hash(x_103, x_110);
return x_111;
}
case 10:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; 
x_112 = lean_ctor_get(x_2, 0);
x_113 = lean_ctor_get(x_2, 1);
x_114 = lean_ctor_get(x_2, 2);
x_115 = l_Lean_instHashableFVarId_hash(x_112);
x_116 = lean_uint64_of_nat(x_113);
x_117 = l_Lean_Compiler_LCNF_hashCode(x_1, x_114);
x_118 = lean_uint64_mix_hash(x_116, x_117);
x_119 = lean_uint64_mix_hash(x_115, x_118);
return x_119;
}
case 11:
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_2, 0);
x_121 = lean_ctor_get(x_2, 1);
x_122 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_123 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_124 = lean_ctor_get(x_2, 2);
x_19 = x_120;
x_20 = x_121;
x_21 = x_122;
x_22 = x_123;
x_23 = x_124;
goto block_29;
}
case 12:
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_2, 0);
x_126 = lean_ctor_get(x_2, 1);
x_127 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_128 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_129 = lean_ctor_get(x_2, 2);
x_19 = x_125;
x_20 = x_126;
x_21 = x_127;
x_22 = x_128;
x_23 = x_129;
goto block_29;
}
case 13:
{
lean_object* x_130; lean_object* x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; 
x_130 = lean_ctor_get(x_2, 0);
x_131 = lean_ctor_get(x_2, 1);
x_132 = l_Lean_instHashableFVarId_hash(x_130);
x_133 = l_Lean_Compiler_LCNF_hashCode(x_1, x_131);
x_134 = lean_uint64_mix_hash(x_132, x_133);
return x_134;
}
default: 
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_135 = lean_ctor_get(x_2, 0);
x_136 = lean_ctor_get(x_2, 1);
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 2);
x_139 = lean_ctor_get(x_135, 3);
x_140 = lean_ctor_get(x_135, 4);
x_141 = l_Lean_instHashableFVarId_hash(x_137);
x_142 = l_Lean_Expr_hash(x_139);
x_143 = lean_uint64_mix_hash(x_141, x_142);
x_144 = l_Lean_Compiler_LCNF_hashCode(x_1, x_140);
x_145 = l_Lean_Compiler_LCNF_hashCode(x_1, x_136);
x_146 = lean_uint64_mix_hash(x_144, x_145);
x_147 = lean_uint64_mix_hash(x_143, x_146);
x_148 = 7;
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_array_get_size(x_138);
x_151 = lean_nat_dec_lt(x_149, x_150);
if (x_151 == 0)
{
uint64_t x_152; 
x_152 = lean_uint64_mix_hash(x_147, x_148);
return x_152;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_150, x_150);
if (x_153 == 0)
{
if (x_151 == 0)
{
uint64_t x_154; 
x_154 = lean_uint64_mix_hash(x_147, x_148);
return x_154;
}
else
{
size_t x_155; size_t x_156; uint64_t x_157; uint64_t x_158; 
x_155 = 0;
x_156 = lean_usize_of_nat(x_150);
x_157 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_138, x_155, x_156, x_148);
x_158 = lean_uint64_mix_hash(x_147, x_157);
return x_158;
}
}
else
{
size_t x_159; size_t x_160; uint64_t x_161; uint64_t x_162; 
x_159 = 0;
x_160 = lean_usize_of_nat(x_150);
x_161 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_138, x_159, x_160, x_148);
x_162 = lean_uint64_mix_hash(x_147, x_161);
return x_162;
}
}
}
}
block_11:
{
uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = l_Lean_Compiler_LCNF_hashCode(x_1, x_4);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_3, x_9);
return x_10;
}
block_18:
{
if (x_14 == 0)
{
uint64_t x_16; 
x_16 = 13;
x_3 = x_13;
x_4 = x_12;
x_5 = x_15;
x_6 = x_16;
goto block_11;
}
else
{
uint64_t x_17; 
x_17 = 11;
x_3 = x_13;
x_4 = x_12;
x_5 = x_15;
x_6 = x_17;
goto block_11;
}
}
block_29:
{
uint64_t x_24; uint64_t x_25; uint64_t x_26; 
x_24 = l_Lean_instHashableFVarId_hash(x_19);
x_25 = lean_uint64_of_nat(x_20);
x_26 = lean_uint64_mix_hash(x_24, x_25);
if (x_22 == 0)
{
uint64_t x_27; 
x_27 = 13;
x_12 = x_23;
x_13 = x_26;
x_14 = x_21;
x_15 = x_27;
goto block_18;
}
else
{
uint64_t x_28; 
x_28 = 11;
x_12 = x_23;
x_13 = x_26;
x_14 = x_21;
x_15 = x_28;
goto block_18;
}
}
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_hashAlt___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
if (lean_obj_tag(x_3) == 0)
{
uint64_t x_25; 
x_25 = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
x_12 = x_25;
goto block_24;
}
else
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_12 = x_26;
goto block_24;
}
block_11:
{
uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = l_Lean_Compiler_LCNF_hashCode(x_1, x_5);
x_10 = lean_uint64_mix_hash(x_8, x_9);
return x_10;
}
block_24:
{
uint64_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = 7;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
x_6 = x_12;
x_7 = x_13;
goto block_11;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
if (x_16 == 0)
{
x_6 = x_12;
x_7 = x_13;
goto block_11;
}
else
{
size_t x_18; size_t x_19; uint64_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_15);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_4, x_18, x_19, x_13);
x_6 = x_12;
x_7 = x_20;
goto block_11;
}
}
else
{
size_t x_21; size_t x_22; uint64_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_4, x_21, x_22, x_13);
x_6 = x_12;
x_7 = x_23;
goto block_11;
}
}
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = l_Lean_Compiler_LCNF_instHashableCtorInfo_hash(x_27);
x_30 = l_Lean_Compiler_LCNF_hashCode(x_1, x_28);
x_31 = lean_uint64_mix_hash(x_29, x_30);
return x_31;
}
default: 
{
lean_object* x_32; uint64_t x_33; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = l_Lean_Compiler_LCNF_hashCode(x_1, x_32);
return x_33;
}
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
x_7 = lean_array_uget_borrowed(x_2, x_3);
x_8 = l_Lean_Compiler_LCNF_hashAlt(x_1, x_7);
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_5);
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
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_3) == 0)
{
uint64_t x_9; 
x_9 = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
x_5 = x_9;
goto block_8;
}
else
{
uint64_t x_10; 
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_5 = x_10;
goto block_8;
}
block_8:
{
uint64_t x_6; 
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_15; uint64_t x_16; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_15 = 0;
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_34; 
x_34 = lean_uint64_once(&l_Lean_Compiler_LCNF_hashAlt___closed__0, &l_Lean_Compiler_LCNF_hashAlt___closed__0_once, _init_l_Lean_Compiler_LCNF_hashAlt___closed__0);
x_16 = x_34;
goto block_33;
}
else
{
uint64_t x_35; 
x_35 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_16 = x_35;
goto block_33;
}
block_14:
{
uint64_t x_9; 
x_9 = lean_uint64_mix_hash(x_7, x_8);
if (x_6 == 0)
{
uint64_t x_10; uint64_t x_11; 
x_10 = 13;
x_11 = lean_uint64_mix_hash(x_9, x_10);
return x_11;
}
else
{
uint64_t x_12; uint64_t x_13; 
x_12 = 11;
x_13 = lean_uint64_mix_hash(x_9, x_12);
return x_13;
}
}
block_33:
{
uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_uint64_mix_hash(x_15, x_16);
x_18 = 7;
x_19 = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableSignature_hash_spec__0(x_18, x_3);
x_20 = lean_uint64_mix_hash(x_17, x_19);
x_21 = l_Lean_Expr_hash(x_4);
x_22 = lean_uint64_mix_hash(x_20, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_5);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
x_7 = x_22;
x_8 = x_18;
goto block_14;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
if (x_25 == 0)
{
x_7 = x_22;
x_8 = x_18;
goto block_14;
}
else
{
size_t x_27; size_t x_28; uint64_t x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_24);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_27, x_28, x_18);
x_7 = x_22;
x_8 = x_29;
goto block_14;
}
}
else
{
size_t x_30; size_t x_31; uint64_t x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_24);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_30, x_31, x_18);
x_7 = x_22;
x_8 = x_32;
goto block_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableSignature_hash(uint8_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_instHashableSignature_hash(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableSignature_hash___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableSignature___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instHashableSignature(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableDecl_hash(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = 0;
x_8 = l_Lean_Compiler_LCNF_instHashableSignature_hash___redArg(x_3);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = l_Lean_Compiler_LCNF_instHashableDeclValue_hash(x_1, x_4);
x_11 = lean_uint64_mix_hash(x_9, x_10);
if (x_5 == 0)
{
uint64_t x_23; 
x_23 = 13;
x_12 = x_23;
goto block_22;
}
else
{
uint64_t x_24; 
x_24 = 11;
x_12 = x_24;
goto block_22;
}
block_22:
{
uint64_t x_13; 
x_13 = lean_uint64_mix_hash(x_11, x_12);
if (lean_obj_tag(x_6) == 0)
{
uint64_t x_14; uint64_t x_15; 
x_14 = 11;
x_15 = lean_uint64_mix_hash(x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Compiler_instHashableInlineAttributeKind_hash(x_17);
x_19 = 13;
x_20 = lean_uint64_mix_hash(x_18, x_19);
x_21 = lean_uint64_mix_hash(x_13, x_20);
return x_21;
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
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DeclHash(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_DeclHash(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_DeclHash(builtin);
}
#ifdef __cplusplus
}
#endif
