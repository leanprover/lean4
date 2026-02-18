// Lean compiler output
// Module: Lean.Compiler.LCNF.Renaming
// Imports: public import Lean.Compiler.LCNF.CompilerM
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
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Name_quickCmp(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_9 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(x_3, x_6);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
lean_inc_ref(x_7);
lean_inc(x_6);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_st_ref_take(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_2, 1, x_15);
lean_inc_ref(x_2);
x_19 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_18, x_2);
lean_ctor_set(x_16, 0, x_19);
x_20 = lean_st_ref_set(x_4, x_16);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_15);
lean_inc_ref(x_2);
x_23 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_21, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_st_ref_set(x_4, x_24);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_st_ref_take(x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_26);
lean_inc_ref(x_2);
x_31 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_28, x_2);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_st_ref_set(x_4, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_2);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_36 = x_9;
} else {
 lean_dec_ref(x_9);
 x_36 = lean_box(0);
}
x_37 = lean_st_ref_take(x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_7);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_8);
lean_inc_ref(x_41);
x_42 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_38, x_41);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
x_44 = lean_st_ref_set(x_4, x_43);
if (lean_is_scalar(x_36)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_36;
 lean_ctor_set_tag(x_45, 0);
}
lean_ctor_set(x_45, 0, x_41);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_9);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_2);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(x_6, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(x_1, x_2, x_3, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_applyRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Param_applyRenaming(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(x_3, x_6);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_st_ref_take(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_2, 1, x_16);
lean_inc_ref(x_2);
x_20 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_19, x_2);
lean_ctor_set(x_17, 0, x_20);
x_21 = lean_st_ref_set(x_4, x_17);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_16);
lean_inc_ref(x_2);
x_24 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_22, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_st_ref_set(x_4, x_25);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_st_ref_take(x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_27);
lean_inc_ref(x_2);
x_32 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_29, x_2);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_st_ref_set(x_4, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_2);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_37 = x_9;
} else {
 lean_dec_ref(x_9);
 x_37 = lean_box(0);
}
x_38 = lean_st_ref_take(x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_7);
lean_ctor_set(x_42, 3, x_8);
lean_inc_ref(x_42);
x_43 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_39, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = lean_st_ref_set(x_4, x_44);
if (lean_is_scalar(x_37)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_37;
 lean_ctor_set_tag(x_46, 0);
}
lean_ctor_set(x_46, 0, x_42);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_9);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_2);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(x_6, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(x_1, x_2, x_3, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_applyRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_LetDecl_applyRenaming(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget_borrowed(x_4, x_3);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(x_1, x_10, x_2, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ptr_addr(x_10);
x_14 = lean_ptr_addr(x_12);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
x_18 = lean_array_fset(x_4, x_3, x_12);
lean_dec(x_3);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_fget_borrowed(x_4, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 2);
x_29 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_27);
x_30 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(x_1, x_2, x_29, x_27, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc_ref(x_28);
x_32 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_28, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
lean_inc_ref(x_13);
x_34 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(x_1, x_13, x_31, x_33);
x_14 = x_34;
x_15 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec_ref(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
case 1:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_41);
x_42 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_41, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc_ref(x_13);
x_44 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_13, x_43);
x_14 = x_44;
x_15 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_48);
x_49 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_48, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc_ref(x_13);
x_51 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_13, x_50);
x_14 = x_51;
x_15 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_52; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
block_26:
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ptr_addr(x_13);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
x_21 = lean_array_fset(x_4, x_3, x_14);
lean_dec(x_3);
x_3 = x_20;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
x_3 = x_24;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
x_11 = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(x_1, x_9, x_3, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc_ref(x_10);
x_13 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; size_t x_25; size_t x_26; uint8_t x_27; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
x_25 = lean_ptr_addr(x_10);
x_26 = lean_ptr_addr(x_14);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
x_16 = x_27;
goto block_24;
}
else
{
size_t x_28; size_t x_29; uint8_t x_30; 
x_28 = lean_ptr_addr(x_9);
x_29 = lean_ptr_addr(x_12);
x_30 = lean_usize_dec_eq(x_28, x_29);
x_16 = x_30;
goto block_24;
}
block_24:
{
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_12);
if (lean_is_scalar(x_15)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_15;
}
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_14);
if (lean_is_scalar(x_15)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_15;
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_12);
if (lean_is_scalar(x_15)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_15;
}
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_2);
return x_13;
}
}
else
{
uint8_t x_31; 
lean_dec_ref(x_2);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_34);
x_36 = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(x_1, x_34, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc_ref(x_35);
x_38 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_35, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; size_t x_50; size_t x_51; uint8_t x_52; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_50 = lean_ptr_addr(x_35);
x_51 = lean_ptr_addr(x_39);
x_52 = lean_usize_dec_eq(x_50, x_51);
if (x_52 == 0)
{
x_41 = x_52;
goto block_49;
}
else
{
size_t x_53; size_t x_54; uint8_t x_55; 
x_53 = lean_ptr_addr(x_34);
x_54 = lean_ptr_addr(x_37);
x_55 = lean_usize_dec_eq(x_53, x_54);
x_41 = x_55;
goto block_49;
}
block_49:
{
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_2, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
lean_ctor_set(x_2, 1, x_39);
lean_ctor_set(x_2, 0, x_37);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_2);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_39);
if (lean_is_scalar(x_40)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_40;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_37);
if (lean_is_scalar(x_40)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_40;
}
lean_ctor_set(x_48, 0, x_2);
return x_48;
}
}
}
else
{
lean_dec(x_37);
lean_dec_ref(x_2);
return x_38;
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_36);
if (x_56 == 0)
{
return x_36;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_36, 0);
lean_inc(x_57);
lean_dec(x_36);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
case 2:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_59);
x_61 = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(x_1, x_59, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc_ref(x_60);
x_63 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_60, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; size_t x_75; size_t x_76; uint8_t x_77; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_75 = lean_ptr_addr(x_60);
x_76 = lean_ptr_addr(x_64);
x_77 = lean_usize_dec_eq(x_75, x_76);
if (x_77 == 0)
{
x_66 = x_77;
goto block_74;
}
else
{
size_t x_78; size_t x_79; uint8_t x_80; 
x_78 = lean_ptr_addr(x_59);
x_79 = lean_ptr_addr(x_62);
x_80 = lean_usize_dec_eq(x_78, x_79);
x_66 = x_80;
goto block_74;
}
block_74:
{
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_2, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_2, 0);
lean_dec(x_69);
lean_ctor_set(x_2, 1, x_64);
lean_ctor_set(x_2, 0, x_62);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_2);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_2);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_64);
if (lean_is_scalar(x_65)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_65;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_dec(x_64);
lean_dec(x_62);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_2);
return x_73;
}
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_2);
return x_63;
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_2);
x_81 = !lean_is_exclusive(x_61);
if (x_81 == 0)
{
return x_61;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_61, 0);
lean_inc(x_82);
lean_dec(x_61);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
case 4:
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_84);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
x_88 = lean_ctor_get(x_84, 2);
x_89 = lean_ctor_get(x_84, 3);
x_90 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_89);
x_91 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(x_1, x_3, x_90, x_89, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; size_t x_94; size_t x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ptr_addr(x_89);
lean_dec_ref(x_89);
x_95 = lean_ptr_addr(x_93);
x_96 = lean_usize_dec_eq(x_94, x_95);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_2);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_2, 0);
lean_dec(x_98);
lean_ctor_set(x_84, 3, x_93);
lean_ctor_set(x_91, 0, x_2);
return x_91;
}
else
{
lean_object* x_99; 
lean_dec(x_2);
lean_ctor_set(x_84, 3, x_93);
x_99 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_99, 0, x_84);
lean_ctor_set(x_91, 0, x_99);
return x_91;
}
}
else
{
lean_dec(x_93);
lean_free_object(x_84);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_ctor_set(x_91, 0, x_2);
return x_91;
}
}
else
{
lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_91, 0);
lean_inc(x_100);
lean_dec(x_91);
x_101 = lean_ptr_addr(x_89);
lean_dec_ref(x_89);
x_102 = lean_ptr_addr(x_100);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_104 = x_2;
} else {
 lean_dec_ref(x_2);
 x_104 = lean_box(0);
}
lean_ctor_set(x_84, 3, x_100);
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(4, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_84);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
else
{
lean_object* x_107; 
lean_dec(x_100);
lean_free_object(x_84);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_2);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_free_object(x_84);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_2);
x_108 = !lean_is_exclusive(x_91);
if (x_108 == 0)
{
return x_91;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_91, 0);
lean_inc(x_109);
lean_dec(x_91);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_84, 0);
x_112 = lean_ctor_get(x_84, 1);
x_113 = lean_ctor_get(x_84, 2);
x_114 = lean_ctor_get(x_84, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_84);
x_115 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_114);
x_116 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(x_1, x_3, x_115, x_114, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; size_t x_119; size_t x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_ptr_addr(x_114);
lean_dec_ref(x_114);
x_120 = lean_ptr_addr(x_117);
x_121 = lean_usize_dec_eq(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_122 = x_2;
} else {
 lean_dec_ref(x_2);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_123, 0, x_111);
lean_ctor_set(x_123, 1, x_112);
lean_ctor_set(x_123, 2, x_113);
lean_ctor_set(x_123, 3, x_117);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(4, 1, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
if (lean_is_scalar(x_118)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_118;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
else
{
lean_object* x_126; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_118)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_118;
}
lean_ctor_set(x_126, 0, x_2);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_2);
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_128 = x_116;
} else {
 lean_dec_ref(x_116);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
}
}
case 7:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_2, 0);
x_131 = lean_ctor_get(x_2, 1);
x_132 = lean_ctor_get(x_2, 2);
x_133 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_133);
x_134 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_133, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; size_t x_137; size_t x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ptr_addr(x_133);
x_138 = lean_ptr_addr(x_136);
x_139 = lean_usize_dec_eq(x_137, x_138);
if (x_139 == 0)
{
uint8_t x_140; 
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
x_140 = !lean_is_exclusive(x_2);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_2, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_2, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_2, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_2, 0);
lean_dec(x_144);
lean_ctor_set(x_2, 3, x_136);
lean_ctor_set(x_134, 0, x_2);
return x_134;
}
else
{
lean_object* x_145; 
lean_dec(x_2);
x_145 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_145, 0, x_130);
lean_ctor_set(x_145, 1, x_131);
lean_ctor_set(x_145, 2, x_132);
lean_ctor_set(x_145, 3, x_136);
lean_ctor_set(x_134, 0, x_145);
return x_134;
}
}
else
{
lean_dec(x_136);
lean_ctor_set(x_134, 0, x_2);
return x_134;
}
}
else
{
lean_object* x_146; size_t x_147; size_t x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_134, 0);
lean_inc(x_146);
lean_dec(x_134);
x_147 = lean_ptr_addr(x_133);
x_148 = lean_ptr_addr(x_146);
x_149 = lean_usize_dec_eq(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_150 = x_2;
} else {
 lean_dec_ref(x_2);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(7, 4, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_130);
lean_ctor_set(x_151, 1, x_131);
lean_ctor_set(x_151, 2, x_132);
lean_ctor_set(x_151, 3, x_146);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
else
{
lean_object* x_153; 
lean_dec(x_146);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_2);
return x_153;
}
}
}
else
{
lean_dec_ref(x_2);
return x_134;
}
}
case 8:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_2, 0);
x_155 = lean_ctor_get(x_2, 1);
x_156 = lean_ctor_get(x_2, 2);
x_157 = lean_ctor_get(x_2, 3);
x_158 = lean_ctor_get(x_2, 4);
x_159 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_159);
x_160 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_159, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_160) == 0)
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; size_t x_163; size_t x_164; uint8_t x_165; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ptr_addr(x_159);
x_164 = lean_ptr_addr(x_162);
x_165 = lean_usize_dec_eq(x_163, x_164);
if (x_165 == 0)
{
uint8_t x_166; 
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
x_166 = !lean_is_exclusive(x_2);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_2, 5);
lean_dec(x_167);
x_168 = lean_ctor_get(x_2, 4);
lean_dec(x_168);
x_169 = lean_ctor_get(x_2, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_2, 2);
lean_dec(x_170);
x_171 = lean_ctor_get(x_2, 1);
lean_dec(x_171);
x_172 = lean_ctor_get(x_2, 0);
lean_dec(x_172);
lean_ctor_set(x_2, 5, x_162);
lean_ctor_set(x_160, 0, x_2);
return x_160;
}
else
{
lean_object* x_173; 
lean_dec(x_2);
x_173 = lean_alloc_ctor(8, 6, 0);
lean_ctor_set(x_173, 0, x_154);
lean_ctor_set(x_173, 1, x_155);
lean_ctor_set(x_173, 2, x_156);
lean_ctor_set(x_173, 3, x_157);
lean_ctor_set(x_173, 4, x_158);
lean_ctor_set(x_173, 5, x_162);
lean_ctor_set(x_160, 0, x_173);
return x_160;
}
}
else
{
lean_dec(x_162);
lean_ctor_set(x_160, 0, x_2);
return x_160;
}
}
else
{
lean_object* x_174; size_t x_175; size_t x_176; uint8_t x_177; 
x_174 = lean_ctor_get(x_160, 0);
lean_inc(x_174);
lean_dec(x_160);
x_175 = lean_ptr_addr(x_159);
x_176 = lean_ptr_addr(x_174);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_178 = x_2;
} else {
 lean_dec_ref(x_2);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(8, 6, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_154);
lean_ctor_set(x_179, 1, x_155);
lean_ctor_set(x_179, 2, x_156);
lean_ctor_set(x_179, 3, x_157);
lean_ctor_set(x_179, 4, x_158);
lean_ctor_set(x_179, 5, x_174);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
else
{
lean_object* x_181; 
lean_dec(x_174);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_2);
return x_181;
}
}
}
else
{
lean_dec_ref(x_2);
return x_160;
}
}
case 9:
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_2, 0);
x_183 = lean_ctor_get(x_2, 1);
x_184 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_185 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_186 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_186);
x_187 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_186, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; size_t x_190; size_t x_191; uint8_t x_192; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_ptr_addr(x_186);
x_191 = lean_ptr_addr(x_189);
x_192 = lean_usize_dec_eq(x_190, x_191);
if (x_192 == 0)
{
uint8_t x_193; 
lean_inc(x_183);
lean_inc(x_182);
x_193 = !lean_is_exclusive(x_2);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_2, 2);
lean_dec(x_194);
x_195 = lean_ctor_get(x_2, 1);
lean_dec(x_195);
x_196 = lean_ctor_get(x_2, 0);
lean_dec(x_196);
lean_ctor_set(x_2, 2, x_189);
lean_ctor_set(x_187, 0, x_2);
return x_187;
}
else
{
lean_object* x_197; 
lean_dec(x_2);
x_197 = lean_alloc_ctor(9, 3, 2);
lean_ctor_set(x_197, 0, x_182);
lean_ctor_set(x_197, 1, x_183);
lean_ctor_set(x_197, 2, x_189);
lean_ctor_set_uint8(x_197, sizeof(void*)*3, x_184);
lean_ctor_set_uint8(x_197, sizeof(void*)*3 + 1, x_185);
lean_ctor_set(x_187, 0, x_197);
return x_187;
}
}
else
{
lean_dec(x_189);
lean_ctor_set(x_187, 0, x_2);
return x_187;
}
}
else
{
lean_object* x_198; size_t x_199; size_t x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_187, 0);
lean_inc(x_198);
lean_dec(x_187);
x_199 = lean_ptr_addr(x_186);
x_200 = lean_ptr_addr(x_198);
x_201 = lean_usize_dec_eq(x_199, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_inc(x_183);
lean_inc(x_182);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_202 = x_2;
} else {
 lean_dec_ref(x_2);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(9, 3, 2);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_182);
lean_ctor_set(x_203, 1, x_183);
lean_ctor_set(x_203, 2, x_198);
lean_ctor_set_uint8(x_203, sizeof(void*)*3, x_184);
lean_ctor_set_uint8(x_203, sizeof(void*)*3 + 1, x_185);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
else
{
lean_object* x_205; 
lean_dec(x_198);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_2);
return x_205;
}
}
}
else
{
lean_dec_ref(x_2);
return x_187;
}
}
case 10:
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
x_206 = lean_ctor_get(x_2, 0);
x_207 = lean_ctor_get(x_2, 1);
x_208 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_209 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_210 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_210);
x_211 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_210, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; size_t x_214; size_t x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ptr_addr(x_210);
x_215 = lean_ptr_addr(x_213);
x_216 = lean_usize_dec_eq(x_214, x_215);
if (x_216 == 0)
{
uint8_t x_217; 
lean_inc(x_207);
lean_inc(x_206);
x_217 = !lean_is_exclusive(x_2);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_2, 2);
lean_dec(x_218);
x_219 = lean_ctor_get(x_2, 1);
lean_dec(x_219);
x_220 = lean_ctor_get(x_2, 0);
lean_dec(x_220);
lean_ctor_set(x_2, 2, x_213);
lean_ctor_set(x_211, 0, x_2);
return x_211;
}
else
{
lean_object* x_221; 
lean_dec(x_2);
x_221 = lean_alloc_ctor(10, 3, 2);
lean_ctor_set(x_221, 0, x_206);
lean_ctor_set(x_221, 1, x_207);
lean_ctor_set(x_221, 2, x_213);
lean_ctor_set_uint8(x_221, sizeof(void*)*3, x_208);
lean_ctor_set_uint8(x_221, sizeof(void*)*3 + 1, x_209);
lean_ctor_set(x_211, 0, x_221);
return x_211;
}
}
else
{
lean_dec(x_213);
lean_ctor_set(x_211, 0, x_2);
return x_211;
}
}
else
{
lean_object* x_222; size_t x_223; size_t x_224; uint8_t x_225; 
x_222 = lean_ctor_get(x_211, 0);
lean_inc(x_222);
lean_dec(x_211);
x_223 = lean_ptr_addr(x_210);
x_224 = lean_ptr_addr(x_222);
x_225 = lean_usize_dec_eq(x_223, x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_inc(x_207);
lean_inc(x_206);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_226 = x_2;
} else {
 lean_dec_ref(x_2);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(10, 3, 2);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_206);
lean_ctor_set(x_227, 1, x_207);
lean_ctor_set(x_227, 2, x_222);
lean_ctor_set_uint8(x_227, sizeof(void*)*3, x_208);
lean_ctor_set_uint8(x_227, sizeof(void*)*3 + 1, x_209);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_227);
return x_228;
}
else
{
lean_object* x_229; 
lean_dec(x_222);
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_2);
return x_229;
}
}
}
else
{
lean_dec_ref(x_2);
return x_211;
}
}
default: 
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_2);
return x_230;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 4);
x_13 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(x_3, x_9);
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_14; 
lean_inc_ref(x_12);
lean_inc(x_9);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_2, 4);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec_ref(x_13);
x_21 = lean_st_ref_take(x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_ctor_set(x_2, 1, x_20);
lean_inc_ref(x_2);
x_24 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_1, x_23, x_2);
lean_ctor_set(x_21, 0, x_24);
x_25 = lean_st_ref_set(x_5, x_21);
x_26 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_2, x_11, x_10, x_27, x_5);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec_ref(x_2);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_ctor_set(x_2, 1, x_20);
lean_inc_ref(x_2);
x_34 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_1, x_32, x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_st_ref_set(x_5, x_35);
x_37 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_2, x_11, x_10, x_38, x_5);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_2);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_13, 0);
lean_inc(x_43);
lean_dec_ref(x_13);
x_44 = lean_st_ref_take(x_5);
x_45 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_10);
lean_ctor_set(x_48, 3, x_11);
lean_ctor_set(x_48, 4, x_12);
lean_inc_ref(x_48);
x_49 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_1, x_45, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
x_51 = lean_st_ref_set(x_5, x_50);
x_52 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_48, x_11, x_10, x_53, x_5);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_48);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_13);
lean_inc_ref(x_12);
x_58 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_2, x_11, x_10, x_59, x_5);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_2);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_applyRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(x_1, x_2, x_3, x_4, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_apply_6(x_1, x_9, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_free_object(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_apply_6(x_1, x_18, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_20);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_25 = x_19;
} else {
 lean_dec_ref(x_19);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_1, x_3, x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_17 = lean_ctor_get(x_10, 3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(x_1, x_3, x_18, x_17, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_box(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed), 8, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_3);
x_23 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(x_22, x_12, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_10, 3, x_20);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_10, 3, x_20);
lean_ctor_set(x_2, 1, x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_free_object(x_10);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_2);
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_free_object(x_10);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
x_38 = lean_ctor_get(x_10, 2);
x_39 = lean_ctor_get(x_10, 3);
x_40 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(x_1, x_3, x_41, x_39, x_5);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_box(x_1);
x_45 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed), 8, 2);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_3);
x_46 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(x_45, x_34, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_37);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_40);
lean_ctor_set(x_2, 1, x_47);
lean_ctor_set(x_2, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_2);
lean_dec(x_35);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_55 = x_42;
} else {
 lean_dec_ref(x_42);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = lean_ctor_get(x_2, 1);
x_59 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_2);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 2);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_57, 3);
lean_inc_ref(x_64);
x_65 = lean_ctor_get_uint8(x_57, sizeof(void*)*4);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
x_67 = lean_unsigned_to_nat(0u);
x_68 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(x_1, x_3, x_67, x_64, x_5);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_box(x_1);
x_71 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed), 8, 2);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_3);
x_72 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(x_71, x_58, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_75 = lean_alloc_ctor(0, 4, 1);
} else {
 x_75 = x_66;
}
lean_ctor_set(x_75, 0, x_61);
lean_ctor_set(x_75, 1, x_62);
lean_ctor_set(x_75, 2, x_63);
lean_ctor_set(x_75, 3, x_69);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_65);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set(x_76, 2, x_60);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_59);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_69);
lean_dec(x_66);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_66);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_58);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_82 = x_68;
} else {
 lean_dec_ref(x_68);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_2);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_applyRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Decl_applyRenaming(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
