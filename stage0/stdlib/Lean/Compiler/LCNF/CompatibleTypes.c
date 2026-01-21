// Lean compiler output
// Module: Lean.Compiler.LCNF.CompatibleTypes
// Imports: public import Lean.Compiler.LCNF.InferType
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Level_isEquiv(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_10; uint8_t x_43; 
x_43 = l_Lean_Expr_isErased(x_1);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Expr_isErased(x_2);
x_10 = x_44;
goto block_42;
}
else
{
x_10 = x_43;
goto block_42;
}
block_9:
{
uint8_t x_7; 
x_7 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_3, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_7;
}
else
{
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
block_42:
{
uint8_t x_11; 
x_11 = 1;
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc_ref(x_1);
x_12 = l_Lean_Expr_headBeta(x_1);
lean_inc_ref(x_2);
x_13 = l_Lean_Expr_headBeta(x_2);
x_14 = lean_expr_eqv(x_1, x_12);
if (x_14 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = lean_expr_eqv(x_2, x_13);
if (x_16 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_18 = lean_expr_eqv(x_1, x_2);
if (x_18 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_2);
x_23 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_19, x_21);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_20);
return x_23;
}
else
{
x_1 = x_20;
x_2 = x_22;
goto _start;
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_2);
x_3 = x_25;
x_4 = x_26;
x_5 = x_27;
x_6 = x_28;
goto block_9;
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_30);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_32);
lean_dec_ref(x_2);
x_3 = x_29;
x_4 = x_30;
x_5 = x_31;
x_6 = x_32;
goto block_9;
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec_ref(x_1);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec_ref(x_2);
x_35 = l_Lean_Level_isEquiv(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
return x_35;
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec_ref(x_2);
x_40 = lean_name_eq(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec(x_37);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
return x_41;
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
default: 
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_1);
x_8 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_headBeta(x_10);
if (lean_obj_tag(x_11) == 7)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec_ref(x_11);
x_15 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0;
x_16 = l_Lean_Expr_app___override(x_1, x_15);
x_17 = l_Lean_Expr_lam___override(x_12, x_13, x_16, x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_19 = lean_box(0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_Lean_Expr_headBeta(x_20);
if (lean_obj_tag(x_21) == 7)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 8);
lean_dec_ref(x_21);
x_25 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0;
x_26 = l_Lean_Expr_app___override(x_1, x_25);
x_27 = l_Lean_Expr_lam___override(x_22, x_23, x_26, x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_21);
lean_dec_ref(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_st_ref_take(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 2);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Name_num___override(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_8, 2, x_4);
x_14 = lean_st_ref_set(x_1, x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Name_num___override(x_6, x_7);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_7, x_25);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_26);
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_18);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_20);
lean_ctor_set(x_27, 6, x_21);
lean_ctor_set(x_27, 7, x_22);
lean_ctor_set(x_27, 8, x_23);
x_28 = lean_st_ref_set(x_1, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_st_ref_take(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 3);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_32, 4);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_32, 5);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_32, 6);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_32, 7);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_32, 8);
lean_inc_ref(x_40);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 lean_ctor_release(x_32, 5);
 lean_ctor_release(x_32, 6);
 lean_ctor_release(x_32, 7);
 lean_ctor_release(x_32, 8);
 x_41 = x_32;
} else {
 lean_dec_ref(x_32);
 x_41 = lean_box(0);
}
lean_inc(x_31);
lean_inc(x_30);
x_42 = l_Lean_Name_num___override(x_30, x_31);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_31, x_43);
lean_dec(x_31);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 9, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_34);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_35);
lean_ctor_set(x_46, 4, x_36);
lean_ctor_set(x_46, 5, x_37);
lean_ctor_set(x_46, 6, x_38);
lean_ctor_set(x_46, 7, x_39);
lean_ctor_set(x_46, 8, x_40);
x_47 = lean_st_ref_set(x_1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_42);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_76; uint8_t x_139; 
x_139 = l_Lean_Expr_isErased(x_1);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = l_Lean_Expr_isErased(x_2);
x_76 = x_140;
goto block_138;
}
else
{
x_76 = x_139;
goto block_138;
}
block_35:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_10);
x_21 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_10, x_13, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_21;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_21);
x_24 = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_25);
x_26 = l_Lean_Expr_fvar___override(x_25);
x_27 = 0;
x_28 = l_Lean_LocalContext_mkLocalDecl(x_15, x_25, x_9, x_10, x_12, x_27);
x_29 = lean_expr_instantiate1(x_11, x_26);
lean_dec_ref(x_11);
x_30 = lean_expr_instantiate1(x_14, x_26);
lean_dec_ref(x_26);
lean_dec_ref(x_14);
x_1 = x_29;
x_2 = x_30;
x_3 = x_28;
x_4 = x_16;
x_5 = x_17;
x_6 = x_18;
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_21;
}
}
block_75:
{
uint8_t x_43; 
x_43 = l_Lean_Expr_isLambda(x_1);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Expr_isLambda(x_2);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; 
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
x_47 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_50; 
lean_free_object(x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_1 = x_50;
x_3 = x_37;
x_4 = x_38;
x_5 = x_39;
x_6 = x_40;
x_7 = x_41;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_49);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_2);
x_52 = lean_box(x_43);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
lean_dec(x_47);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_1 = x_54;
x_3 = x_37;
x_4 = x_38;
x_5 = x_39;
x_6 = x_40;
x_7 = x_41;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_2);
x_56 = lean_box(x_43);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_2);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
lean_dec(x_47);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; 
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
x_61 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; 
lean_free_object(x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_2 = x_64;
x_3 = x_37;
x_4 = x_38;
x_5 = x_39;
x_6 = x_40;
x_7 = x_41;
goto _start;
}
else
{
lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_1);
x_66 = lean_box(x_36);
lean_ctor_set(x_61, 0, x_66);
return x_61;
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
lean_dec(x_61);
if (lean_obj_tag(x_67) == 1)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_2 = x_68;
x_3 = x_37;
x_4 = x_38;
x_5 = x_39;
x_6 = x_40;
x_7 = x_41;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_1);
x_70 = lean_box(x_36);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_61);
if (x_72 == 0)
{
return x_61;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
lean_dec(x_61);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
block_138:
{
uint8_t x_77; 
x_77 = 1;
if (x_76 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_inc_ref(x_1);
x_78 = l_Lean_Expr_headBeta(x_1);
lean_inc_ref(x_2);
x_79 = l_Lean_Expr_headBeta(x_2);
x_80 = lean_expr_eqv(x_1, x_78);
if (x_80 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_78;
x_2 = x_79;
goto _start;
}
else
{
uint8_t x_82; 
x_82 = lean_expr_eqv(x_2, x_79);
if (x_82 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_78;
x_2 = x_79;
goto _start;
}
else
{
uint8_t x_84; 
lean_dec_ref(x_79);
lean_dec_ref(x_78);
x_84 = lean_expr_eqv(x_1, x_2);
if (x_84 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_86);
lean_dec_ref(x_1);
x_87 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_88);
lean_dec_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_89 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_85, x_87, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_dec_ref(x_88);
lean_dec_ref(x_86);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_89;
}
else
{
lean_dec_ref(x_89);
x_1 = x_86;
x_2 = x_88;
goto _start;
}
}
else
{
lean_dec_ref(x_88);
lean_dec_ref(x_86);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_89;
}
}
case 10:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_93);
lean_dec_ref(x_2);
x_2 = x_93;
goto _start;
}
default: 
{
x_36 = x_84;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = lean_box(0);
goto block_75;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_97);
x_98 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_99 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_100);
lean_dec_ref(x_2);
x_9 = x_95;
x_10 = x_96;
x_11 = x_97;
x_12 = x_98;
x_13 = x_99;
x_14 = x_100;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = lean_box(0);
goto block_35;
}
case 10:
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_101);
lean_dec_ref(x_2);
x_2 = x_101;
goto _start;
}
default: 
{
x_36 = x_84;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = lean_box(0);
goto block_75;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_105);
x_106 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_107 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_108);
lean_dec_ref(x_2);
x_9 = x_103;
x_10 = x_104;
x_11 = x_105;
x_12 = x_106;
x_13 = x_107;
x_14 = x_108;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = lean_box(0);
goto block_35;
}
case 10:
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_109);
lean_dec_ref(x_2);
x_2 = x_109;
goto _start;
}
default: 
{
x_36 = x_84;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = lean_box(0);
goto block_75;
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
lean_dec_ref(x_1);
x_112 = lean_ctor_get(x_2, 0);
lean_inc(x_112);
lean_dec_ref(x_2);
x_113 = l_Lean_Level_isEquiv(x_111, x_112);
lean_dec(x_112);
lean_dec(x_111);
x_114 = lean_box(x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
case 10:
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_116);
lean_dec_ref(x_2);
x_2 = x_116;
goto _start;
}
default: 
{
x_36 = x_84;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = lean_box(0);
goto block_75;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 1);
lean_inc(x_119);
lean_dec_ref(x_1);
x_120 = lean_ctor_get(x_2, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_2, 1);
lean_inc(x_121);
lean_dec_ref(x_2);
x_122 = lean_name_eq(x_118, x_120);
lean_dec(x_120);
lean_dec(x_118);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_121);
lean_dec(x_119);
x_123 = lean_box(x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
else
{
uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_125 = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_119, x_121);
lean_dec(x_121);
lean_dec(x_119);
x_126 = lean_box(x_125);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
case 10:
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_128);
lean_dec_ref(x_2);
x_2 = x_128;
goto _start;
}
default: 
{
x_36 = x_84;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = lean_box(0);
goto block_75;
}
}
}
case 10:
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_130);
lean_dec_ref(x_1);
x_1 = x_130;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_132);
lean_dec_ref(x_2);
x_2 = x_132;
goto _start;
}
else
{
x_36 = x_84;
x_37 = x_3;
x_38 = x_4;
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = lean_box(0);
goto block_75;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_134 = lean_box(x_77);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_136 = lean_box(x_77);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_compatibleTypes(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0 = _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
