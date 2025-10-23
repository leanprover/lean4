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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object* x_1, lean_object* x_2) {
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
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec_ref(x_2);
x_21 = l_Lean_Level_isEquiv(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
return x_21;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec_ref(x_2);
x_26 = lean_name_eq(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_23);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
return x_27;
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_2);
x_32 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_28, x_30);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_29);
return x_32;
}
else
{
x_1 = x_29;
x_2 = x_31;
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
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_35);
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_37);
lean_dec_ref(x_2);
x_3 = x_34;
x_4 = x_35;
x_5 = x_36;
x_6 = x_37;
goto block_9;
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_39);
lean_dec_ref(x_1);
x_40 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_41);
lean_dec_ref(x_2);
x_3 = x_38;
x_4 = x_39;
x_5 = x_40;
x_6 = x_41;
goto block_9;
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
LEAN_EXPORT lean_object* l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
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
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_inc(x_6);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_8, 2, x_4);
x_13 = lean_st_ref_set(x_1, x_8);
x_14 = l_Lean_Name_num___override(x_6, x_7);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
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
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_7, x_24);
lean_inc(x_6);
lean_ctor_set(x_4, 1, x_25);
x_26 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 3, x_18);
lean_ctor_set(x_26, 4, x_19);
lean_ctor_set(x_26, 5, x_20);
lean_ctor_set(x_26, 6, x_21);
lean_ctor_set(x_26, 7, x_22);
lean_ctor_set(x_26, 8, x_23);
x_27 = lean_st_ref_set(x_1, x_26);
x_28 = l_Lean_Name_num___override(x_6, x_7);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
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
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_31, x_42);
lean_inc(x_30);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 9, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_38);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
x_46 = lean_st_ref_set(x_1, x_45);
x_47 = l_Lean_Name_num___override(x_30, x_31);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_73; uint8_t x_136; 
x_136 = l_Lean_Expr_isErased(x_1);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = l_Lean_Expr_isErased(x_2);
x_73 = x_137;
goto block_135;
}
else
{
x_73 = x_136;
goto block_135;
}
block_32:
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_21);
x_24 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(x_15, x_16, x_17, x_18, x_19);
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
block_72:
{
uint8_t x_40; 
x_40 = l_Lean_Expr_isLambda(x_1);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Expr_isLambda(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; 
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc_ref(x_34);
x_44 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_2);
x_47 = lean_box(x_40);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; 
lean_free_object(x_44);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec_ref(x_46);
x_1 = x_48;
x_3 = x_34;
x_4 = x_35;
x_5 = x_36;
x_6 = x_37;
x_7 = x_38;
goto _start;
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_2);
x_51 = lean_box(x_40);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec_ref(x_50);
x_1 = x_53;
x_3 = x_34;
x_4 = x_35;
x_5 = x_36;
x_6 = x_37;
x_7 = x_38;
goto _start;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
return x_44;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
lean_dec(x_44);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; 
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc_ref(x_34);
x_58 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_1);
x_61 = lean_box(x_33);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; 
lean_free_object(x_58);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec_ref(x_60);
x_2 = x_62;
x_3 = x_34;
x_4 = x_35;
x_5 = x_36;
x_6 = x_37;
x_7 = x_38;
goto _start;
}
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_1);
x_65 = lean_box(x_33);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec_ref(x_64);
x_2 = x_67;
x_3 = x_34;
x_4 = x_35;
x_5 = x_36;
x_6 = x_37;
x_7 = x_38;
goto _start;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
return x_58;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_58, 0);
lean_inc(x_70);
lean_dec(x_58);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
block_135:
{
uint8_t x_74; 
x_74 = 1;
if (x_73 == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_inc_ref(x_1);
x_75 = l_Lean_Expr_headBeta(x_1);
lean_inc_ref(x_2);
x_76 = l_Lean_Expr_headBeta(x_2);
x_77 = lean_expr_eqv(x_1, x_75);
if (x_77 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_75;
x_2 = x_76;
goto _start;
}
else
{
uint8_t x_79; 
x_79 = lean_expr_eqv(x_2, x_76);
if (x_79 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_75;
x_2 = x_76;
goto _start;
}
else
{
uint8_t x_81; 
lean_dec_ref(x_76);
lean_dec_ref(x_75);
x_81 = lean_expr_eqv(x_1, x_2);
if (x_81 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
lean_dec_ref(x_1);
x_83 = lean_ctor_get(x_2, 0);
lean_inc(x_83);
lean_dec_ref(x_2);
x_84 = l_Lean_Level_isEquiv(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
x_85 = lean_box(x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
case 10:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_87);
lean_dec_ref(x_2);
x_2 = x_87;
goto _start;
}
default: 
{
x_33 = x_81;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_6;
x_38 = x_7;
x_39 = lean_box(0);
goto block_72;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 1);
lean_inc(x_90);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
lean_dec_ref(x_2);
x_93 = lean_name_eq(x_89, x_91);
lean_dec(x_91);
lean_dec(x_89);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_92);
lean_dec(x_90);
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
else
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_96 = l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_90, x_92);
lean_dec(x_92);
lean_dec(x_90);
x_97 = lean_box(x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
case 10:
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_99);
lean_dec_ref(x_2);
x_2 = x_99;
goto _start;
}
default: 
{
x_33 = x_81;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_6;
x_38 = x_7;
x_39 = lean_box(0);
goto block_72;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_102);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_104);
lean_dec_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_105 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_101, x_103, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_105;
}
else
{
lean_dec_ref(x_105);
x_1 = x_102;
x_2 = x_104;
goto _start;
}
}
else
{
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_105;
}
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
x_33 = x_81;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_6;
x_38 = x_7;
x_39 = lean_box(0);
goto block_72;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_113);
x_114 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_115 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_116);
lean_dec_ref(x_2);
x_9 = x_111;
x_10 = x_112;
x_11 = x_113;
x_12 = x_114;
x_13 = x_115;
x_14 = x_116;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = lean_box(0);
goto block_32;
}
case 10:
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_117);
lean_dec_ref(x_2);
x_2 = x_117;
goto _start;
}
default: 
{
x_33 = x_81;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_6;
x_38 = x_7;
x_39 = lean_box(0);
goto block_72;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_1, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_121);
x_122 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_124);
lean_dec_ref(x_2);
x_9 = x_119;
x_10 = x_120;
x_11 = x_121;
x_12 = x_122;
x_13 = x_123;
x_14 = x_124;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = lean_box(0);
goto block_32;
}
case 10:
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_125);
lean_dec_ref(x_2);
x_2 = x_125;
goto _start;
}
default: 
{
x_33 = x_81;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_6;
x_38 = x_7;
x_39 = lean_box(0);
goto block_72;
}
}
}
case 10:
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_127);
lean_dec_ref(x_1);
x_1 = x_127;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_129);
lean_dec_ref(x_2);
x_2 = x_129;
goto _start;
}
else
{
x_33 = x_81;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_6;
x_38 = x_7;
x_39 = lean_box(0);
goto block_72;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_131 = lean_box(x_74);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_133 = lean_box(x_74);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
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
