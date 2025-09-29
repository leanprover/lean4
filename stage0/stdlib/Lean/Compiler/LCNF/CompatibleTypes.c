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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_1);
x_8 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Lean_Expr_headBeta(x_20);
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = lean_ctor_get_uint8(x_22, sizeof(void*)*3 + 8);
lean_dec_ref(x_22);
x_26 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0;
x_27 = l_Lean_Expr_app___override(x_1, x_26);
x_28 = l_Lean_Expr_lam___override(x_23, x_24, x_27, x_25);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_22);
lean_dec_ref(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_st_ref_take(x_1, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_9, x_15);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_11, 2, x_5);
x_17 = lean_st_ref_set(x_1, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Name_num___override(x_8, x_9);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Name_num___override(x_8, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get(x_11, 6);
x_30 = lean_ctor_get(x_11, 7);
x_31 = lean_ctor_get(x_11, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_9, x_32);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_33);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set(x_34, 4, x_27);
lean_ctor_set(x_34, 5, x_28);
lean_ctor_set(x_34, 6, x_29);
lean_ctor_set(x_34, 7, x_30);
lean_ctor_set(x_34, 8, x_31);
x_35 = lean_st_ref_set(x_1, x_34, x_12);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = l_Lean_Name_num___override(x_8, x_9);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_st_ref_take(x_1, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 3);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_43, 4);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_43, 5);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_43, 6);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_43, 7);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_43, 8);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 lean_ctor_release(x_43, 6);
 lean_ctor_release(x_43, 7);
 lean_ctor_release(x_43, 8);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_41, x_54);
lean_inc(x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 9, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_49);
lean_ctor_set(x_57, 6, x_50);
lean_ctor_set(x_57, 7, x_51);
lean_ctor_set(x_57, 8, x_52);
x_58 = lean_st_ref_set(x_1, x_57, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Name_num___override(x_40, x_41);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_77; uint8_t x_141; 
x_141 = l_Lean_Expr_isErased(x_1);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = l_Lean_Expr_isErased(x_2);
x_77 = x_142;
goto block_140;
}
else
{
x_77 = x_141;
goto block_140;
}
block_34:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_10);
x_21 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_10, x_13, x_15, x_16, x_17, x_18, x_19, x_20);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(x_15, x_16, x_17, x_18, x_19, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
lean_inc(x_26);
x_28 = l_Lean_Expr_fvar___override(x_26);
x_29 = 0;
x_30 = l_Lean_LocalContext_mkLocalDecl(x_15, x_26, x_9, x_10, x_12, x_29);
x_31 = lean_expr_instantiate1(x_11, x_28);
lean_dec_ref(x_11);
x_32 = lean_expr_instantiate1(x_14, x_28);
lean_dec_ref(x_28);
lean_dec_ref(x_14);
x_1 = x_31;
x_2 = x_32;
x_3 = x_30;
x_4 = x_16;
x_5 = x_17;
x_6 = x_18;
x_7 = x_19;
x_8 = x_27;
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
block_76:
{
uint8_t x_42; 
x_42 = l_Lean_Expr_isLambda(x_1);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_isLambda(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
lean_object* x_46; 
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_36);
x_46 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_36, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_2);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_box(x_42);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_box(x_42);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec_ref(x_46);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec_ref(x_47);
x_1 = x_55;
x_3 = x_36;
x_4 = x_37;
x_5 = x_38;
x_6 = x_39;
x_7 = x_40;
x_8 = x_54;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_2);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; 
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_36);
x_61 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_36, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = lean_box(x_35);
lean_ctor_set(x_61, 0, x_65);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_box(x_35);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
lean_dec_ref(x_61);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
lean_dec_ref(x_62);
x_2 = x_70;
x_3 = x_36;
x_4 = x_37;
x_5 = x_38;
x_6 = x_39;
x_7 = x_40;
x_8 = x_69;
goto _start;
}
}
else
{
uint8_t x_72; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_61);
if (x_72 == 0)
{
return x_61;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_61, 0);
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_61);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
block_140:
{
uint8_t x_78; 
x_78 = 1;
if (x_77 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_inc_ref(x_1);
x_79 = l_Lean_Expr_headBeta(x_1);
lean_inc_ref(x_2);
x_80 = l_Lean_Expr_headBeta(x_2);
x_81 = lean_expr_eqv(x_1, x_79);
if (x_81 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_79;
x_2 = x_80;
goto _start;
}
else
{
uint8_t x_83; 
x_83 = lean_expr_eqv(x_2, x_80);
if (x_83 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_79;
x_2 = x_80;
goto _start;
}
else
{
uint8_t x_85; 
lean_dec_ref(x_80);
lean_dec_ref(x_79);
x_85 = lean_expr_eqv(x_1, x_2);
if (x_85 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
lean_dec_ref(x_1);
x_87 = lean_ctor_get(x_2, 0);
lean_inc(x_87);
lean_dec_ref(x_2);
x_88 = l_Lean_Level_isEquiv(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
x_89 = lean_box(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_8);
return x_90;
}
case 10:
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_91);
lean_dec_ref(x_2);
x_2 = x_91;
goto _start;
}
default: 
{
x_35 = x_85;
x_36 = x_3;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
x_40 = x_7;
x_41 = x_8;
goto block_76;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
lean_dec_ref(x_1);
x_95 = lean_ctor_get(x_2, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
lean_dec_ref(x_2);
x_97 = lean_name_eq(x_93, x_95);
lean_dec(x_95);
lean_dec(x_93);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_96);
lean_dec(x_94);
x_98 = lean_box(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_8);
return x_99;
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_100 = l_List_isEqv___at___Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_94, x_96);
lean_dec(x_96);
lean_dec(x_94);
x_101 = lean_box(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_8);
return x_102;
}
}
case 10:
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_103);
lean_dec_ref(x_2);
x_2 = x_103;
goto _start;
}
default: 
{
x_35 = x_85;
x_36 = x_3;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
x_40 = x_7;
x_41 = x_8;
goto block_76;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_106);
lean_dec_ref(x_1);
x_107 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_108);
lean_dec_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_109 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_105, x_107, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_dec_ref(x_108);
lean_dec_ref(x_106);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_109;
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec_ref(x_109);
x_1 = x_106;
x_2 = x_108;
x_8 = x_112;
goto _start;
}
}
else
{
lean_dec_ref(x_108);
lean_dec_ref(x_106);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_109;
}
}
case 10:
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_114);
lean_dec_ref(x_2);
x_2 = x_114;
goto _start;
}
default: 
{
x_35 = x_85;
x_36 = x_3;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
x_40 = x_7;
x_41 = x_8;
goto block_76;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_1, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_118);
x_119 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_120 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_121);
lean_dec_ref(x_2);
x_9 = x_116;
x_10 = x_117;
x_11 = x_118;
x_12 = x_119;
x_13 = x_120;
x_14 = x_121;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
goto block_34;
}
case 10:
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_122);
lean_dec_ref(x_2);
x_2 = x_122;
goto _start;
}
default: 
{
x_35 = x_85;
x_36 = x_3;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
x_40 = x_7;
x_41 = x_8;
goto block_76;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_126);
x_127 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_129);
lean_dec_ref(x_2);
x_9 = x_124;
x_10 = x_125;
x_11 = x_126;
x_12 = x_127;
x_13 = x_128;
x_14 = x_129;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
goto block_34;
}
case 10:
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_130);
lean_dec_ref(x_2);
x_2 = x_130;
goto _start;
}
default: 
{
x_35 = x_85;
x_36 = x_3;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
x_40 = x_7;
x_41 = x_8;
goto block_76;
}
}
}
case 10:
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_132);
lean_dec_ref(x_1);
x_1 = x_132;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_134);
lean_dec_ref(x_2);
x_2 = x_134;
goto _start;
}
else
{
x_35 = x_85;
x_36 = x_3;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
x_40 = x_7;
x_41 = x_8;
goto block_76;
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
x_136 = lean_box(x_78);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_8);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_138 = lean_box(x_78);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_8);
return x_139;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_7 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_compatibleTypesFull_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0 = _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
