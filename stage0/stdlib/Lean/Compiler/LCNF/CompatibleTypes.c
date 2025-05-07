// Lean compiler output
// Module: Lean.Compiler.LCNF.CompatibleTypes
// Imports: Lean.Compiler.LCNF.InferType
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
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isErased(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isErased(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_6 = l_Lean_Expr_headBeta(x_2);
x_7 = lean_expr_eqv(x_1, x_5);
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = lean_expr_eqv(x_2, x_6);
if (x_9 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_expr_eqv(x_1, x_2);
if (x_11 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Level_isEquiv(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = 0;
return x_15;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_19);
lean_dec(x_17);
x_21 = 0;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_24, x_26);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_27);
lean_dec(x_25);
x_29 = 0;
return x_29;
}
else
{
x_1 = x_25;
x_2 = x_27;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = 0;
return x_31;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_32, x_34);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_35);
lean_dec(x_33);
x_37 = 0;
return x_37;
}
else
{
x_1 = x_33;
x_2 = x_35;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = 0;
return x_39;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
lean_dec(x_2);
x_44 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_40, x_42);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_43);
lean_dec(x_41);
x_45 = 0;
return x_45;
}
else
{
x_1 = x_41;
x_2 = x_43;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = 0;
return x_47;
}
}
default: 
{
uint8_t x_48; 
lean_dec(x_2);
lean_dec(x_1);
x_48 = 0;
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = 1;
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = 1;
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = 1;
return x_51;
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
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
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
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_15 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1;
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
lean_dec(x_11);
lean_dec(x_1);
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
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_22, sizeof(void*)*3 + 8);
lean_dec(x_22);
x_26 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1;
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
lean_dec(x_22);
lean_dec(x_1);
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Expr_fvar___override(x_14);
x_17 = 0;
x_18 = l_Lean_LocalContext_mkLocalDecl(x_7, x_14, x_1, x_2, x_3, x_17);
x_19 = lean_expr_instantiate1(x_4, x_16);
x_20 = lean_expr_instantiate1(x_5, x_16);
lean_dec(x_16);
x_21 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_19, x_20, x_18, x_8, x_9, x_10, x_11, x_15);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isErased(x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isErased(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_12 = l_Lean_Expr_headBeta(x_2);
x_13 = lean_expr_eqv(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = lean_expr_eqv(x_2, x_12);
if (x_15 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_expr_eqv(x_1, x_2);
if (x_17 == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_Level_isEquiv(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
case 10:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_2 = x_23;
goto _start;
}
default: 
{
uint8_t x_25; 
x_25 = l_Lean_Expr_isLambda(x_1);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_isLambda(x_2);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
else
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_1 = x_41;
x_8 = x_40;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_47 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = 0;
x_52 = lean_box(x_51);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = 0;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
lean_dec(x_48);
x_2 = x_58;
x_8 = x_57;
goto _start;
}
}
else
{
uint8_t x_60; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
lean_dec(x_1);
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
lean_dec(x_2);
x_68 = lean_name_eq(x_64, x_66);
lean_dec(x_66);
lean_dec(x_64);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_65);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_8);
return x_71;
}
else
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_72 = l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(x_65, x_67);
lean_dec(x_67);
lean_dec(x_65);
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_8);
return x_74;
}
}
case 10:
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_dec(x_2);
x_2 = x_75;
goto _start;
}
default: 
{
uint8_t x_77; 
x_77 = l_Lean_Expr_isLambda(x_1);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Expr_isLambda(x_2);
if (x_78 == 0)
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = 0;
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_8);
return x_81;
}
else
{
lean_object* x_82; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_82 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
x_86 = 0;
x_87 = lean_box(x_86);
lean_ctor_set(x_82, 0, x_87);
return x_82;
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = 0;
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_dec(x_82);
x_93 = lean_ctor_get(x_83, 0);
lean_inc(x_93);
lean_dec(x_83);
x_1 = x_93;
x_8 = x_92;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
return x_82;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_82);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_99 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_99, 0);
lean_dec(x_102);
x_103 = 0;
x_104 = lean_box(x_103);
lean_ctor_set(x_99, 0, x_104);
return x_99;
}
else
{
lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
x_106 = 0;
x_107 = lean_box(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_99, 1);
lean_inc(x_109);
lean_dec(x_99);
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
lean_dec(x_100);
x_2 = x_110;
x_8 = x_109;
goto _start;
}
}
else
{
uint8_t x_112; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_99);
if (x_112 == 0)
{
return x_99;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_99, 0);
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_99);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_1, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_1, 1);
lean_inc(x_117);
lean_dec(x_1);
x_118 = lean_ctor_get(x_2, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_120 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_116, x_118, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
uint8_t x_123; 
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_120);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_120, 0);
lean_dec(x_124);
return x_120;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
else
{
lean_object* x_127; 
lean_dec(x_121);
x_127 = lean_ctor_get(x_120, 1);
lean_inc(x_127);
lean_dec(x_120);
x_1 = x_117;
x_2 = x_119;
x_8 = x_127;
goto _start;
}
}
else
{
uint8_t x_129; 
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_120);
if (x_129 == 0)
{
return x_120;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_120, 0);
x_131 = lean_ctor_get(x_120, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_120);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
case 10:
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
lean_dec(x_2);
x_2 = x_133;
goto _start;
}
default: 
{
uint8_t x_135; 
x_135 = l_Lean_Expr_isLambda(x_1);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = l_Lean_Expr_isLambda(x_2);
if (x_136 == 0)
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = 0;
x_138 = lean_box(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_8);
return x_139;
}
else
{
lean_object* x_140; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_140 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_140);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_140, 0);
lean_dec(x_143);
x_144 = 0;
x_145 = lean_box(x_144);
lean_ctor_set(x_140, 0, x_145);
return x_140;
}
else
{
lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
x_147 = 0;
x_148 = lean_box(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_140, 1);
lean_inc(x_150);
lean_dec(x_140);
x_151 = lean_ctor_get(x_141, 0);
lean_inc(x_151);
lean_dec(x_141);
x_1 = x_151;
x_8 = x_150;
goto _start;
}
}
else
{
uint8_t x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_140);
if (x_153 == 0)
{
return x_140;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_140, 0);
x_155 = lean_ctor_get(x_140, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_140);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
lean_object* x_157; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_157 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
x_161 = 0;
x_162 = lean_box(x_161);
lean_ctor_set(x_157, 0, x_162);
return x_157;
}
else
{
lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = 0;
x_165 = lean_box(x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_157, 1);
lean_inc(x_167);
lean_dec(x_157);
x_168 = lean_ctor_get(x_158, 0);
lean_inc(x_168);
lean_dec(x_158);
x_2 = x_168;
x_8 = x_167;
goto _start;
}
}
else
{
uint8_t x_170; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_157);
if (x_170 == 0)
{
return x_157;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_157, 0);
x_172 = lean_ctor_get(x_157, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_157);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_1, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_1, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_1, 2);
lean_inc(x_176);
x_177 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_178 = lean_ctor_get(x_2, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_2, 2);
lean_inc(x_179);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_175);
x_180 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_175, x_178, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
uint8_t x_183; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = !lean_is_exclusive(x_180);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_180, 0);
lean_dec(x_184);
x_185 = 0;
x_186 = lean_box(x_185);
lean_ctor_set(x_180, 0, x_186);
return x_180;
}
else
{
lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_180, 1);
lean_inc(x_187);
lean_dec(x_180);
x_188 = 0;
x_189 = lean_box(x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_180, 1);
lean_inc(x_191);
lean_dec(x_180);
x_192 = lean_box(0);
x_193 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_174, x_175, x_177, x_176, x_179, x_192, x_3, x_4, x_5, x_6, x_7, x_191);
lean_dec(x_179);
lean_dec(x_176);
return x_193;
}
}
else
{
uint8_t x_194; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = !lean_is_exclusive(x_180);
if (x_194 == 0)
{
return x_180;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_180, 0);
x_196 = lean_ctor_get(x_180, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_180);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
case 10:
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_2, 1);
lean_inc(x_198);
lean_dec(x_2);
x_2 = x_198;
goto _start;
}
default: 
{
uint8_t x_200; 
x_200 = l_Lean_Expr_isLambda(x_1);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = l_Lean_Expr_isLambda(x_2);
if (x_201 == 0)
{
uint8_t x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = 0;
x_203 = lean_box(x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
else
{
lean_object* x_205; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_205 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = !lean_is_exclusive(x_205);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_205, 0);
lean_dec(x_208);
x_209 = 0;
x_210 = lean_box(x_209);
lean_ctor_set(x_205, 0, x_210);
return x_205;
}
else
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_205, 1);
lean_inc(x_211);
lean_dec(x_205);
x_212 = 0;
x_213 = lean_box(x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_211);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_205, 1);
lean_inc(x_215);
lean_dec(x_205);
x_216 = lean_ctor_get(x_206, 0);
lean_inc(x_216);
lean_dec(x_206);
x_1 = x_216;
x_8 = x_215;
goto _start;
}
}
else
{
uint8_t x_218; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_218 = !lean_is_exclusive(x_205);
if (x_218 == 0)
{
return x_205;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_205, 0);
x_220 = lean_ctor_get(x_205, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_205);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
}
else
{
lean_object* x_222; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_222 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_222);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_222, 0);
lean_dec(x_225);
x_226 = 0;
x_227 = lean_box(x_226);
lean_ctor_set(x_222, 0, x_227);
return x_222;
}
else
{
lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_222, 1);
lean_inc(x_228);
lean_dec(x_222);
x_229 = 0;
x_230 = lean_box(x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_228);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_222, 1);
lean_inc(x_232);
lean_dec(x_222);
x_233 = lean_ctor_get(x_223, 0);
lean_inc(x_233);
lean_dec(x_223);
x_2 = x_233;
x_8 = x_232;
goto _start;
}
}
else
{
uint8_t x_235; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_222);
if (x_235 == 0)
{
return x_222;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_222, 0);
x_237 = lean_ctor_get(x_222, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_222);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_239 = lean_ctor_get(x_1, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_1, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_1, 2);
lean_inc(x_241);
x_242 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_243 = lean_ctor_get(x_2, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_2, 2);
lean_inc(x_244);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_240);
x_245 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_240, x_243, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; uint8_t x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_unbox(x_246);
lean_dec(x_246);
if (x_247 == 0)
{
uint8_t x_248; 
lean_dec(x_244);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_248 = !lean_is_exclusive(x_245);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_245, 0);
lean_dec(x_249);
x_250 = 0;
x_251 = lean_box(x_250);
lean_ctor_set(x_245, 0, x_251);
return x_245;
}
else
{
lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_245, 1);
lean_inc(x_252);
lean_dec(x_245);
x_253 = 0;
x_254 = lean_box(x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_245, 1);
lean_inc(x_256);
lean_dec(x_245);
x_257 = lean_box(0);
x_258 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_239, x_240, x_242, x_241, x_244, x_257, x_3, x_4, x_5, x_6, x_7, x_256);
lean_dec(x_244);
lean_dec(x_241);
return x_258;
}
}
else
{
uint8_t x_259; 
lean_dec(x_244);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_259 = !lean_is_exclusive(x_245);
if (x_259 == 0)
{
return x_245;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_245, 0);
x_261 = lean_ctor_get(x_245, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_245);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
case 10:
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_2, 1);
lean_inc(x_263);
lean_dec(x_2);
x_2 = x_263;
goto _start;
}
default: 
{
uint8_t x_265; 
x_265 = l_Lean_Expr_isLambda(x_1);
if (x_265 == 0)
{
uint8_t x_266; 
x_266 = l_Lean_Expr_isLambda(x_2);
if (x_266 == 0)
{
uint8_t x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = 0;
x_268 = lean_box(x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_8);
return x_269;
}
else
{
lean_object* x_270; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_270 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_272 = !lean_is_exclusive(x_270);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_270, 0);
lean_dec(x_273);
x_274 = 0;
x_275 = lean_box(x_274);
lean_ctor_set(x_270, 0, x_275);
return x_270;
}
else
{
lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_270, 1);
lean_inc(x_276);
lean_dec(x_270);
x_277 = 0;
x_278 = lean_box(x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_276);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_270, 1);
lean_inc(x_280);
lean_dec(x_270);
x_281 = lean_ctor_get(x_271, 0);
lean_inc(x_281);
lean_dec(x_271);
x_1 = x_281;
x_8 = x_280;
goto _start;
}
}
else
{
uint8_t x_283; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_283 = !lean_is_exclusive(x_270);
if (x_283 == 0)
{
return x_270;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_270, 0);
x_285 = lean_ctor_get(x_270, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_270);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
else
{
lean_object* x_287; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_287 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_287);
if (x_289 == 0)
{
lean_object* x_290; uint8_t x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_287, 0);
lean_dec(x_290);
x_291 = 0;
x_292 = lean_box(x_291);
lean_ctor_set(x_287, 0, x_292);
return x_287;
}
else
{
lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; 
x_293 = lean_ctor_get(x_287, 1);
lean_inc(x_293);
lean_dec(x_287);
x_294 = 0;
x_295 = lean_box(x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_293);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_287, 1);
lean_inc(x_297);
lean_dec(x_287);
x_298 = lean_ctor_get(x_288, 0);
lean_inc(x_298);
lean_dec(x_288);
x_2 = x_298;
x_8 = x_297;
goto _start;
}
}
else
{
uint8_t x_300; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_287);
if (x_300 == 0)
{
return x_287;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_287, 0);
x_302 = lean_ctor_get(x_287, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_287);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
}
}
}
case 10:
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_1, 1);
lean_inc(x_304);
lean_dec(x_1);
x_1 = x_304;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_2, 1);
lean_inc(x_306);
lean_dec(x_2);
x_2 = x_306;
goto _start;
}
else
{
uint8_t x_308; 
x_308 = l_Lean_Expr_isLambda(x_1);
if (x_308 == 0)
{
uint8_t x_309; 
x_309 = l_Lean_Expr_isLambda(x_2);
if (x_309 == 0)
{
uint8_t x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_310 = 0;
x_311 = lean_box(x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_8);
return x_312;
}
else
{
lean_object* x_313; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_313 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
if (lean_obj_tag(x_314) == 0)
{
uint8_t x_315; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_315 = !lean_is_exclusive(x_313);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_313, 0);
lean_dec(x_316);
x_317 = 0;
x_318 = lean_box(x_317);
lean_ctor_set(x_313, 0, x_318);
return x_313;
}
else
{
lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; 
x_319 = lean_ctor_get(x_313, 1);
lean_inc(x_319);
lean_dec(x_313);
x_320 = 0;
x_321 = lean_box(x_320);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_319);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_313, 1);
lean_inc(x_323);
lean_dec(x_313);
x_324 = lean_ctor_get(x_314, 0);
lean_inc(x_324);
lean_dec(x_314);
x_1 = x_324;
x_8 = x_323;
goto _start;
}
}
else
{
uint8_t x_326; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_326 = !lean_is_exclusive(x_313);
if (x_326 == 0)
{
return x_313;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_313, 0);
x_328 = lean_ctor_get(x_313, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_313);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
}
else
{
lean_object* x_330; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_330 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_obj_tag(x_331) == 0)
{
uint8_t x_332; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_332 = !lean_is_exclusive(x_330);
if (x_332 == 0)
{
lean_object* x_333; uint8_t x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_330, 0);
lean_dec(x_333);
x_334 = 0;
x_335 = lean_box(x_334);
lean_ctor_set(x_330, 0, x_335);
return x_330;
}
else
{
lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; 
x_336 = lean_ctor_get(x_330, 1);
lean_inc(x_336);
lean_dec(x_330);
x_337 = 0;
x_338 = lean_box(x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_336);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_330, 1);
lean_inc(x_340);
lean_dec(x_330);
x_341 = lean_ctor_get(x_331, 0);
lean_inc(x_341);
lean_dec(x_331);
x_2 = x_341;
x_8 = x_340;
goto _start;
}
}
else
{
uint8_t x_343; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_343 = !lean_is_exclusive(x_330);
if (x_343 == 0)
{
return x_330;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_330, 0);
x_345 = lean_ctor_get(x_330, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_330);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
}
}
}
}
else
{
uint8_t x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_347 = 1;
x_348 = lean_box(x_347);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_8);
return x_349;
}
}
}
}
else
{
uint8_t x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_350 = 1;
x_351 = lean_box(x_350);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_8);
return x_352;
}
}
else
{
uint8_t x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_353 = 1;
x_354 = lean_box(x_353);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_8);
return x_355;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_InferType_compatibleTypesFull(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
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
l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_compatibleTypesFull_etaExpand_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
