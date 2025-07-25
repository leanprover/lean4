// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AlphaShareCommon
// Imports: Lean.Meta.Tactic.Grind.ExprPtr
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_shareCommonAlpha(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqAlphaKey___private__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instHashableExprPtr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableAlphaKey;
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqAlphaKey___lam__0(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_shareCommonAlpha_go(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqAlphaKey___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqAlphaKey___private__1(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(lean_object*);
lean_object* l_Lean_Meta_Grind_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableAlphaKey___lam__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash___boxed(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableAlphaKey___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqAlphaKey;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableAlphaKey___private__1___boxed(lean_object*);
uint64_t l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableAlphaKey___lam__0___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
uint64_t x_2; 
x_2 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_1);
return x_2;
}
case 6:
{
uint64_t x_3; 
x_3 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_1);
return x_3;
}
case 7:
{
uint64_t x_4; 
x_4 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_1);
return x_4;
}
case 8:
{
uint64_t x_5; 
x_5 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_1);
return x_5;
}
case 10:
{
uint64_t x_6; 
x_6 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_1);
return x_6;
}
case 11:
{
uint64_t x_7; 
x_7 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_1);
return x_7;
}
default: 
{
uint64_t x_8; 
x_8 = l_Lean_Expr_hash(x_1);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_8);
x_11 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_9);
x_12 = lean_uint64_mix_hash(x_10, x_11);
return x_12;
}
case 6:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_2 = x_13;
x_3 = x_14;
goto block_7;
}
case 7:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_2 = x_15;
x_3 = x_16;
goto block_7;
}
case 8:
{
lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; 
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
x_19 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_17);
x_20 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_18);
x_21 = lean_uint64_mix_hash(x_19, x_20);
return x_21;
}
case 10:
{
lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; 
x_22 = lean_ctor_get(x_1, 1);
x_23 = 13;
x_24 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_22);
x_25 = lean_uint64_mix_hash(x_23, x_24);
return x_25;
}
case 11:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = l_Lean_Name_hash___override(x_26);
x_30 = lean_uint64_of_nat(x_27);
x_31 = lean_uint64_mix_hash(x_29, x_30);
x_32 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_28);
x_33 = lean_uint64_mix_hash(x_31, x_32);
return x_33;
}
default: 
{
uint64_t x_34; 
x_34 = l_Lean_Expr_hash(x_1);
return x_34;
}
}
block_7:
{
uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_4 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_2);
x_5 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_3, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
if (x_7 == 0)
{
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_4, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = 0;
return x_9;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_10, x_12);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
if (x_14 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_11);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_11, x_13);
lean_dec_ref(x_13);
lean_dec_ref(x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = 0;
return x_16;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_20);
lean_dec_ref(x_2);
x_21 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_17, x_19);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_18);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_18, x_20);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = 0;
return x_23;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_25);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_27);
lean_dec_ref(x_2);
x_28 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_24, x_26);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_25);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_25, x_27);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = 0;
return x_30;
}
}
case 10:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_2);
x_35 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_32, x_34);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = l_Lean_KVMap_eqv(x_31, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = 0;
return x_37;
}
}
case 11:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_47; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_40);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_43);
lean_dec_ref(x_2);
x_47 = lean_name_eq(x_38, x_41);
lean_dec(x_41);
lean_dec(x_38);
if (x_47 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
x_44 = x_47;
goto block_46;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_eq(x_39, x_42);
lean_dec(x_42);
lean_dec(x_39);
x_44 = x_48;
goto block_46;
}
block_46:
{
if (x_44 == 0)
{
lean_dec_ref(x_43);
lean_dec_ref(x_40);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_40, x_43);
lean_dec_ref(x_43);
lean_dec_ref(x_40);
return x_45;
}
}
}
else
{
uint8_t x_49; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = 0;
return x_49;
}
}
default: 
{
uint8_t x_50; 
x_50 = lean_expr_eqv(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableAlphaKey___private__1(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableAlphaKey___private__1___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_instHashableAlphaKey___private__1(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableAlphaKey___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instHashableAlphaKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableAlphaKey___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableAlphaKey___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_instHashableAlphaKey___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqAlphaKey___private__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqAlphaKey___private__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_instBEqAlphaKey___private__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqAlphaKey___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqAlphaKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqAlphaKey___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqAlphaKey___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_instBEqAlphaKey___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqExprPtr___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableExprPtr___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqAlphaKey___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableAlphaKey___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_8 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
x_9 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__2;
x_10 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__3;
lean_inc_ref(x_2);
lean_inc_ref(x_6);
x_11 = l_Lean_PersistentHashMap_findEntry_x3f___redArg(x_9, x_10, x_6, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_2);
x_12 = l_Lean_PersistentHashMap_insert___redArg(x_7, x_8, x_5, x_1, x_2);
lean_inc_ref_n(x_2, 2);
x_13 = l_Lean_PersistentHashMap_insert___redArg(x_7, x_8, x_12, x_2, x_2);
x_14 = lean_box(0);
lean_inc_ref(x_2);
x_15 = l_Lean_PersistentHashMap_insert___redArg(x_9, x_10, x_6, x_2, x_14);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec_ref(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_dec(x_20);
lean_inc(x_19);
x_21 = l_Lean_PersistentHashMap_insert___redArg(x_7, x_8, x_5, x_1, x_19);
lean_ctor_set(x_3, 0, x_21);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
lean_inc(x_22);
x_23 = l_Lean_PersistentHashMap_insert___redArg(x_7, x_8, x_5, x_1, x_22);
lean_ctor_set(x_3, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_28 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
x_29 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__2;
x_30 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__3;
lean_inc_ref(x_2);
lean_inc_ref(x_26);
x_31 = l_Lean_PersistentHashMap_findEntry_x3f___redArg(x_29, x_30, x_26, x_2);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc_ref(x_2);
x_32 = l_Lean_PersistentHashMap_insert___redArg(x_27, x_28, x_25, x_1, x_2);
lean_inc_ref_n(x_2, 2);
x_33 = l_Lean_PersistentHashMap_insert___redArg(x_27, x_28, x_32, x_2, x_2);
x_34 = lean_box(0);
lean_inc_ref(x_2);
x_35 = l_Lean_PersistentHashMap_insert___redArg(x_29, x_30, x_26, x_2, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_2);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec_ref(x_31);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
lean_inc(x_39);
x_41 = l_Lean_PersistentHashMap_insert___redArg(x_27, x_28, x_25, x_1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_26);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_6 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
lean_inc_ref(x_1);
x_7 = l_Lean_PersistentHashMap_find_x3f___redArg(x_5, x_6, x_4, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_apply_1(x_2, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec_ref(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_shareCommonAlpha_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_7 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
lean_inc_ref(x_1);
x_8 = l_Lean_PersistentHashMap_find_x3f___redArg(x_6, x_7, x_5, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_3, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_mkApp(x_10, x_13);
x_16 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_15, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec_ref(x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
}
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_21);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_23 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_23);
x_24 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_25 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
lean_inc_ref(x_1);
x_26 = l_Lean_PersistentHashMap_find_x3f___redArg(x_24, x_25, x_23, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_20, x_2);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_21, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_mkLambda(x_19, x_22, x_28, x_31);
x_34 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_33, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec_ref(x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
return x_36;
}
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_39);
x_40 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_41 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_41);
x_42 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_43 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
lean_inc_ref(x_1);
x_44 = l_Lean_PersistentHashMap_find_x3f___redArg(x_42, x_43, x_41, x_1);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_38, x_2);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_39, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Lean_mkForall(x_37, x_40, x_46, x_49);
x_52 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_51, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec_ref(x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_2);
return x_54;
}
}
case 8:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_58);
x_59 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_60 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_60);
x_61 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_62 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
lean_inc_ref(x_1);
x_63 = l_Lean_PersistentHashMap_find_x3f___redArg(x_61, x_62, x_60, x_1);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_57, x_2);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_58, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = l_Lean_Expr_letE___override(x_55, x_56, x_65, x_68, x_59);
x_71 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_70, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_1);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec_ref(x_63);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_2);
return x_73;
}
}
case 10:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_76);
x_77 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_78 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
lean_inc_ref(x_1);
x_79 = l_Lean_PersistentHashMap_find_x3f___redArg(x_77, x_78, x_76, x_1);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_75, x_2);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = l_Lean_mkMData(x_74, x_81);
x_84 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_83, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
lean_dec_ref(x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_2);
return x_86;
}
}
case 11:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_90);
x_91 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0;
x_92 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1;
lean_inc_ref(x_1);
x_93 = l_Lean_PersistentHashMap_find_x3f___redArg(x_91, x_92, x_90, x_1);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_89, x_2);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = l_Lean_mkProj(x_87, x_88, x_95);
x_98 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_97, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_1);
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
lean_dec_ref(x_93);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_2);
return x_100;
}
}
default: 
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_102);
x_103 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__2;
x_104 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__3;
lean_inc_ref(x_1);
lean_inc_ref(x_102);
x_105 = l_Lean_PersistentHashMap_findEntry_x3f___redArg(x_103, x_104, x_102, x_1);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_2);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_2, 1);
lean_dec(x_107);
x_108 = lean_ctor_get(x_2, 0);
lean_dec(x_108);
x_109 = lean_box(0);
lean_inc_ref(x_1);
x_110 = l_Lean_PersistentHashMap_insert___redArg(x_103, x_104, x_102, x_1, x_109);
lean_ctor_set(x_2, 1, x_110);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_2);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_112 = lean_box(0);
lean_inc_ref(x_1);
x_113 = l_Lean_PersistentHashMap_insert___redArg(x_103, x_104, x_102, x_1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_101);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
lean_object* x_116; uint8_t x_117; 
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_1);
x_116 = lean_ctor_get(x_105, 0);
lean_inc(x_116);
lean_dec_ref(x_105);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_116, 1);
lean_dec(x_118);
lean_ctor_set(x_116, 1, x_2);
return x_116;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_2);
return x_120;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_shareCommonAlpha(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_ExprPtr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AlphaShareCommon(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_ExprPtr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instHashableAlphaKey = _init_l_Lean_Meta_Grind_instHashableAlphaKey();
lean_mark_persistent(l_Lean_Meta_Grind_instHashableAlphaKey);
l_Lean_Meta_Grind_instBEqAlphaKey = _init_l_Lean_Meta_Grind_instBEqAlphaKey();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqAlphaKey);
l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__0);
l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__1);
l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__2);
l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
