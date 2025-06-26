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
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instHashableExprPtr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableAlphaKey;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqAlphaKey___lam__0(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_shareCommonAlpha_go(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqAlphaKey___lam__0___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild(lean_object*);
uint8_t l_Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_hashChild___boxed(lean_object*);
static lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableAlphaKey___lam__0(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash___boxed(lean_object*);
static lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqAlphaKey;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(lean_object*);
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___Lean_PersistentHashMap_findEntry_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableAlphaKey___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_28);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
return x_34;
}
}
case 10:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec(x_35);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = l_Lean_KVMap_eqv(x_35, x_37);
return x_40;
}
}
else
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
return x_42;
}
}
case 11:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_52; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
x_52 = lean_name_eq(x_43, x_46);
lean_dec(x_46);
lean_dec(x_43);
if (x_52 == 0)
{
lean_dec(x_47);
lean_dec(x_44);
x_49 = x_52;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_eq(x_44, x_47);
lean_dec(x_47);
lean_dec(x_44);
x_49 = x_53;
goto block_51;
}
block_51:
{
if (x_49 == 0)
{
lean_dec(x_48);
lean_dec(x_45);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_45, x_48);
lean_dec(x_48);
lean_dec(x_45);
return x_50;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_unbox(x_54);
return x_55;
}
}
default: 
{
uint8_t x_56; 
x_56 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_56;
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
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
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
static lean_object* _init_l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqAlphaKey___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg___closed__0;
x_4 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findEntryAux___at___Lean_PersistentHashMap_findEntry_x3f_spec__0___redArg(x_3, x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqExprPtr___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableExprPtr___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_4 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__0;
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__1;
x_6 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_8, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableAlphaKey___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_4 = l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg___closed__0;
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg___closed__0;
x_6 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_alphaHash(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_8, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_6);
x_7 = l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg(x_6, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_8 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_5, x_1, x_2);
lean_inc_n(x_2, 2);
x_9 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_8, x_2, x_2);
x_10 = lean_box(0);
lean_inc(x_2);
x_11 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg(x_6, x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_dec(x_16);
lean_inc(x_15);
x_17 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_5, x_1, x_15);
lean_ctor_set(x_3, 0, x_17);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
lean_inc(x_18);
x_19 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_5, x_1, x_18);
lean_ctor_set(x_3, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_22);
x_23 = l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg(x_22, x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_2);
x_24 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_21, x_1, x_2);
lean_inc_n(x_2, 2);
x_25 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_24, x_2, x_2);
x_26 = lean_box(0);
lean_inc(x_2);
x_27 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg(x_22, x_2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
lean_inc(x_31);
x_33 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_21, x_1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__0;
x_6 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__1;
lean_inc(x_1);
x_7 = l_Lean_PersistentHashMap_find_x3f___redArg(x_5, x_6, x_4, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_apply_1(x_2, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__0;
x_4 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f_spec__0___redArg(x_3, x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_shareCommonAlpha_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_3, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_app___override(x_8, x_11);
x_14 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_13, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
return x_16;
}
}
case 6:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_inc(x_1);
x_22 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_21, x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_18, x_2);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_19, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Expr_lam___override(x_17, x_24, x_27, x_20);
x_30 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_29, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
return x_32;
}
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
lean_inc(x_1);
x_38 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_37, x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_34, x_2);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_35, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Expr_forallE___override(x_33, x_40, x_43, x_36);
x_46 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_45, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_2);
return x_48;
}
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 3);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_inc(x_1);
x_55 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_54, x_1);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_51, x_2);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_52, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Expr_letE___override(x_49, x_50, x_57, x_60, x_53);
x_63 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_62, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_1);
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
lean_dec(x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_2);
return x_65;
}
}
case 10:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
lean_inc(x_1);
x_69 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_68, x_1);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_67, x_2);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Expr_mdata___override(x_66, x_71);
x_74 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_73, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_1);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
lean_dec(x_69);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_2);
return x_76;
}
}
case 11:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
lean_inc(x_1);
x_81 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_80, x_1);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_79, x_2);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_proj___override(x_77, x_78, x_83);
x_86 = l___private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save(x_1, x_85, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_1);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_2);
return x_88;
}
}
default: 
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_2, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
lean_inc(x_1);
lean_inc(x_90);
x_91 = l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg(x_90, x_1);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_2);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_2, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_2, 0);
lean_dec(x_94);
x_95 = lean_box(0);
lean_inc(x_1);
x_96 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg(x_90, x_1, x_95);
lean_ctor_set(x_2, 1, x_96);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_2);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_2);
x_98 = lean_box(0);
lean_inc(x_1);
x_99 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg(x_90, x_1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; uint8_t x_103; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_1);
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
lean_dec(x_91);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 1);
lean_dec(x_104);
lean_ctor_set(x_102, 1, x_2);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_2);
return x_106;
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
l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_findEntry_x3f___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__0___redArg___closed__0);
l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__0);
l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg___closed__1);
l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__2___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
