// Lean compiler output
// Module: Lean.Meta.Offset
// Imports: Init Lean.Data.LBool Lean.Meta.InferType Lean.Meta.AppBuilder
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
static lean_object* l_Lean_Meta_evalNat_visit___closed__1;
static lean_object* l_Lean_Meta_isNatProjInst___closed__18;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isNatProjInst___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__5;
static lean_object* l_Lean_Meta_isDefEqOffset___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__6;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__12;
static lean_object* l_Lean_Meta_isNatProjInst___closed__3;
static lean_object* l_Lean_Meta_isNatProjInst___closed__5;
lean_object* l_Lean_Meta_unfoldProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isDefEqOffset___closed__1;
static lean_object* l_Lean_Meta_evalNat_visit___closed__3;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__8;
static lean_object* l_Lean_Meta_isNatProjInst___closed__19;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__4;
static lean_object* l_Lean_Meta_isNatProjInst___closed__9;
LEAN_EXPORT uint8_t l_Lean_Meta_isNatProjInst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__20;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__7;
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__15;
static lean_object* l_Lean_Meta_isNatProjInst___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__16;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat___closed__2;
static lean_object* l_Lean_Meta_isNatProjInst___closed__14;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isNatProjInst___closed__11;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasMVar(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_st_ref_get(x_3, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_instantiateMVarsCore(x_13, x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_3, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_3, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_15);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_3, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_15);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_getAppFn(x_12);
x_14 = l_Lean_Expr_isMVar(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_8);
x_15 = lean_apply_6(x_2, x_12, x_3, x_4, x_5, x_6, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_getAppFn(x_19);
x_21 = l_Lean_Expr_isMVar(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_apply_6(x_2, x_19, x_3, x_4, x_5, x_6, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isNatProjInst___closed__1;
x_2 = l_Lean_Meta_isNatProjInst___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isNatProjInst___closed__4;
x_2 = l_Lean_Meta_isNatProjInst___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HSub", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hSub", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isNatProjInst___closed__7;
x_2 = l_Lean_Meta_isNatProjInst___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HMul", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hMul", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isNatProjInst___closed__10;
x_2 = l_Lean_Meta_isNatProjInst___closed__11;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Add", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("add", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isNatProjInst___closed__13;
x_2 = l_Lean_Meta_isNatProjInst___closed__14;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Sub", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sub", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isNatProjInst___closed__16;
x_2 = l_Lean_Meta_isNatProjInst___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Mul", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mul", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isNatProjInst___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isNatProjInst___closed__19;
x_2 = l_Lean_Meta_isNatProjInst___closed__20;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isNatProjInst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_dec_eq(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
x_3 = x_28;
goto block_25;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Meta_isNatProjInst___closed__15;
x_30 = lean_name_eq(x_1, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Meta_isNatProjInst___closed__18;
x_32 = lean_name_eq(x_1, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_isNatProjInst___closed__21;
x_34 = lean_name_eq(x_1, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_3 = x_35;
goto block_25;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = 1;
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = 1;
return x_38;
}
}
block_25:
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_3);
x_4 = lean_unsigned_to_nat(6u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_isNatProjInst___closed__3;
x_10 = lean_name_eq(x_1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_isNatProjInst___closed__6;
x_12 = lean_name_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Meta_isNatProjInst___closed__9;
x_14 = lean_name_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Meta_isNatProjInst___closed__12;
x_16 = lean_name_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_dec_eq(x_2, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_isNatProjInst___closed__3;
x_21 = lean_name_eq(x_1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 1;
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 1;
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isNatProjInst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_isNatProjInst(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__1;
x_2 = l_Lean_Meta_isNatProjInst___closed__20;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__1;
x_2 = l_Lean_Meta_isNatProjInst___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__1;
x_2 = l_Lean_Meta_evalNat_visit___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__1;
x_2 = l_Lean_Meta_isNatProjInst___closed__14;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_7)) {
case 2:
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_getAppFn(x_12);
x_14 = l_Lean_Expr_isMVar(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_8);
x_15 = l_Lean_Meta_evalNat(x_12, x_2, x_3, x_4, x_5, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(0);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_getAppFn(x_19);
x_21 = l_Lean_Expr_isMVar(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Meta_evalNat(x_19, x_2, x_3, x_4, x_5, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_95; uint8_t x_149; lean_object* x_203; uint8_t x_204; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_26);
x_203 = l_Lean_Meta_evalNat_visit___closed__5;
x_204 = lean_name_eq(x_25, x_203);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = l_Lean_Meta_evalNat_visit___closed__6;
x_206 = lean_name_eq(x_25, x_205);
if (x_206 == 0)
{
uint8_t x_207; 
x_207 = 0;
x_149 = x_207;
goto block_202;
}
else
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_unsigned_to_nat(2u);
x_209 = lean_nat_dec_eq(x_27, x_208);
x_149 = x_209;
goto block_202;
}
}
else
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_nat_dec_eq(x_27, x_210);
if (x_211 == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = l_Lean_Meta_evalNat_visit___closed__6;
x_213 = lean_name_eq(x_25, x_212);
if (x_213 == 0)
{
uint8_t x_214; 
x_214 = 0;
x_149 = x_214;
goto block_202;
}
else
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_unsigned_to_nat(2u);
x_216 = lean_nat_dec_eq(x_27, x_215);
x_149 = x_216;
goto block_202;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_25);
x_217 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_218 = lean_nat_sub(x_217, x_210);
lean_dec(x_217);
x_219 = l_Lean_Expr_getRevArg_x21(x_1, x_218);
x_220 = l_Lean_Meta_evalNat(x_219, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_220);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_220, 0);
lean_dec(x_223);
x_224 = lean_box(0);
lean_ctor_set(x_220, 0, x_224);
return x_220;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_220, 1);
lean_inc(x_225);
lean_dec(x_220);
x_226 = lean_box(0);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_220);
if (x_228 == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_220, 0);
lean_dec(x_229);
x_230 = !lean_is_exclusive(x_221);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_221, 0);
x_232 = lean_nat_add(x_231, x_210);
lean_dec(x_231);
lean_ctor_set(x_221, 0, x_232);
return x_220;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_221, 0);
lean_inc(x_233);
lean_dec(x_221);
x_234 = lean_nat_add(x_233, x_210);
lean_dec(x_233);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_220, 0, x_235);
return x_220;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_220, 1);
lean_inc(x_236);
lean_dec(x_220);
x_237 = lean_ctor_get(x_221, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_238 = x_221;
} else {
 lean_dec_ref(x_221);
 x_238 = lean_box(0);
}
x_239 = lean_nat_add(x_237, x_210);
lean_dec(x_237);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_236);
return x_241;
}
}
}
else
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_220);
if (x_242 == 0)
{
return x_220;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_220, 0);
x_244 = lean_ctor_get(x_220, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_220);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
block_94:
{
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Meta_isNatProjInst(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = l_Lean_Meta_evalNat(x_41, x_2, x_3, x_4, x_5, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_25);
x_47 = lean_nat_sub(x_27, x_26);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_47, x_48);
lean_dec(x_47);
lean_inc(x_1);
x_50 = l_Lean_Expr_getRevArg_x21(x_1, x_49);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_evalNat(x_50, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_51, 0, x_55);
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_dec(x_51);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
lean_dec(x_52);
x_61 = lean_nat_sub(x_27, x_48);
lean_dec(x_27);
x_62 = lean_nat_sub(x_61, x_48);
lean_dec(x_61);
x_63 = l_Lean_Expr_getRevArg_x21(x_1, x_62);
x_64 = l_Lean_Meta_evalNat(x_63, x_2, x_3, x_4, x_5, x_59);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_dec(x_60);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_64, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_65, 0);
x_76 = lean_nat_mul(x_60, x_75);
lean_dec(x_75);
lean_dec(x_60);
lean_ctor_set(x_65, 0, x_76);
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 0);
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_nat_mul(x_60, x_77);
lean_dec(x_77);
lean_dec(x_60);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_64, 0, x_79);
return x_64;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
lean_dec(x_64);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_82 = x_65;
} else {
 lean_dec_ref(x_65);
 x_82 = lean_box(0);
}
x_83 = lean_nat_mul(x_60, x_81);
lean_dec(x_81);
lean_dec(x_60);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_60);
x_86 = !lean_is_exclusive(x_64);
if (x_86 == 0)
{
return x_64;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_64, 0);
x_88 = lean_ctor_get(x_64, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_64);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_51);
if (x_90 == 0)
{
return x_51;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_51, 0);
x_92 = lean_ctor_get(x_51, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_51);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
block_148:
{
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = l_Lean_Meta_evalNat_visit___closed__2;
x_97 = lean_name_eq(x_25, x_96);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = 0;
x_28 = x_98;
goto block_94;
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_nat_dec_eq(x_27, x_99);
x_28 = x_100;
goto block_94;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_25);
x_101 = lean_nat_sub(x_27, x_26);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_sub(x_101, x_102);
lean_dec(x_101);
lean_inc(x_1);
x_104 = l_Lean_Expr_getRevArg_x21(x_1, x_103);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_105 = l_Lean_Meta_evalNat(x_104, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 0);
lean_dec(x_108);
x_109 = lean_box(0);
lean_ctor_set(x_105, 0, x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
lean_dec(x_105);
x_114 = lean_ctor_get(x_106, 0);
lean_inc(x_114);
lean_dec(x_106);
x_115 = lean_nat_sub(x_27, x_102);
lean_dec(x_27);
x_116 = lean_nat_sub(x_115, x_102);
lean_dec(x_115);
x_117 = l_Lean_Expr_getRevArg_x21(x_1, x_116);
x_118 = l_Lean_Meta_evalNat(x_117, x_2, x_3, x_4, x_5, x_113);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
lean_dec(x_114);
x_120 = !lean_is_exclusive(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_118, 0);
lean_dec(x_121);
x_122 = lean_box(0);
lean_ctor_set(x_118, 0, x_122);
return x_118;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec(x_118);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_118);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_118, 0);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_119);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_119, 0);
x_130 = lean_nat_sub(x_114, x_129);
lean_dec(x_129);
lean_dec(x_114);
lean_ctor_set(x_119, 0, x_130);
return x_118;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_119, 0);
lean_inc(x_131);
lean_dec(x_119);
x_132 = lean_nat_sub(x_114, x_131);
lean_dec(x_131);
lean_dec(x_114);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_118, 0, x_133);
return x_118;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_118, 1);
lean_inc(x_134);
lean_dec(x_118);
x_135 = lean_ctor_get(x_119, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_136 = x_119;
} else {
 lean_dec_ref(x_119);
 x_136 = lean_box(0);
}
x_137 = lean_nat_sub(x_114, x_135);
lean_dec(x_135);
lean_dec(x_114);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_114);
x_140 = !lean_is_exclusive(x_118);
if (x_140 == 0)
{
return x_118;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_118, 0);
x_142 = lean_ctor_get(x_118, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_118);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_105);
if (x_144 == 0)
{
return x_105;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_105, 0);
x_146 = lean_ctor_get(x_105, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_105);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
block_202:
{
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = l_Lean_Meta_evalNat_visit___closed__3;
x_151 = lean_name_eq(x_25, x_150);
if (x_151 == 0)
{
uint8_t x_152; 
x_152 = 0;
x_95 = x_152;
goto block_148;
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_unsigned_to_nat(2u);
x_154 = lean_nat_dec_eq(x_27, x_153);
x_95 = x_154;
goto block_148;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_25);
x_155 = lean_nat_sub(x_27, x_26);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_sub(x_155, x_156);
lean_dec(x_155);
lean_inc(x_1);
x_158 = l_Lean_Expr_getRevArg_x21(x_1, x_157);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_159 = l_Lean_Meta_evalNat(x_158, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
uint8_t x_161; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_159);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_159, 0);
lean_dec(x_162);
x_163 = lean_box(0);
lean_ctor_set(x_159, 0, x_163);
return x_159;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_dec(x_159);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_159, 1);
lean_inc(x_167);
lean_dec(x_159);
x_168 = lean_ctor_get(x_160, 0);
lean_inc(x_168);
lean_dec(x_160);
x_169 = lean_nat_sub(x_27, x_156);
lean_dec(x_27);
x_170 = lean_nat_sub(x_169, x_156);
lean_dec(x_169);
x_171 = l_Lean_Expr_getRevArg_x21(x_1, x_170);
x_172 = l_Lean_Meta_evalNat(x_171, x_2, x_3, x_4, x_5, x_167);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
lean_dec(x_168);
x_174 = !lean_is_exclusive(x_172);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_172, 0);
lean_dec(x_175);
x_176 = lean_box(0);
lean_ctor_set(x_172, 0, x_176);
return x_172;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
lean_dec(x_172);
x_178 = lean_box(0);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_172);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_172, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_173);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_173, 0);
x_184 = lean_nat_add(x_168, x_183);
lean_dec(x_183);
lean_dec(x_168);
lean_ctor_set(x_173, 0, x_184);
return x_172;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_173, 0);
lean_inc(x_185);
lean_dec(x_173);
x_186 = lean_nat_add(x_168, x_185);
lean_dec(x_185);
lean_dec(x_168);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_172, 0, x_187);
return x_172;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_172, 1);
lean_inc(x_188);
lean_dec(x_172);
x_189 = lean_ctor_get(x_173, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_190 = x_173;
} else {
 lean_dec_ref(x_173);
 x_190 = lean_box(0);
}
x_191 = lean_nat_add(x_168, x_189);
lean_dec(x_189);
lean_dec(x_168);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_188);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_168);
x_194 = !lean_is_exclusive(x_172);
if (x_194 == 0)
{
return x_172;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_172, 0);
x_196 = lean_ctor_get(x_172, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_172);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_159);
if (x_198 == 0)
{
return x_159;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_159, 0);
x_200 = lean_ctor_get(x_159, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_159);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
}
default: 
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_6);
return x_247;
}
}
}
}
static lean_object* _init_l_Lean_Meta_evalNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("zero", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
case 4:
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Meta_evalNat_visit___closed__1;
x_14 = lean_string_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_evalNat___closed__1;
x_18 = lean_string_dec_eq(x_11, x_17);
lean_dec(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Meta_evalNat___closed__2;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
case 5:
{
lean_object* x_29; 
x_29 = l_Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_29;
}
case 9:
{
lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
return x_35;
}
}
case 10:
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_1 = x_36;
goto _start;
}
default: 
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_9)) {
case 2:
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_9);
lean_dec(x_8);
x_10 = l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_getAppFn(x_14);
x_16 = l_Lean_Expr_isMVar(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_free_object(x_10);
x_1 = x_14;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_box(0);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_getAppFn(x_21);
x_23 = l_Lean_Expr_isMVar(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
x_1 = x_21;
x_7 = x_20;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_53; lean_object* x_133; uint8_t x_134; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_28);
x_133 = l_Lean_Meta_evalNat_visit___closed__5;
x_134 = lean_name_eq(x_27, x_133);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
lean_dec(x_8);
x_135 = l_Lean_Meta_evalNat_visit___closed__6;
x_136 = lean_name_eq(x_27, x_135);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = 0;
x_53 = x_137;
goto block_132;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_unsigned_to_nat(2u);
x_139 = lean_nat_dec_eq(x_29, x_138);
x_53 = x_139;
goto block_132;
}
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_dec_eq(x_29, x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_8);
x_142 = l_Lean_Meta_evalNat_visit___closed__6;
x_143 = lean_name_eq(x_27, x_142);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = 0;
x_53 = x_144;
goto block_132;
}
else
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_unsigned_to_nat(2u);
x_146 = lean_nat_dec_eq(x_29, x_145);
x_53 = x_146;
goto block_132;
}
}
else
{
uint8_t x_147; lean_object* x_148; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_1);
x_147 = 0;
x_148 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_8, x_147, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_148, 0);
lean_dec(x_151);
x_152 = lean_box(0);
lean_ctor_set(x_148, 0, x_152);
return x_148;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_148, 1);
lean_inc(x_153);
lean_dec(x_148);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_149);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_148);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_ctor_get(x_149, 0);
x_159 = lean_ctor_get(x_148, 0);
lean_dec(x_159);
x_160 = !lean_is_exclusive(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_158, 1);
x_162 = lean_nat_add(x_161, x_140);
lean_dec(x_161);
lean_ctor_set(x_158, 1, x_162);
return x_148;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_158, 0);
x_164 = lean_ctor_get(x_158, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_158);
x_165 = lean_nat_add(x_164, x_140);
lean_dec(x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_149, 0, x_166);
return x_148;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_167 = lean_ctor_get(x_149, 0);
x_168 = lean_ctor_get(x_148, 1);
lean_inc(x_168);
lean_dec(x_148);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = lean_nat_add(x_170, x_140);
lean_dec(x_170);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_149, 0, x_173);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_149);
lean_ctor_set(x_174, 1, x_168);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_175 = lean_ctor_get(x_149, 0);
lean_inc(x_175);
lean_dec(x_149);
x_176 = lean_ctor_get(x_148, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_177 = x_148;
} else {
 lean_dec_ref(x_148);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
x_181 = lean_nat_add(x_179, x_140);
lean_dec(x_179);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
if (lean_is_scalar(x_177)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_177;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_176);
return x_184;
}
}
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_148);
if (x_185 == 0)
{
return x_148;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_148, 0);
x_187 = lean_ctor_get(x_148, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_148);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
block_52:
{
if (x_30 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
x_46 = 0;
x_1 = x_45;
x_2 = x_46;
x_7 = x_44;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
return x_36;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
block_132:
{
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Meta_isNatProjInst___closed__15;
x_55 = lean_name_eq(x_27, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Meta_isNatProjInst___closed__6;
x_57 = lean_name_eq(x_27, x_56);
lean_dec(x_27);
if (x_57 == 0)
{
uint8_t x_58; 
lean_dec(x_29);
x_58 = 0;
x_30 = x_58;
goto block_52;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_unsigned_to_nat(6u);
x_60 = lean_nat_dec_eq(x_29, x_59);
lean_dec(x_29);
x_30 = x_60;
goto block_52;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_dec_eq(x_29, x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Lean_Meta_isNatProjInst___closed__6;
x_64 = lean_name_eq(x_27, x_63);
lean_dec(x_27);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_29);
x_65 = 0;
x_30 = x_65;
goto block_52;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_unsigned_to_nat(6u);
x_67 = lean_nat_dec_eq(x_29, x_66);
lean_dec(x_29);
x_30 = x_67;
goto block_52;
}
}
else
{
uint8_t x_68; 
lean_dec(x_29);
lean_dec(x_27);
x_68 = 1;
x_30 = x_68;
goto block_52;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_27);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_29, x_69);
x_71 = lean_nat_sub(x_70, x_69);
lean_dec(x_70);
lean_inc(x_1);
x_72 = l_Lean_Expr_getRevArg_x21(x_1, x_71);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_73 = l_Lean_Meta_evalNat(x_72, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_73, 0, x_77);
return x_73;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
lean_dec(x_73);
x_82 = lean_ctor_get(x_74, 0);
lean_inc(x_82);
lean_dec(x_74);
x_83 = lean_nat_sub(x_29, x_28);
lean_dec(x_29);
x_84 = lean_nat_sub(x_83, x_69);
lean_dec(x_83);
x_85 = l_Lean_Expr_getRevArg_x21(x_1, x_84);
x_86 = 0;
x_87 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_85, x_86, x_3, x_4, x_5, x_6, x_81);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
lean_dec(x_90);
x_91 = lean_box(0);
lean_ctor_set(x_87, 0, x_91);
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_88);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_87);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_87, 0);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_nat_add(x_100, x_82);
lean_dec(x_82);
lean_dec(x_100);
lean_ctor_set(x_97, 1, x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_97);
x_104 = lean_nat_add(x_103, x_82);
lean_dec(x_82);
lean_dec(x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_88, 0, x_105);
return x_87;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_88, 0);
x_107 = lean_ctor_get(x_87, 1);
lean_inc(x_107);
lean_dec(x_87);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
x_111 = lean_nat_add(x_109, x_82);
lean_dec(x_82);
lean_dec(x_109);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_88, 0, x_112);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_88);
lean_ctor_set(x_113, 1, x_107);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_114 = lean_ctor_get(x_88, 0);
lean_inc(x_114);
lean_dec(x_88);
x_115 = lean_ctor_get(x_87, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_116 = x_87;
} else {
 lean_dec_ref(x_87);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
x_120 = lean_nat_add(x_118, x_82);
lean_dec(x_82);
lean_dec(x_118);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
if (lean_is_scalar(x_116)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_116;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_82);
x_124 = !lean_is_exclusive(x_87);
if (x_124 == 0)
{
return x_87;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_87, 0);
x_126 = lean_ctor_get(x_87, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_87);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_73);
if (x_128 == 0)
{
return x_73;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_73, 0);
x_130 = lean_ctor_get(x_73, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_73);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
}
default: 
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_7);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_1);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_7);
return x_194;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_unsigned_to_nat(0u);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_1);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_7);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_1);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_7);
return x_200;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_7)) {
case 2:
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_getAppFn(x_12);
x_14 = l_Lean_Expr_isMVar(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_free_object(x_8);
x_1 = x_12;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(0);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_getAppFn(x_19);
x_21 = l_Lean_Expr_isMVar(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
x_1 = x_19;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_40; lean_object* x_50; uint8_t x_51; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_26);
x_50 = l_Lean_Meta_evalNat_visit___closed__5;
x_51 = lean_name_eq(x_25, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Meta_evalNat_visit___closed__6;
x_53 = lean_name_eq(x_25, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_40 = x_54;
goto block_49;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_nat_dec_eq(x_27, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_40 = x_57;
goto block_49;
}
else
{
uint8_t x_58; lean_object* x_59; 
lean_dec(x_27);
lean_dec(x_25);
x_58 = 1;
x_59 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_1, x_58, x_2, x_3, x_4, x_5, x_6);
return x_59;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_dec_eq(x_27, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_Meta_evalNat_visit___closed__6;
x_63 = lean_name_eq(x_25, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_box(0);
x_40 = x_64;
goto block_49;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_dec_eq(x_27, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_box(0);
x_40 = x_67;
goto block_49;
}
else
{
uint8_t x_68; lean_object* x_69; 
lean_dec(x_27);
lean_dec(x_25);
x_68 = 1;
x_69 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_1, x_68, x_2, x_3, x_4, x_5, x_6);
return x_69;
}
}
}
else
{
uint8_t x_70; lean_object* x_71; 
lean_dec(x_27);
lean_dec(x_25);
x_70 = 1;
x_71 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_1, x_70, x_2, x_3, x_4, x_5, x_6);
return x_71;
}
}
block_39:
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_28);
x_29 = l_Lean_Meta_isNatProjInst___closed__6;
x_30 = lean_name_eq(x_25, x_29);
lean_dec(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(6u);
x_34 = lean_nat_dec_eq(x_27, x_33);
lean_dec(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
else
{
uint8_t x_37; lean_object* x_38; 
x_37 = 1;
x_38 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_1, x_37, x_2, x_3, x_4, x_5, x_6);
return x_38;
}
}
}
block_49:
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_40);
x_41 = l_Lean_Meta_isNatProjInst___closed__15;
x_42 = lean_name_eq(x_25, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_28 = x_43;
goto block_39;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_nat_dec_eq(x_27, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_28 = x_46;
goto block_39;
}
else
{
uint8_t x_47; lean_object* x_48; 
lean_dec(x_27);
lean_dec(x_25);
x_47 = 1;
x_48 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffsetAux(x_1, x_47, x_2, x_3, x_4, x_5, x_6);
return x_48;
}
}
}
}
default: 
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_6);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_6);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
x_22 = lean_box(x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_mkNatLit(x_2);
x_15 = l_Lean_Meta_mkAdd(x_1, x_14, x_3, x_4, x_5, x_6, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = l_Lean_mkNatLit(x_2);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_mkNatLit(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Meta_isDefEqOffset___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_evalNat_visit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isDefEqOffset___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isDefEqOffset___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_431; 
x_8 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_431 = lean_ctor_get_uint8(x_9, 11);
lean_dec(x_9);
if (x_431 == 0)
{
uint8_t x_432; 
x_432 = 1;
x_12 = x_432;
goto block_430;
}
else
{
uint8_t x_433; 
x_433 = 0;
x_12 = x_433;
goto block_430;
}
block_430:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Meta_evalNat(x_1, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = 2;
x_21 = lean_box(x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = 2;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_28 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset(x_2, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = 2;
x_36 = lean_box(x_35);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = 2;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_nat_dec_eq(x_27, x_42);
lean_dec(x_42);
lean_dec(x_27);
x_44 = l_Bool_toLBool(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_isDefEqOffset___closed__2;
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_49, 0, x_46);
lean_closure_set(x_49, 1, x_48);
x_50 = 0;
x_51 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_49, x_50, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = 2;
x_57 = lean_box(x_56);
lean_ctor_set(x_51, 0, x_57);
return x_51;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = 2;
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_51);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_51, 0);
lean_dec(x_63);
x_64 = lean_box(x_44);
lean_ctor_set(x_51, 0, x_64);
return x_51;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_dec(x_51);
x_66 = lean_box(x_44);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_51);
if (x_68 == 0)
{
return x_51;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_51, 0);
x_70 = lean_ctor_get(x_51, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_51);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_45);
if (x_72 == 0)
{
return x_45;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_45, 0);
x_74 = lean_ctor_get(x_45, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_45);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_31);
if (x_76 == 0)
{
return x_31;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_31, 0);
x_78 = lean_ctor_get(x_31, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_31);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_2);
x_80 = lean_ctor_get(x_29, 0);
lean_inc(x_80);
lean_dec(x_29);
x_81 = lean_ctor_get(x_28, 1);
lean_inc(x_81);
lean_dec(x_28);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_nat_dec_le(x_83, x_27);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_27);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_85 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_81);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Meta_isDefEqOffset___closed__2;
x_89 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_89, 0, x_86);
lean_closure_set(x_89, 1, x_88);
x_90 = 0;
x_91 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_89, x_90, x_3, x_4, x_5, x_6, x_87);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
x_96 = 2;
x_97 = lean_box(x_96);
lean_ctor_set(x_91, 0, x_97);
return x_91;
}
else
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_99 = 2;
x_100 = lean_box(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_91);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_91, 0);
lean_dec(x_103);
x_104 = 0;
x_105 = lean_box(x_104);
lean_ctor_set(x_91, 0, x_105);
return x_91;
}
else
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_91, 1);
lean_inc(x_106);
lean_dec(x_91);
x_107 = 0;
x_108 = lean_box(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_91);
if (x_110 == 0)
{
return x_91;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_91, 0);
x_112 = lean_ctor_get(x_91, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_91);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_85);
if (x_114 == 0)
{
return x_85;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_85, 0);
x_116 = lean_ctor_get(x_85, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_85);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_nat_sub(x_27, x_83);
lean_dec(x_83);
lean_dec(x_27);
x_119 = l_Lean_mkNatLit(x_118);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_120 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_81);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Meta_isDefEqOffset___closed__2;
x_124 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_124, 0, x_121);
lean_closure_set(x_124, 1, x_123);
x_125 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_126 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_124, x_125, x_3, x_4, x_5, x_6, x_122);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
uint8_t x_129; 
lean_dec(x_119);
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 0);
lean_dec(x_130);
x_131 = 2;
x_132 = lean_box(x_131);
lean_ctor_set(x_126, 0, x_132);
return x_126;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_dec(x_126);
x_134 = 2;
x_135 = lean_box(x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_126, 1);
lean_inc(x_137);
lean_dec(x_126);
x_138 = lean_is_expr_def_eq(x_119, x_82, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; uint8_t x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
x_142 = l_Bool_toLBool(x_141);
x_143 = lean_box(x_142);
lean_ctor_set(x_138, 0, x_143);
return x_138;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_138, 0);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_138);
x_146 = lean_unbox(x_144);
lean_dec(x_144);
x_147 = l_Bool_toLBool(x_146);
x_148 = lean_box(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
return x_149;
}
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_138);
if (x_150 == 0)
{
return x_138;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_138, 0);
x_152 = lean_ctor_get(x_138, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_138);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_119);
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_126);
if (x_154 == 0)
{
return x_126;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_126, 0);
x_156 = lean_ctor_get(x_126, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_126);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_119);
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_158 = !lean_is_exclusive(x_120);
if (x_158 == 0)
{
return x_120;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_120, 0);
x_160 = lean_ctor_get(x_120, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_120);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_28);
if (x_162 == 0)
{
return x_28;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_28, 0);
x_164 = lean_ctor_get(x_28, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_28);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_16);
if (x_166 == 0)
{
return x_16;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_16, 0);
x_168 = lean_ctor_get(x_16, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_16);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_14, 0);
lean_inc(x_170);
lean_dec(x_14);
x_171 = lean_ctor_get(x_13, 1);
lean_inc(x_171);
lean_dec(x_13);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_174 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset(x_2, x_3, x_4, x_5, x_6, x_171);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_177 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_177);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_177, 0);
lean_dec(x_180);
x_181 = 2;
x_182 = lean_box(x_181);
lean_ctor_set(x_177, 0, x_182);
return x_177;
}
else
{
lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
lean_dec(x_177);
x_184 = 2;
x_185 = lean_box(x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_183);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_177, 1);
lean_inc(x_187);
lean_dec(x_177);
x_188 = lean_ctor_get(x_178, 0);
lean_inc(x_188);
lean_dec(x_178);
x_189 = lean_nat_dec_le(x_173, x_188);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_188);
lean_dec(x_173);
lean_dec(x_172);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_190 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_187);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_Meta_isDefEqOffset___closed__2;
x_194 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_194, 0, x_191);
lean_closure_set(x_194, 1, x_193);
x_195 = 0;
x_196 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_194, x_195, x_3, x_4, x_5, x_6, x_192);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_unbox(x_197);
lean_dec(x_197);
if (x_198 == 0)
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_196);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_196, 0);
lean_dec(x_200);
x_201 = 2;
x_202 = lean_box(x_201);
lean_ctor_set(x_196, 0, x_202);
return x_196;
}
else
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_196, 1);
lean_inc(x_203);
lean_dec(x_196);
x_204 = 2;
x_205 = lean_box(x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
}
else
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_196);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_196, 0);
lean_dec(x_208);
x_209 = 0;
x_210 = lean_box(x_209);
lean_ctor_set(x_196, 0, x_210);
return x_196;
}
else
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_196, 1);
lean_inc(x_211);
lean_dec(x_196);
x_212 = 0;
x_213 = lean_box(x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_211);
return x_214;
}
}
}
else
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_196);
if (x_215 == 0)
{
return x_196;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_196, 0);
x_217 = lean_ctor_get(x_196, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_196);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_219 = !lean_is_exclusive(x_190);
if (x_219 == 0)
{
return x_190;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_190, 0);
x_221 = lean_ctor_get(x_190, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_190);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_nat_sub(x_188, x_173);
lean_dec(x_173);
lean_dec(x_188);
x_224 = l_Lean_mkNatLit(x_223);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_225 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_187);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l_Lean_Meta_isDefEqOffset___closed__2;
x_229 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_229, 0, x_226);
lean_closure_set(x_229, 1, x_228);
x_230 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_231 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_229, x_230, x_3, x_4, x_5, x_6, x_227);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_unbox(x_232);
lean_dec(x_232);
if (x_233 == 0)
{
uint8_t x_234; 
lean_dec(x_224);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_234 = !lean_is_exclusive(x_231);
if (x_234 == 0)
{
lean_object* x_235; uint8_t x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_231, 0);
lean_dec(x_235);
x_236 = 2;
x_237 = lean_box(x_236);
lean_ctor_set(x_231, 0, x_237);
return x_231;
}
else
{
lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_231, 1);
lean_inc(x_238);
lean_dec(x_231);
x_239 = 2;
x_240 = lean_box(x_239);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_238);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_231, 1);
lean_inc(x_242);
lean_dec(x_231);
x_243 = lean_is_expr_def_eq(x_172, x_224, x_3, x_4, x_5, x_6, x_242);
if (lean_obj_tag(x_243) == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; uint8_t x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_unbox(x_245);
lean_dec(x_245);
x_247 = l_Bool_toLBool(x_246);
x_248 = lean_box(x_247);
lean_ctor_set(x_243, 0, x_248);
return x_243;
}
else
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_243, 0);
x_250 = lean_ctor_get(x_243, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_243);
x_251 = lean_unbox(x_249);
lean_dec(x_249);
x_252 = l_Bool_toLBool(x_251);
x_253 = lean_box(x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
return x_254;
}
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_243);
if (x_255 == 0)
{
return x_243;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_243, 0);
x_257 = lean_ctor_get(x_243, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_243);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_224);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_259 = !lean_is_exclusive(x_231);
if (x_259 == 0)
{
return x_231;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_231, 0);
x_261 = lean_ctor_get(x_231, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_231);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_224);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_263 = !lean_is_exclusive(x_225);
if (x_263 == 0)
{
return x_225;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_225, 0);
x_265 = lean_ctor_get(x_225, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_225);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_177);
if (x_267 == 0)
{
return x_177;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_177, 0);
x_269 = lean_ctor_get(x_177, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_177);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
lean_dec(x_2);
x_271 = lean_ctor_get(x_175, 0);
lean_inc(x_271);
lean_dec(x_175);
x_272 = lean_ctor_get(x_174, 1);
lean_inc(x_272);
lean_dec(x_174);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_nat_dec_eq(x_173, x_274);
if (x_275 == 0)
{
uint8_t x_276; 
x_276 = lean_nat_dec_lt(x_173, x_274);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_nat_sub(x_173, x_274);
lean_dec(x_274);
lean_dec(x_173);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_278 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_172, x_277, x_3, x_4, x_5, x_6, x_272);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_281 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = l_Lean_Meta_isDefEqOffset___closed__2;
x_285 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_285, 0, x_282);
lean_closure_set(x_285, 1, x_284);
x_286 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_287 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_285, x_286, x_3, x_4, x_5, x_6, x_283);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_unbox(x_288);
lean_dec(x_288);
if (x_289 == 0)
{
uint8_t x_290; 
lean_dec(x_279);
lean_dec(x_273);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_290 = !lean_is_exclusive(x_287);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_287, 0);
lean_dec(x_291);
x_292 = 2;
x_293 = lean_box(x_292);
lean_ctor_set(x_287, 0, x_293);
return x_287;
}
else
{
lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; 
x_294 = lean_ctor_get(x_287, 1);
lean_inc(x_294);
lean_dec(x_287);
x_295 = 2;
x_296 = lean_box(x_295);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_294);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_287, 1);
lean_inc(x_298);
lean_dec(x_287);
x_299 = lean_is_expr_def_eq(x_279, x_273, x_3, x_4, x_5, x_6, x_298);
if (lean_obj_tag(x_299) == 0)
{
uint8_t x_300; 
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; uint8_t x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_299, 0);
x_302 = lean_unbox(x_301);
lean_dec(x_301);
x_303 = l_Bool_toLBool(x_302);
x_304 = lean_box(x_303);
lean_ctor_set(x_299, 0, x_304);
return x_299;
}
else
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; 
x_305 = lean_ctor_get(x_299, 0);
x_306 = lean_ctor_get(x_299, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_299);
x_307 = lean_unbox(x_305);
lean_dec(x_305);
x_308 = l_Bool_toLBool(x_307);
x_309 = lean_box(x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_306);
return x_310;
}
}
else
{
uint8_t x_311; 
x_311 = !lean_is_exclusive(x_299);
if (x_311 == 0)
{
return x_299;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_299, 0);
x_313 = lean_ctor_get(x_299, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_299);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_279);
lean_dec(x_273);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_315 = !lean_is_exclusive(x_287);
if (x_315 == 0)
{
return x_287;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_279);
lean_dec(x_273);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_319 = !lean_is_exclusive(x_281);
if (x_319 == 0)
{
return x_281;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_281, 0);
x_321 = lean_ctor_get(x_281, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_281);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
else
{
uint8_t x_323; 
lean_dec(x_273);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_323 = !lean_is_exclusive(x_278);
if (x_323 == 0)
{
return x_278;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_278, 0);
x_325 = lean_ctor_get(x_278, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_278);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_nat_sub(x_274, x_173);
lean_dec(x_173);
lean_dec(x_274);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_328 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_273, x_327, x_3, x_4, x_5, x_6, x_272);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_331 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_330);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = l_Lean_Meta_isDefEqOffset___closed__2;
x_335 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_335, 0, x_332);
lean_closure_set(x_335, 1, x_334);
x_336 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_337 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_335, x_336, x_3, x_4, x_5, x_6, x_333);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; uint8_t x_339; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_unbox(x_338);
lean_dec(x_338);
if (x_339 == 0)
{
uint8_t x_340; 
lean_dec(x_329);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_340 = !lean_is_exclusive(x_337);
if (x_340 == 0)
{
lean_object* x_341; uint8_t x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_337, 0);
lean_dec(x_341);
x_342 = 2;
x_343 = lean_box(x_342);
lean_ctor_set(x_337, 0, x_343);
return x_337;
}
else
{
lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_337, 1);
lean_inc(x_344);
lean_dec(x_337);
x_345 = 2;
x_346 = lean_box(x_345);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_344);
return x_347;
}
}
else
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_337, 1);
lean_inc(x_348);
lean_dec(x_337);
x_349 = lean_is_expr_def_eq(x_172, x_329, x_3, x_4, x_5, x_6, x_348);
if (lean_obj_tag(x_349) == 0)
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; uint8_t x_352; uint8_t x_353; lean_object* x_354; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_unbox(x_351);
lean_dec(x_351);
x_353 = l_Bool_toLBool(x_352);
x_354 = lean_box(x_353);
lean_ctor_set(x_349, 0, x_354);
return x_349;
}
else
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; 
x_355 = lean_ctor_get(x_349, 0);
x_356 = lean_ctor_get(x_349, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_349);
x_357 = lean_unbox(x_355);
lean_dec(x_355);
x_358 = l_Bool_toLBool(x_357);
x_359 = lean_box(x_358);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_356);
return x_360;
}
}
else
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_349);
if (x_361 == 0)
{
return x_349;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_349, 0);
x_363 = lean_ctor_get(x_349, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_349);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_329);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_365 = !lean_is_exclusive(x_337);
if (x_365 == 0)
{
return x_337;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_337, 0);
x_367 = lean_ctor_get(x_337, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_337);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
}
else
{
uint8_t x_369; 
lean_dec(x_329);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_369 = !lean_is_exclusive(x_331);
if (x_369 == 0)
{
return x_331;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_331, 0);
x_371 = lean_ctor_get(x_331, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_331);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
uint8_t x_373; 
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_373 = !lean_is_exclusive(x_328);
if (x_373 == 0)
{
return x_328;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_328, 0);
x_375 = lean_ctor_get(x_328, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_328);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
}
else
{
lean_object* x_377; 
lean_dec(x_274);
lean_dec(x_173);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_377 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_272);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = l_Lean_Meta_isDefEqOffset___closed__2;
x_381 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_381, 0, x_378);
lean_closure_set(x_381, 1, x_380);
x_382 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_383 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_381, x_382, x_3, x_4, x_5, x_6, x_379);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; uint8_t x_385; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_unbox(x_384);
lean_dec(x_384);
if (x_385 == 0)
{
uint8_t x_386; 
lean_dec(x_273);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_386 = !lean_is_exclusive(x_383);
if (x_386 == 0)
{
lean_object* x_387; uint8_t x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_383, 0);
lean_dec(x_387);
x_388 = 2;
x_389 = lean_box(x_388);
lean_ctor_set(x_383, 0, x_389);
return x_383;
}
else
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; 
x_390 = lean_ctor_get(x_383, 1);
lean_inc(x_390);
lean_dec(x_383);
x_391 = 2;
x_392 = lean_box(x_391);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_390);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_ctor_get(x_383, 1);
lean_inc(x_394);
lean_dec(x_383);
x_395 = lean_is_expr_def_eq(x_172, x_273, x_3, x_4, x_5, x_6, x_394);
if (lean_obj_tag(x_395) == 0)
{
uint8_t x_396; 
x_396 = !lean_is_exclusive(x_395);
if (x_396 == 0)
{
lean_object* x_397; uint8_t x_398; uint8_t x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_395, 0);
x_398 = lean_unbox(x_397);
lean_dec(x_397);
x_399 = l_Bool_toLBool(x_398);
x_400 = lean_box(x_399);
lean_ctor_set(x_395, 0, x_400);
return x_395;
}
else
{
lean_object* x_401; lean_object* x_402; uint8_t x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; 
x_401 = lean_ctor_get(x_395, 0);
x_402 = lean_ctor_get(x_395, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_395);
x_403 = lean_unbox(x_401);
lean_dec(x_401);
x_404 = l_Bool_toLBool(x_403);
x_405 = lean_box(x_404);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_402);
return x_406;
}
}
else
{
uint8_t x_407; 
x_407 = !lean_is_exclusive(x_395);
if (x_407 == 0)
{
return x_395;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_395, 0);
x_409 = lean_ctor_get(x_395, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_395);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
}
else
{
uint8_t x_411; 
lean_dec(x_273);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_411 = !lean_is_exclusive(x_383);
if (x_411 == 0)
{
return x_383;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_383, 0);
x_413 = lean_ctor_get(x_383, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_383);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
else
{
uint8_t x_415; 
lean_dec(x_273);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_415 = !lean_is_exclusive(x_377);
if (x_415 == 0)
{
return x_377;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_377, 0);
x_417 = lean_ctor_get(x_377, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_377);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
}
}
else
{
uint8_t x_419; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_419 = !lean_is_exclusive(x_174);
if (x_419 == 0)
{
return x_174;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_174, 0);
x_421 = lean_ctor_get(x_174, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_174);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
return x_422;
}
}
}
}
else
{
uint8_t x_423; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_423 = !lean_is_exclusive(x_13);
if (x_423 == 0)
{
return x_13;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_13, 0);
x_425 = lean_ctor_get(x_13, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_13);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
else
{
uint8_t x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_427 = 2;
x_428 = lean_box(x_427);
if (lean_is_scalar(x_11)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_11;
}
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_10);
return x_429;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_isNatProjInst___closed__1 = _init_l_Lean_Meta_isNatProjInst___closed__1();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__1);
l_Lean_Meta_isNatProjInst___closed__2 = _init_l_Lean_Meta_isNatProjInst___closed__2();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__2);
l_Lean_Meta_isNatProjInst___closed__3 = _init_l_Lean_Meta_isNatProjInst___closed__3();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__3);
l_Lean_Meta_isNatProjInst___closed__4 = _init_l_Lean_Meta_isNatProjInst___closed__4();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__4);
l_Lean_Meta_isNatProjInst___closed__5 = _init_l_Lean_Meta_isNatProjInst___closed__5();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__5);
l_Lean_Meta_isNatProjInst___closed__6 = _init_l_Lean_Meta_isNatProjInst___closed__6();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__6);
l_Lean_Meta_isNatProjInst___closed__7 = _init_l_Lean_Meta_isNatProjInst___closed__7();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__7);
l_Lean_Meta_isNatProjInst___closed__8 = _init_l_Lean_Meta_isNatProjInst___closed__8();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__8);
l_Lean_Meta_isNatProjInst___closed__9 = _init_l_Lean_Meta_isNatProjInst___closed__9();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__9);
l_Lean_Meta_isNatProjInst___closed__10 = _init_l_Lean_Meta_isNatProjInst___closed__10();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__10);
l_Lean_Meta_isNatProjInst___closed__11 = _init_l_Lean_Meta_isNatProjInst___closed__11();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__11);
l_Lean_Meta_isNatProjInst___closed__12 = _init_l_Lean_Meta_isNatProjInst___closed__12();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__12);
l_Lean_Meta_isNatProjInst___closed__13 = _init_l_Lean_Meta_isNatProjInst___closed__13();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__13);
l_Lean_Meta_isNatProjInst___closed__14 = _init_l_Lean_Meta_isNatProjInst___closed__14();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__14);
l_Lean_Meta_isNatProjInst___closed__15 = _init_l_Lean_Meta_isNatProjInst___closed__15();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__15);
l_Lean_Meta_isNatProjInst___closed__16 = _init_l_Lean_Meta_isNatProjInst___closed__16();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__16);
l_Lean_Meta_isNatProjInst___closed__17 = _init_l_Lean_Meta_isNatProjInst___closed__17();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__17);
l_Lean_Meta_isNatProjInst___closed__18 = _init_l_Lean_Meta_isNatProjInst___closed__18();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__18);
l_Lean_Meta_isNatProjInst___closed__19 = _init_l_Lean_Meta_isNatProjInst___closed__19();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__19);
l_Lean_Meta_isNatProjInst___closed__20 = _init_l_Lean_Meta_isNatProjInst___closed__20();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__20);
l_Lean_Meta_isNatProjInst___closed__21 = _init_l_Lean_Meta_isNatProjInst___closed__21();
lean_mark_persistent(l_Lean_Meta_isNatProjInst___closed__21);
l_Lean_Meta_evalNat_visit___closed__1 = _init_l_Lean_Meta_evalNat_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__1);
l_Lean_Meta_evalNat_visit___closed__2 = _init_l_Lean_Meta_evalNat_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__2);
l_Lean_Meta_evalNat_visit___closed__3 = _init_l_Lean_Meta_evalNat_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__3);
l_Lean_Meta_evalNat_visit___closed__4 = _init_l_Lean_Meta_evalNat_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__4);
l_Lean_Meta_evalNat_visit___closed__5 = _init_l_Lean_Meta_evalNat_visit___closed__5();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__5);
l_Lean_Meta_evalNat_visit___closed__6 = _init_l_Lean_Meta_evalNat_visit___closed__6();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__6);
l_Lean_Meta_evalNat___closed__1 = _init_l_Lean_Meta_evalNat___closed__1();
lean_mark_persistent(l_Lean_Meta_evalNat___closed__1);
l_Lean_Meta_evalNat___closed__2 = _init_l_Lean_Meta_evalNat___closed__2();
lean_mark_persistent(l_Lean_Meta_evalNat___closed__2);
l_Lean_Meta_isDefEqOffset___closed__1 = _init_l_Lean_Meta_isDefEqOffset___closed__1();
lean_mark_persistent(l_Lean_Meta_isDefEqOffset___closed__1);
l_Lean_Meta_isDefEqOffset___closed__2 = _init_l_Lean_Meta_isDefEqOffset___closed__2();
lean_mark_persistent(l_Lean_Meta_isDefEqOffset___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
