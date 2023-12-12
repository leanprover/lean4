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
static lean_object* l_Lean_Meta_isNatProjInst___closed__8;
static lean_object* l_Lean_Meta_isNatProjInst___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_isNatProjInst___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_2 = l_Lean_Meta_isNatProjInst___closed__14;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__1;
x_2 = l_Lean_Meta_isNatProjInst___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__1;
x_2 = l_Lean_Meta_evalNat_visit___closed__5;
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_117; lean_object* x_224; uint8_t x_225; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_26);
x_224 = l_Lean_Meta_evalNat_visit___closed__6;
x_225 = lean_name_eq(x_25, x_224);
if (x_225 == 0)
{
lean_object* x_226; 
x_226 = lean_box(0);
x_117 = x_226;
goto block_223;
}
else
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_unsigned_to_nat(1u);
x_228 = lean_nat_dec_eq(x_27, x_227);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_box(0);
x_117 = x_229;
goto block_223;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_25);
x_230 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_231 = lean_nat_sub(x_230, x_227);
lean_dec(x_230);
x_232 = l_Lean_Expr_getRevArg_x21(x_1, x_231);
x_233 = l_Lean_Meta_evalNat(x_232, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
if (lean_obj_tag(x_234) == 0)
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_233);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_233, 0);
lean_dec(x_236);
x_237 = lean_box(0);
lean_ctor_set(x_233, 0, x_237);
return x_233;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
lean_dec(x_233);
x_239 = lean_box(0);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_233);
if (x_241 == 0)
{
lean_object* x_242; uint8_t x_243; 
x_242 = lean_ctor_get(x_233, 0);
lean_dec(x_242);
x_243 = !lean_is_exclusive(x_234);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_234, 0);
x_245 = lean_nat_add(x_244, x_227);
lean_dec(x_244);
lean_ctor_set(x_234, 0, x_245);
return x_233;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_234, 0);
lean_inc(x_246);
lean_dec(x_234);
x_247 = lean_nat_add(x_246, x_227);
lean_dec(x_246);
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_233, 0, x_248);
return x_233;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_233, 1);
lean_inc(x_249);
lean_dec(x_233);
x_250 = lean_ctor_get(x_234, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 x_251 = x_234;
} else {
 lean_dec_ref(x_234);
 x_251 = lean_box(0);
}
x_252 = lean_nat_add(x_250, x_227);
lean_dec(x_250);
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(1, 1, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_249);
return x_254;
}
}
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_233);
if (x_255 == 0)
{
return x_233;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_233, 0);
x_257 = lean_ctor_get(x_233, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_233);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
}
block_116:
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_28);
x_29 = l_Lean_Meta_evalNat_visit___closed__2;
x_30 = lean_name_eq(x_25, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Meta_isNatProjInst(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
else
{
lean_object* x_34; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l_Lean_Meta_evalNat(x_43, x_2, x_3, x_4, x_5, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_nat_dec_eq(x_27, x_49);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Meta_isNatProjInst(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_6);
return x_53;
}
else
{
lean_object* x_54; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_54 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_box(0);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
lean_dec(x_55);
x_64 = l_Lean_Meta_evalNat(x_63, x_2, x_3, x_4, x_5, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_54);
if (x_65 == 0)
{
return x_54;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_54, 0);
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_54);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_25);
x_69 = lean_nat_sub(x_27, x_26);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_69, x_70);
lean_dec(x_69);
lean_inc(x_1);
x_72 = l_Lean_Expr_getRevArg_x21(x_1, x_71);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_73 = l_Lean_Meta_evalNat(x_72, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
lean_dec(x_73);
x_82 = lean_ctor_get(x_74, 0);
lean_inc(x_82);
lean_dec(x_74);
x_83 = lean_nat_sub(x_27, x_70);
lean_dec(x_27);
x_84 = lean_nat_sub(x_83, x_70);
lean_dec(x_83);
x_85 = l_Lean_Expr_getRevArg_x21(x_1, x_84);
x_86 = l_Lean_Meta_evalNat(x_85, x_2, x_3, x_4, x_5, x_81);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_82);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 0);
lean_dec(x_89);
x_90 = lean_box(0);
lean_ctor_set(x_86, 0, x_90);
return x_86;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_86, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_87);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_87, 0);
x_98 = lean_nat_mul(x_82, x_97);
lean_dec(x_97);
lean_dec(x_82);
lean_ctor_set(x_87, 0, x_98);
return x_86;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_87, 0);
lean_inc(x_99);
lean_dec(x_87);
x_100 = lean_nat_mul(x_82, x_99);
lean_dec(x_99);
lean_dec(x_82);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_86, 0, x_101);
return x_86;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_86, 1);
lean_inc(x_102);
lean_dec(x_86);
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_104 = x_87;
} else {
 lean_dec_ref(x_87);
 x_104 = lean_box(0);
}
x_105 = lean_nat_mul(x_82, x_103);
lean_dec(x_103);
lean_dec(x_82);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_82);
x_108 = !lean_is_exclusive(x_86);
if (x_108 == 0)
{
return x_86;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_86, 0);
x_110 = lean_ctor_get(x_86, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_86);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_73);
if (x_112 == 0)
{
return x_73;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_73, 0);
x_114 = lean_ctor_get(x_73, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_73);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
block_223:
{
lean_object* x_118; uint8_t x_119; 
lean_dec(x_117);
x_118 = l_Lean_Meta_evalNat_visit___closed__3;
x_119 = lean_name_eq(x_25, x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_Meta_evalNat_visit___closed__4;
x_121 = lean_name_eq(x_25, x_120);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_box(0);
x_28 = x_122;
goto block_116;
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_unsigned_to_nat(2u);
x_124 = lean_nat_dec_eq(x_27, x_123);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_box(0);
x_28 = x_125;
goto block_116;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_25);
x_126 = lean_nat_sub(x_27, x_26);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_sub(x_126, x_127);
lean_dec(x_126);
lean_inc(x_1);
x_129 = l_Lean_Expr_getRevArg_x21(x_1, x_128);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_130 = l_Lean_Meta_evalNat(x_129, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 0);
lean_dec(x_133);
x_134 = lean_box(0);
lean_ctor_set(x_130, 0, x_134);
return x_130;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
lean_dec(x_130);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_130, 1);
lean_inc(x_138);
lean_dec(x_130);
x_139 = lean_ctor_get(x_131, 0);
lean_inc(x_139);
lean_dec(x_131);
x_140 = lean_nat_sub(x_27, x_127);
lean_dec(x_27);
x_141 = lean_nat_sub(x_140, x_127);
lean_dec(x_140);
x_142 = l_Lean_Expr_getRevArg_x21(x_1, x_141);
x_143 = l_Lean_Meta_evalNat(x_142, x_2, x_3, x_4, x_5, x_138);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
lean_dec(x_139);
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
x_147 = lean_box(0);
lean_ctor_set(x_143, 0, x_147);
return x_143;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_dec(x_143);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_143, 0);
lean_dec(x_152);
x_153 = !lean_is_exclusive(x_144);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_144, 0);
x_155 = lean_nat_sub(x_139, x_154);
lean_dec(x_154);
lean_dec(x_139);
lean_ctor_set(x_144, 0, x_155);
return x_143;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_144, 0);
lean_inc(x_156);
lean_dec(x_144);
x_157 = lean_nat_sub(x_139, x_156);
lean_dec(x_156);
lean_dec(x_139);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_143, 0, x_158);
return x_143;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_143, 1);
lean_inc(x_159);
lean_dec(x_143);
x_160 = lean_ctor_get(x_144, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_161 = x_144;
} else {
 lean_dec_ref(x_144);
 x_161 = lean_box(0);
}
x_162 = lean_nat_sub(x_139, x_160);
lean_dec(x_160);
lean_dec(x_139);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_159);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_139);
x_165 = !lean_is_exclusive(x_143);
if (x_165 == 0)
{
return x_143;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_143, 0);
x_167 = lean_ctor_get(x_143, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_143);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_130);
if (x_169 == 0)
{
return x_130;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_130, 0);
x_171 = lean_ctor_get(x_130, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_130);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_unsigned_to_nat(2u);
x_174 = lean_nat_dec_eq(x_27, x_173);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = lean_box(0);
x_28 = x_175;
goto block_116;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_25);
x_176 = lean_nat_sub(x_27, x_26);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_sub(x_176, x_177);
lean_dec(x_176);
lean_inc(x_1);
x_179 = l_Lean_Expr_getRevArg_x21(x_1, x_178);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_180 = l_Lean_Meta_evalNat(x_179, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_180);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_180, 0);
lean_dec(x_183);
x_184 = lean_box(0);
lean_ctor_set(x_180, 0, x_184);
return x_180;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
lean_dec(x_180);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_180, 1);
lean_inc(x_188);
lean_dec(x_180);
x_189 = lean_ctor_get(x_181, 0);
lean_inc(x_189);
lean_dec(x_181);
x_190 = lean_nat_sub(x_27, x_177);
lean_dec(x_27);
x_191 = lean_nat_sub(x_190, x_177);
lean_dec(x_190);
x_192 = l_Lean_Expr_getRevArg_x21(x_1, x_191);
x_193 = l_Lean_Meta_evalNat(x_192, x_2, x_3, x_4, x_5, x_188);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
lean_dec(x_189);
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_193, 0);
lean_dec(x_196);
x_197 = lean_box(0);
lean_ctor_set(x_193, 0, x_197);
return x_193;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
lean_dec(x_193);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_193);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_193, 0);
lean_dec(x_202);
x_203 = !lean_is_exclusive(x_194);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_194, 0);
x_205 = lean_nat_add(x_189, x_204);
lean_dec(x_204);
lean_dec(x_189);
lean_ctor_set(x_194, 0, x_205);
return x_193;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_194, 0);
lean_inc(x_206);
lean_dec(x_194);
x_207 = lean_nat_add(x_189, x_206);
lean_dec(x_206);
lean_dec(x_189);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_193, 0, x_208);
return x_193;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_193, 1);
lean_inc(x_209);
lean_dec(x_193);
x_210 = lean_ctor_get(x_194, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_211 = x_194;
} else {
 lean_dec_ref(x_194);
 x_211 = lean_box(0);
}
x_212 = lean_nat_add(x_189, x_210);
lean_dec(x_210);
lean_dec(x_189);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_209);
return x_214;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_189);
x_215 = !lean_is_exclusive(x_193);
if (x_215 == 0)
{
return x_193;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_193, 0);
x_217 = lean_ctor_get(x_193, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_193);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_180);
if (x_219 == 0)
{
return x_180;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_180, 0);
x_221 = lean_ctor_get(x_180, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_180);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
}
}
default: 
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_259 = lean_box(0);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_6);
return x_260;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_8)) {
case 2:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_7);
x_9 = l_Lean_instantiateMVars___at___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_getAppFn(x_13);
x_15 = l_Lean_Expr_isMVar(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_free_object(x_9);
x_1 = x_13;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_getAppFn(x_20);
x_22 = l_Lean_Expr_isMVar(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
x_1 = x_20;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
}
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_96; lean_object* x_167; uint8_t x_168; 
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_27);
x_167 = l_Lean_Meta_evalNat_visit___closed__6;
x_168 = lean_name_eq(x_26, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_7);
x_169 = lean_box(0);
x_96 = x_169;
goto block_166;
}
else
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_dec_eq(x_28, x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_7);
x_172 = lean_box(0);
x_96 = x_172;
goto block_166;
}
else
{
lean_object* x_173; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_1);
x_173 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 1);
x_178 = lean_nat_add(x_177, x_170);
lean_dec(x_177);
lean_ctor_set(x_175, 1, x_178);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_173, 0, x_179);
return x_173;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_175, 0);
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_175);
x_182 = lean_nat_add(x_181, x_170);
lean_dec(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_173, 0, x_184);
return x_173;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_185 = lean_ctor_get(x_173, 0);
x_186 = lean_ctor_get(x_173, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_173);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_189 = x_185;
} else {
 lean_dec_ref(x_185);
 x_189 = lean_box(0);
}
x_190 = lean_nat_add(x_188, x_170);
lean_dec(x_188);
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_189;
}
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_186);
return x_193;
}
}
else
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_173);
if (x_194 == 0)
{
return x_173;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_173, 0);
x_196 = lean_ctor_get(x_173, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_173);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
block_95:
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_29);
x_30 = l_Lean_Meta_isNatProjInst___closed__15;
x_31 = lean_name_eq(x_26, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_isNatProjInst___closed__6;
x_33 = lean_name_eq(x_26, x_32);
lean_dec(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(6u);
x_37 = lean_nat_dec_eq(x_28, x_36);
lean_dec(x_28);
if (x_37 == 0)
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
else
{
lean_object* x_40; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
x_1 = x_49;
x_6 = x_48;
goto _start;
}
}
else
{
uint8_t x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_nat_dec_eq(x_28, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Meta_isNatProjInst___closed__6;
x_58 = lean_name_eq(x_26, x_57);
lean_dec(x_26);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_6);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(6u);
x_62 = lean_nat_dec_eq(x_28, x_61);
lean_dec(x_28);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_6);
return x_64;
}
else
{
lean_object* x_65; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_65 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_1 = x_74;
x_6 = x_73;
goto _start;
}
}
else
{
uint8_t x_76; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_65);
if (x_76 == 0)
{
return x_65;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 0);
x_78 = lean_ctor_get(x_65, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_65);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_28);
lean_dec(x_26);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_80 = l_Lean_Meta_unfoldProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
lean_dec(x_80);
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
lean_dec(x_81);
x_1 = x_89;
x_6 = x_88;
goto _start;
}
}
else
{
uint8_t x_91; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_80);
if (x_91 == 0)
{
return x_80;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
block_166:
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_96);
x_97 = l_Lean_Meta_evalNat_visit___closed__3;
x_98 = lean_name_eq(x_26, x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_box(0);
x_29 = x_99;
goto block_95;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_unsigned_to_nat(2u);
x_101 = lean_nat_dec_eq(x_28, x_100);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_box(0);
x_29 = x_102;
goto block_95;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_26);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_sub(x_28, x_103);
x_105 = lean_nat_sub(x_104, x_103);
lean_dec(x_104);
lean_inc(x_1);
x_106 = l_Lean_Expr_getRevArg_x21(x_1, x_105);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_Meta_evalNat(x_106, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_107, 0);
lean_dec(x_110);
x_111 = lean_box(0);
lean_ctor_set(x_107, 0, x_111);
return x_107;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
lean_dec(x_107);
x_116 = !lean_is_exclusive(x_108);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_108, 0);
x_118 = lean_nat_sub(x_28, x_27);
lean_dec(x_28);
x_119 = lean_nat_sub(x_118, x_103);
lean_dec(x_118);
x_120 = l_Lean_Expr_getRevArg_x21(x_1, x_119);
x_121 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_120, x_2, x_3, x_4, x_5, x_115);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 1);
x_126 = lean_nat_add(x_125, x_117);
lean_dec(x_117);
lean_dec(x_125);
lean_ctor_set(x_123, 1, x_126);
lean_ctor_set(x_108, 0, x_123);
lean_ctor_set(x_121, 0, x_108);
return x_121;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_123, 0);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_123);
x_129 = lean_nat_add(x_128, x_117);
lean_dec(x_117);
lean_dec(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_108, 0, x_130);
lean_ctor_set(x_121, 0, x_108);
return x_121;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_121, 0);
x_132 = lean_ctor_get(x_121, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_121);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_135 = x_131;
} else {
 lean_dec_ref(x_131);
 x_135 = lean_box(0);
}
x_136 = lean_nat_add(x_134, x_117);
lean_dec(x_117);
lean_dec(x_134);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_108, 0, x_137);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_108);
lean_ctor_set(x_138, 1, x_132);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_free_object(x_108);
lean_dec(x_117);
x_139 = !lean_is_exclusive(x_121);
if (x_139 == 0)
{
return x_121;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_121, 0);
x_141 = lean_ctor_get(x_121, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_121);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_108, 0);
lean_inc(x_143);
lean_dec(x_108);
x_144 = lean_nat_sub(x_28, x_27);
lean_dec(x_28);
x_145 = lean_nat_sub(x_144, x_103);
lean_dec(x_144);
x_146 = l_Lean_Expr_getRevArg_x21(x_1, x_145);
x_147 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_146, x_2, x_3, x_4, x_5, x_115);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_153 = x_148;
} else {
 lean_dec_ref(x_148);
 x_153 = lean_box(0);
}
x_154 = lean_nat_add(x_152, x_143);
lean_dec(x_143);
lean_dec(x_152);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_150)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_150;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_149);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_143);
x_158 = lean_ctor_get(x_147, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_147, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_160 = x_147;
} else {
 lean_dec_ref(x_147);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_107);
if (x_162 == 0)
{
return x_107;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_107, 0);
x_164 = lean_ctor_get(x_107, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_107);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
}
}
default: 
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_6);
return x_199;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_6);
return x_201;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = 2;
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = 2;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_20 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f(x_1, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_23 = l_Lean_Meta_evalNat(x_1, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = 2;
x_28 = lean_box(x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = 2;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_35 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = 2;
x_43 = lean_box(x_42);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = 2;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_nat_dec_eq(x_34, x_49);
lean_dec(x_49);
lean_dec(x_34);
x_51 = l_Bool_toLBool(x_50);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_52 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Meta_isDefEqOffset___closed__2;
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_56, 0, x_53);
lean_closure_set(x_56, 1, x_55);
x_57 = 0;
x_58 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_56, x_57, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
lean_dec(x_62);
x_63 = 2;
x_64 = lean_box(x_63);
lean_ctor_set(x_58, 0, x_64);
return x_58;
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
lean_dec(x_58);
x_66 = 2;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_58, 0);
lean_dec(x_70);
x_71 = lean_box(x_51);
lean_ctor_set(x_58, 0, x_71);
return x_58;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
lean_dec(x_58);
x_73 = lean_box(x_51);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
return x_58;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_58, 0);
x_77 = lean_ctor_get(x_58, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_58);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_52);
if (x_79 == 0)
{
return x_52;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_52, 0);
x_81 = lean_ctor_get(x_52, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_52);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_38);
if (x_83 == 0)
{
return x_38;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_38, 0);
x_85 = lean_ctor_get(x_38, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_38);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_2);
x_87 = lean_ctor_get(x_36, 0);
lean_inc(x_87);
lean_dec(x_36);
x_88 = lean_ctor_get(x_35, 1);
lean_inc(x_88);
lean_dec(x_35);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_nat_dec_le(x_90, x_34);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_92 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_88);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Meta_isDefEqOffset___closed__2;
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_96, 0, x_93);
lean_closure_set(x_96, 1, x_95);
x_97 = 0;
x_98 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_96, x_97, x_3, x_4, x_5, x_6, x_94);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_98);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_98, 0);
lean_dec(x_102);
x_103 = 2;
x_104 = lean_box(x_103);
lean_ctor_set(x_98, 0, x_104);
return x_98;
}
else
{
lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = 2;
x_107 = lean_box(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
else
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_98);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_98, 0);
lean_dec(x_110);
x_111 = 0;
x_112 = lean_box(x_111);
lean_ctor_set(x_98, 0, x_112);
return x_98;
}
else
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_98, 1);
lean_inc(x_113);
lean_dec(x_98);
x_114 = 0;
x_115 = lean_box(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
}
else
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_98);
if (x_117 == 0)
{
return x_98;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_98, 0);
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_98);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_92);
if (x_121 == 0)
{
return x_92;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_92, 0);
x_123 = lean_ctor_get(x_92, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_92);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_nat_sub(x_34, x_90);
lean_dec(x_90);
lean_dec(x_34);
x_126 = l_Lean_mkNatLit(x_125);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_127 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_88);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_Meta_isDefEqOffset___closed__2;
x_131 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_131, 0, x_128);
lean_closure_set(x_131, 1, x_130);
x_132 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_133 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_131, x_132, x_3, x_4, x_5, x_6, x_129);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
uint8_t x_136; 
lean_dec(x_126);
lean_dec(x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = !lean_is_exclusive(x_133);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_133, 0);
lean_dec(x_137);
x_138 = 2;
x_139 = lean_box(x_138);
lean_ctor_set(x_133, 0, x_139);
return x_133;
}
else
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_133, 1);
lean_inc(x_140);
lean_dec(x_133);
x_141 = 2;
x_142 = lean_box(x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_133, 1);
lean_inc(x_144);
lean_dec(x_133);
x_145 = lean_is_expr_def_eq(x_126, x_89, x_3, x_4, x_5, x_6, x_144);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; uint8_t x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
x_149 = l_Bool_toLBool(x_148);
x_150 = lean_box(x_149);
lean_ctor_set(x_145, 0, x_150);
return x_145;
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_145, 0);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_145);
x_153 = lean_unbox(x_151);
lean_dec(x_151);
x_154 = l_Bool_toLBool(x_153);
x_155 = lean_box(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
return x_156;
}
}
else
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_145);
if (x_157 == 0)
{
return x_145;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_145, 0);
x_159 = lean_ctor_get(x_145, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_145);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_126);
lean_dec(x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_161 = !lean_is_exclusive(x_133);
if (x_161 == 0)
{
return x_133;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_133, 0);
x_163 = lean_ctor_get(x_133, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_133);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_126);
lean_dec(x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_165 = !lean_is_exclusive(x_127);
if (x_165 == 0)
{
return x_127;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_127, 0);
x_167 = lean_ctor_get(x_127, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_127);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_35);
if (x_169 == 0)
{
return x_35;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_35, 0);
x_171 = lean_ctor_get(x_35, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_35);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_23);
if (x_173 == 0)
{
return x_23;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_23, 0);
x_175 = lean_ctor_get(x_23, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_23);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_21, 0);
lean_inc(x_177);
lean_dec(x_21);
x_178 = lean_ctor_get(x_20, 1);
lean_inc(x_178);
lean_dec(x_20);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_181 = l___private_Lean_Meta_Offset_0__Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6, x_178);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_184 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_184);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_184, 0);
lean_dec(x_187);
x_188 = 2;
x_189 = lean_box(x_188);
lean_ctor_set(x_184, 0, x_189);
return x_184;
}
else
{
lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_184, 1);
lean_inc(x_190);
lean_dec(x_184);
x_191 = 2;
x_192 = lean_box(x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_184, 1);
lean_inc(x_194);
lean_dec(x_184);
x_195 = lean_ctor_get(x_185, 0);
lean_inc(x_195);
lean_dec(x_185);
x_196 = lean_nat_dec_le(x_180, x_195);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_195);
lean_dec(x_180);
lean_dec(x_179);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_197 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_194);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l_Lean_Meta_isDefEqOffset___closed__2;
x_201 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_201, 0, x_198);
lean_closure_set(x_201, 1, x_200);
x_202 = 0;
x_203 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_201, x_202, x_3, x_4, x_5, x_6, x_199);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_unbox(x_204);
lean_dec(x_204);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_203);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_203, 0);
lean_dec(x_207);
x_208 = 2;
x_209 = lean_box(x_208);
lean_ctor_set(x_203, 0, x_209);
return x_203;
}
else
{
lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_203, 1);
lean_inc(x_210);
lean_dec(x_203);
x_211 = 2;
x_212 = lean_box(x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_210);
return x_213;
}
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_203);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_203, 0);
lean_dec(x_215);
x_216 = 0;
x_217 = lean_box(x_216);
lean_ctor_set(x_203, 0, x_217);
return x_203;
}
else
{
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_203, 1);
lean_inc(x_218);
lean_dec(x_203);
x_219 = 0;
x_220 = lean_box(x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
return x_221;
}
}
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_203);
if (x_222 == 0)
{
return x_203;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_203, 0);
x_224 = lean_ctor_get(x_203, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_203);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_226 = !lean_is_exclusive(x_197);
if (x_226 == 0)
{
return x_197;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_197, 0);
x_228 = lean_ctor_get(x_197, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_197);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_nat_sub(x_195, x_180);
lean_dec(x_180);
lean_dec(x_195);
x_231 = l_Lean_mkNatLit(x_230);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_232 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_194);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_Meta_isDefEqOffset___closed__2;
x_236 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_236, 0, x_233);
lean_closure_set(x_236, 1, x_235);
x_237 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_238 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_236, x_237, x_3, x_4, x_5, x_6, x_234);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
uint8_t x_241; 
lean_dec(x_231);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_241 = !lean_is_exclusive(x_238);
if (x_241 == 0)
{
lean_object* x_242; uint8_t x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_238, 0);
lean_dec(x_242);
x_243 = 2;
x_244 = lean_box(x_243);
lean_ctor_set(x_238, 0, x_244);
return x_238;
}
else
{
lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_238, 1);
lean_inc(x_245);
lean_dec(x_238);
x_246 = 2;
x_247 = lean_box(x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_238, 1);
lean_inc(x_249);
lean_dec(x_238);
x_250 = lean_is_expr_def_eq(x_179, x_231, x_3, x_4, x_5, x_6, x_249);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; uint8_t x_253; uint8_t x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_250, 0);
x_253 = lean_unbox(x_252);
lean_dec(x_252);
x_254 = l_Bool_toLBool(x_253);
x_255 = lean_box(x_254);
lean_ctor_set(x_250, 0, x_255);
return x_250;
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; 
x_256 = lean_ctor_get(x_250, 0);
x_257 = lean_ctor_get(x_250, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_250);
x_258 = lean_unbox(x_256);
lean_dec(x_256);
x_259 = l_Bool_toLBool(x_258);
x_260 = lean_box(x_259);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_257);
return x_261;
}
}
else
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_250);
if (x_262 == 0)
{
return x_250;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_250, 0);
x_264 = lean_ctor_get(x_250, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_250);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_231);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_266 = !lean_is_exclusive(x_238);
if (x_266 == 0)
{
return x_238;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_238, 0);
x_268 = lean_ctor_get(x_238, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_238);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_231);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_270 = !lean_is_exclusive(x_232);
if (x_270 == 0)
{
return x_232;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_232, 0);
x_272 = lean_ctor_get(x_232, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_232);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_184);
if (x_274 == 0)
{
return x_184;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_184, 0);
x_276 = lean_ctor_get(x_184, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_184);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_dec(x_2);
x_278 = lean_ctor_get(x_182, 0);
lean_inc(x_278);
lean_dec(x_182);
x_279 = lean_ctor_get(x_181, 1);
lean_inc(x_279);
lean_dec(x_181);
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
lean_dec(x_278);
x_282 = lean_nat_dec_eq(x_180, x_281);
if (x_282 == 0)
{
uint8_t x_283; 
x_283 = lean_nat_dec_lt(x_180, x_281);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_nat_sub(x_180, x_281);
lean_dec(x_281);
lean_dec(x_180);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_285 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_179, x_284, x_3, x_4, x_5, x_6, x_279);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_288 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = l_Lean_Meta_isDefEqOffset___closed__2;
x_292 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_292, 0, x_289);
lean_closure_set(x_292, 1, x_291);
x_293 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_294 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_292, x_293, x_3, x_4, x_5, x_6, x_290);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_unbox(x_295);
lean_dec(x_295);
if (x_296 == 0)
{
uint8_t x_297; 
lean_dec(x_286);
lean_dec(x_280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_297 = !lean_is_exclusive(x_294);
if (x_297 == 0)
{
lean_object* x_298; uint8_t x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_294, 0);
lean_dec(x_298);
x_299 = 2;
x_300 = lean_box(x_299);
lean_ctor_set(x_294, 0, x_300);
return x_294;
}
else
{
lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_294, 1);
lean_inc(x_301);
lean_dec(x_294);
x_302 = 2;
x_303 = lean_box(x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_301);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_294, 1);
lean_inc(x_305);
lean_dec(x_294);
x_306 = lean_is_expr_def_eq(x_286, x_280, x_3, x_4, x_5, x_6, x_305);
if (lean_obj_tag(x_306) == 0)
{
uint8_t x_307; 
x_307 = !lean_is_exclusive(x_306);
if (x_307 == 0)
{
lean_object* x_308; uint8_t x_309; uint8_t x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_306, 0);
x_309 = lean_unbox(x_308);
lean_dec(x_308);
x_310 = l_Bool_toLBool(x_309);
x_311 = lean_box(x_310);
lean_ctor_set(x_306, 0, x_311);
return x_306;
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; 
x_312 = lean_ctor_get(x_306, 0);
x_313 = lean_ctor_get(x_306, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_306);
x_314 = lean_unbox(x_312);
lean_dec(x_312);
x_315 = l_Bool_toLBool(x_314);
x_316 = lean_box(x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_313);
return x_317;
}
}
else
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_306);
if (x_318 == 0)
{
return x_306;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_306, 0);
x_320 = lean_ctor_get(x_306, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_306);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_286);
lean_dec(x_280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_322 = !lean_is_exclusive(x_294);
if (x_322 == 0)
{
return x_294;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_294, 0);
x_324 = lean_ctor_get(x_294, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_294);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_286);
lean_dec(x_280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_326 = !lean_is_exclusive(x_288);
if (x_326 == 0)
{
return x_288;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_288, 0);
x_328 = lean_ctor_get(x_288, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_288);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
else
{
uint8_t x_330; 
lean_dec(x_280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_330 = !lean_is_exclusive(x_285);
if (x_330 == 0)
{
return x_285;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_285, 0);
x_332 = lean_ctor_get(x_285, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_285);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_nat_sub(x_281, x_180);
lean_dec(x_180);
lean_dec(x_281);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_335 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_280, x_334, x_3, x_4, x_5, x_6, x_279);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_338 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = l_Lean_Meta_isDefEqOffset___closed__2;
x_342 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_342, 0, x_339);
lean_closure_set(x_342, 1, x_341);
x_343 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_344 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_342, x_343, x_3, x_4, x_5, x_6, x_340);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; uint8_t x_346; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_unbox(x_345);
lean_dec(x_345);
if (x_346 == 0)
{
uint8_t x_347; 
lean_dec(x_336);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_347 = !lean_is_exclusive(x_344);
if (x_347 == 0)
{
lean_object* x_348; uint8_t x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_344, 0);
lean_dec(x_348);
x_349 = 2;
x_350 = lean_box(x_349);
lean_ctor_set(x_344, 0, x_350);
return x_344;
}
else
{
lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; 
x_351 = lean_ctor_get(x_344, 1);
lean_inc(x_351);
lean_dec(x_344);
x_352 = 2;
x_353 = lean_box(x_352);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_351);
return x_354;
}
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_344, 1);
lean_inc(x_355);
lean_dec(x_344);
x_356 = lean_is_expr_def_eq(x_179, x_336, x_3, x_4, x_5, x_6, x_355);
if (lean_obj_tag(x_356) == 0)
{
uint8_t x_357; 
x_357 = !lean_is_exclusive(x_356);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; uint8_t x_360; lean_object* x_361; 
x_358 = lean_ctor_get(x_356, 0);
x_359 = lean_unbox(x_358);
lean_dec(x_358);
x_360 = l_Bool_toLBool(x_359);
x_361 = lean_box(x_360);
lean_ctor_set(x_356, 0, x_361);
return x_356;
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_365; lean_object* x_366; lean_object* x_367; 
x_362 = lean_ctor_get(x_356, 0);
x_363 = lean_ctor_get(x_356, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_356);
x_364 = lean_unbox(x_362);
lean_dec(x_362);
x_365 = l_Bool_toLBool(x_364);
x_366 = lean_box(x_365);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_363);
return x_367;
}
}
else
{
uint8_t x_368; 
x_368 = !lean_is_exclusive(x_356);
if (x_368 == 0)
{
return x_356;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_356, 0);
x_370 = lean_ctor_get(x_356, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_356);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
}
else
{
uint8_t x_372; 
lean_dec(x_336);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_372 = !lean_is_exclusive(x_344);
if (x_372 == 0)
{
return x_344;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_344, 0);
x_374 = lean_ctor_get(x_344, 1);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_344);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
return x_375;
}
}
}
else
{
uint8_t x_376; 
lean_dec(x_336);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_376 = !lean_is_exclusive(x_338);
if (x_376 == 0)
{
return x_338;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_338, 0);
x_378 = lean_ctor_get(x_338, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_338);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
}
else
{
uint8_t x_380; 
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_380 = !lean_is_exclusive(x_335);
if (x_380 == 0)
{
return x_335;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_335, 0);
x_382 = lean_ctor_get(x_335, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_335);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
}
else
{
lean_object* x_384; 
lean_dec(x_281);
lean_dec(x_180);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_384 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_279);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = l_Lean_Meta_isDefEqOffset___closed__2;
x_388 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_388, 0, x_385);
lean_closure_set(x_388, 1, x_387);
x_389 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_390 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_388, x_389, x_3, x_4, x_5, x_6, x_386);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; uint8_t x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_unbox(x_391);
lean_dec(x_391);
if (x_392 == 0)
{
uint8_t x_393; 
lean_dec(x_280);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_393 = !lean_is_exclusive(x_390);
if (x_393 == 0)
{
lean_object* x_394; uint8_t x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_390, 0);
lean_dec(x_394);
x_395 = 2;
x_396 = lean_box(x_395);
lean_ctor_set(x_390, 0, x_396);
return x_390;
}
else
{
lean_object* x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_390, 1);
lean_inc(x_397);
lean_dec(x_390);
x_398 = 2;
x_399 = lean_box(x_398);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_397);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_390, 1);
lean_inc(x_401);
lean_dec(x_390);
x_402 = lean_is_expr_def_eq(x_179, x_280, x_3, x_4, x_5, x_6, x_401);
if (lean_obj_tag(x_402) == 0)
{
uint8_t x_403; 
x_403 = !lean_is_exclusive(x_402);
if (x_403 == 0)
{
lean_object* x_404; uint8_t x_405; uint8_t x_406; lean_object* x_407; 
x_404 = lean_ctor_get(x_402, 0);
x_405 = lean_unbox(x_404);
lean_dec(x_404);
x_406 = l_Bool_toLBool(x_405);
x_407 = lean_box(x_406);
lean_ctor_set(x_402, 0, x_407);
return x_402;
}
else
{
lean_object* x_408; lean_object* x_409; uint8_t x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; 
x_408 = lean_ctor_get(x_402, 0);
x_409 = lean_ctor_get(x_402, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_402);
x_410 = lean_unbox(x_408);
lean_dec(x_408);
x_411 = l_Bool_toLBool(x_410);
x_412 = lean_box(x_411);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_409);
return x_413;
}
}
else
{
uint8_t x_414; 
x_414 = !lean_is_exclusive(x_402);
if (x_414 == 0)
{
return x_402;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_402, 0);
x_416 = lean_ctor_get(x_402, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_402);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
}
else
{
uint8_t x_418; 
lean_dec(x_280);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_418 = !lean_is_exclusive(x_390);
if (x_418 == 0)
{
return x_390;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_390, 0);
x_420 = lean_ctor_get(x_390, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_390);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
uint8_t x_422; 
lean_dec(x_280);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_422 = !lean_is_exclusive(x_384);
if (x_422 == 0)
{
return x_384;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_384, 0);
x_424 = lean_ctor_get(x_384, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_384);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_426 = !lean_is_exclusive(x_181);
if (x_426 == 0)
{
return x_181;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_181, 0);
x_428 = lean_ctor_get(x_181, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_181);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_430 = !lean_is_exclusive(x_20);
if (x_430 == 0)
{
return x_20;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_20, 0);
x_432 = lean_ctor_get(x_20, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_20);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
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
