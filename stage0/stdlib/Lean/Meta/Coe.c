// Lean compiler output
// Module: Lean.Meta.Coe
// Imports: Init Lean.Meta.WHNF Lean.Meta.Transform Lean.Meta.SynthInstance Lean.Meta.AppBuilder
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
static lean_object* l_Lean_Meta_expandCoe___lambda__1___closed__1;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__7;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__3;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__9;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__11;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__8;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__2;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__1;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__7;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__17;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__6;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__10;
uint8_t l_Lean_Expr_isSort(lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__3;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__6;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290_(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__2;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__1;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__15;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__5;
static lean_object* l_Lean_Meta_expandCoe___closed__1;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__10;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__14;
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__8;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__4;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__1;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__4;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__9;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_autoLift;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__8;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__1;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__6;
static lean_object* l_Lean_Meta_expandCoe___lambda__2___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__12;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__13;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__7;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__6;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__2;
static lean_object* l_Lean_Meta_expandCoe___closed__2;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coe_decl", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coeDeclAttr", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("auxiliary definition used to implement coercion (unfolded during elaboration)", 77);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__7;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__8;
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__6;
x_6 = 0;
x_7 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_coeDeclAttr;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_isCoeDecl___closed__1;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_isCoeDecl(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_expandCoe___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_expandCoe___lambda__1___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_expandCoe___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_expandCoe___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Expr_getAppFn(x_1);
x_8 = l_Lean_Meta_expandCoe___lambda__2___closed__1;
x_9 = l_Lean_Expr_isConst(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_6(x_8, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = l_Lean_Expr_constName_x21(x_7);
lean_dec(x_7);
x_13 = lean_st_ref_get(x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_isCoeDecl___closed__1;
x_18 = l_Lean_TagAttribute_hasTag(x_17, x_16, x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_apply_6(x_8, x_19, x_2, x_3, x_4, x_5, x_15);
return x_20;
}
else
{
lean_object* x_21; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_apply_6(x_8, x_24, x_2, x_3, x_4, x_5, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Expr_headBeta(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
lean_dec(x_22);
x_33 = l_Lean_Expr_headBeta(x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_expandCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_expandCoe___lambda__2), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_expandCoe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_expandCoe___lambda__3___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = 3;
lean_ctor_set_uint8(x_8, 9, x_10);
x_11 = l_Lean_Meta_expandCoe___closed__1;
x_12 = l_Lean_Meta_expandCoe___closed__2;
x_13 = 0;
x_14 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_11, x_12, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_23 = lean_ctor_get_uint8(x_8, 0);
x_24 = lean_ctor_get_uint8(x_8, 1);
x_25 = lean_ctor_get_uint8(x_8, 2);
x_26 = lean_ctor_get_uint8(x_8, 3);
x_27 = lean_ctor_get_uint8(x_8, 4);
x_28 = lean_ctor_get_uint8(x_8, 5);
x_29 = lean_ctor_get_uint8(x_8, 6);
x_30 = lean_ctor_get_uint8(x_8, 7);
x_31 = lean_ctor_get_uint8(x_8, 8);
x_32 = lean_ctor_get_uint8(x_8, 10);
x_33 = lean_ctor_get_uint8(x_8, 11);
lean_dec(x_8);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_35, 0, x_23);
lean_ctor_set_uint8(x_35, 1, x_24);
lean_ctor_set_uint8(x_35, 2, x_25);
lean_ctor_set_uint8(x_35, 3, x_26);
lean_ctor_set_uint8(x_35, 4, x_27);
lean_ctor_set_uint8(x_35, 5, x_28);
lean_ctor_set_uint8(x_35, 6, x_29);
lean_ctor_set_uint8(x_35, 7, x_30);
lean_ctor_set_uint8(x_35, 8, x_31);
lean_ctor_set_uint8(x_35, 9, x_34);
lean_ctor_set_uint8(x_35, 10, x_32);
lean_ctor_set_uint8(x_35, 11, x_33);
lean_ctor_set(x_2, 0, x_35);
x_36 = l_Lean_Meta_expandCoe___closed__1;
x_37 = l_Lean_Meta_expandCoe___closed__2;
x_38 = 0;
x_39 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_36, x_37, x_38, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_46 = x_39;
} else {
 lean_dec_ref(x_39);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_ctor_get(x_2, 3);
x_52 = lean_ctor_get(x_2, 4);
x_53 = lean_ctor_get(x_2, 5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_2);
x_54 = lean_ctor_get_uint8(x_48, 0);
x_55 = lean_ctor_get_uint8(x_48, 1);
x_56 = lean_ctor_get_uint8(x_48, 2);
x_57 = lean_ctor_get_uint8(x_48, 3);
x_58 = lean_ctor_get_uint8(x_48, 4);
x_59 = lean_ctor_get_uint8(x_48, 5);
x_60 = lean_ctor_get_uint8(x_48, 6);
x_61 = lean_ctor_get_uint8(x_48, 7);
x_62 = lean_ctor_get_uint8(x_48, 8);
x_63 = lean_ctor_get_uint8(x_48, 10);
x_64 = lean_ctor_get_uint8(x_48, 11);
if (lean_is_exclusive(x_48)) {
 x_65 = x_48;
} else {
 lean_dec_ref(x_48);
 x_65 = lean_box(0);
}
x_66 = 3;
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 0, 12);
} else {
 x_67 = x_65;
}
lean_ctor_set_uint8(x_67, 0, x_54);
lean_ctor_set_uint8(x_67, 1, x_55);
lean_ctor_set_uint8(x_67, 2, x_56);
lean_ctor_set_uint8(x_67, 3, x_57);
lean_ctor_set_uint8(x_67, 4, x_58);
lean_ctor_set_uint8(x_67, 5, x_59);
lean_ctor_set_uint8(x_67, 6, x_60);
lean_ctor_set_uint8(x_67, 7, x_61);
lean_ctor_set_uint8(x_67, 8, x_62);
lean_ctor_set_uint8(x_67, 9, x_66);
lean_ctor_set_uint8(x_67, 10, x_63);
lean_ctor_set_uint8(x_67, 11, x_64);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_49);
lean_ctor_set(x_68, 2, x_50);
lean_ctor_set(x_68, 3, x_51);
lean_ctor_set(x_68, 4, x_52);
lean_ctor_set(x_68, 5, x_53);
x_69 = l_Lean_Meta_expandCoe___closed__1;
x_70 = l_Lean_Meta_expandCoe___closed__2;
x_71 = 0;
x_72 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_69, x_70, x_71, x_68, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_expandCoe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_expandCoe___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("autoLift", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("insert monadic lifts (i.e., `liftM` and coercions) when needed", 62);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeT", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coe", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__1;
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("could not coerce", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nto", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\ncoerced expression has wrong type:", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Meta_getLevel(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_coerceSimple_x3f___closed__2;
lean_inc(x_19);
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_9);
x_23 = lean_array_push(x_22, x_9);
lean_inc(x_1);
x_24 = lean_array_push(x_23, x_1);
lean_inc(x_2);
x_25 = lean_array_push(x_24, x_2);
x_26 = l_Lean_mkAppN(x_21, x_25);
x_27 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Meta_trySynthInstance(x_26, x_27, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = l_Lean_Meta_coerceSimple_x3f___closed__5;
x_39 = l_Lean_Expr_const___override(x_38, x_19);
x_40 = l_Lean_Meta_coerceSimple_x3f___closed__6;
x_41 = lean_array_push(x_40, x_9);
lean_inc(x_1);
x_42 = lean_array_push(x_41, x_1);
lean_inc(x_2);
x_43 = lean_array_push(x_42, x_2);
x_44 = lean_array_push(x_43, x_37);
x_45 = l_Lean_mkAppN(x_39, x_44);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_Lean_Meta_expandCoe(x_45, x_3, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_47);
x_49 = lean_infer_type(x_47, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l_Lean_Meta_isExprDefEq(x_50, x_2, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_indentExpr(x_1);
x_57 = l_Lean_Meta_coerceSimple_x3f___closed__8;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Meta_coerceSimple_x3f___closed__10;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_indentExpr(x_2);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_coerceSimple_x3f___closed__12;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_indentExpr(x_47);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_coerceSimple_x3f___closed__13;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_68, x_3, x_4, x_5, x_6, x_55);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
return x_69;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_69);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_ctor_get(x_52, 1);
lean_inc(x_74);
lean_dec(x_52);
x_75 = lean_box(0);
x_76 = l_Lean_Meta_coerceSimple_x3f___lambda__1(x_47, x_75, x_3, x_4, x_5, x_6, x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_52);
if (x_77 == 0)
{
return x_52;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_52, 0);
x_79 = lean_ctor_get(x_52, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_52);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_49);
if (x_81 == 0)
{
return x_49;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_49, 0);
x_83 = lean_ctor_get(x_49, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_49);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_46);
if (x_85 == 0)
{
return x_46;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_46, 0);
x_87 = lean_ctor_get(x_46, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_46);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
default: 
{
uint8_t x_89; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_28);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_28, 0);
lean_dec(x_90);
x_91 = lean_box(2);
lean_ctor_set(x_28, 0, x_91);
return x_28;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_28, 1);
lean_inc(x_92);
lean_dec(x_28);
x_93 = lean_box(2);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_28);
if (x_95 == 0)
{
return x_28;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_28, 0);
x_97 = lean_ctor_get(x_28, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_28);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_14);
if (x_99 == 0)
{
return x_14;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_14, 0);
x_101 = lean_ctor_get(x_14, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_14);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_11);
if (x_103 == 0)
{
return x_11;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_11, 0);
x_105 = lean_ctor_get(x_11, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_11);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_8);
if (x_107 == 0)
{
return x_8;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_8, 0);
x_109 = lean_ctor_get(x_8, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_8);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_coerceSimple_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeFun", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_coerceToFunction_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_coerceToFunction_x3f___closed__1;
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to coerce", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToFunction_x3f___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nto a function, after applying `CoeFun.coe`, result is still not a function", 75);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToFunction_x3f___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nthis is often due to incorrect `CoeFun` instances, the synthesized instance was", 80);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToFunction_x3f___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_10 = l_Lean_Meta_getLevel(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Expr_sort___override(x_14);
lean_inc(x_8);
x_17 = l_Lean_mkArrow(x_8, x_16, x_4, x_5, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = 0;
x_22 = lean_box(0);
lean_inc(x_2);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_20, x_21, x_22, x_2, x_3, x_4, x_5, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_coerceToFunction_x3f___closed__2;
lean_inc(x_28);
x_30 = l_Lean_Expr_const___override(x_29, x_28);
lean_inc(x_24);
lean_inc(x_8);
x_31 = l_Lean_mkAppB(x_30, x_8, x_24);
x_32 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_Meta_trySynthInstance(x_31, x_32, x_2, x_3, x_4, x_5, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_coerceToFunction_x3f___closed__3;
x_38 = l_Lean_Expr_const___override(x_37, x_28);
lean_inc(x_1);
lean_inc(x_36);
x_39 = l_Lean_mkApp4(x_38, x_8, x_24, x_36, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_40 = l_Lean_Meta_expandCoe(x_39, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_41);
x_43 = lean_infer_type(x_41, x_2, x_3, x_4, x_5, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_46 = lean_whnf(x_44, x_2, x_3, x_4, x_5, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_isForall(x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_50 = l_Lean_indentExpr(x_1);
x_51 = l_Lean_Meta_coerceToFunction_x3f___closed__5;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Meta_coerceToFunction_x3f___closed__7;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_indentExpr(x_41);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_coerceToFunction_x3f___closed__9;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_indentExpr(x_36);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Meta_coerceSimple_x3f___closed__13;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_62, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_36);
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_41, x_68, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_46);
if (x_70 == 0)
{
return x_46;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_46, 0);
x_72 = lean_ctor_get(x_46, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_46);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_43);
if (x_74 == 0)
{
return x_43;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_43, 0);
x_76 = lean_ctor_get(x_43, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_43);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_40);
if (x_78 == 0)
{
return x_40;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_40, 0);
x_80 = lean_ctor_get(x_40, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_40);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_33);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_33, 0);
lean_dec(x_83);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_33, 1);
lean_inc(x_84);
lean_dec(x_33);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_32);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_33);
if (x_86 == 0)
{
return x_33;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_33, 0);
x_88 = lean_ctor_get(x_33, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_33);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_10);
if (x_90 == 0)
{
return x_10;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_10, 0);
x_92 = lean_ctor_get(x_10, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_10);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_7);
if (x_94 == 0)
{
return x_7;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_7, 0);
x_96 = lean_ctor_get(x_7, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_7);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeSort", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_coerceToSort_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_coerceToSort_x3f___closed__1;
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nto a type, after applying `CoeSort.coe`, result is still not a type", 68);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToSort_x3f___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nthis is often due to incorrect `CoeSort` instances, the synthesized instance was", 81);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToSort_x3f___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_10 = l_Lean_Meta_getLevel(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Expr_sort___override(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = 0;
x_19 = lean_box(0);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_17, x_18, x_19, x_2, x_3, x_4, x_5, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_coerceToSort_x3f___closed__2;
lean_inc(x_25);
x_27 = l_Lean_Expr_const___override(x_26, x_25);
lean_inc(x_21);
lean_inc(x_8);
x_28 = l_Lean_mkAppB(x_27, x_8, x_21);
x_29 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = l_Lean_Meta_trySynthInstance(x_28, x_29, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_coerceToSort_x3f___closed__3;
x_35 = l_Lean_Expr_const___override(x_34, x_25);
lean_inc(x_1);
lean_inc(x_33);
x_36 = l_Lean_mkApp4(x_35, x_8, x_21, x_33, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_Meta_expandCoe(x_36, x_2, x_3, x_4, x_5, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_38);
x_40 = lean_infer_type(x_38, x_2, x_3, x_4, x_5, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = lean_whnf(x_41, x_2, x_3, x_4, x_5, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Expr_isSort(x_44);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_47 = l_Lean_indentExpr(x_1);
x_48 = l_Lean_Meta_coerceToFunction_x3f___closed__5;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_coerceToSort_x3f___closed__5;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_indentExpr(x_38);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_coerceToSort_x3f___closed__7;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_indentExpr(x_33);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_coerceSimple_x3f___closed__13;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_59, x_2, x_3, x_4, x_5, x_45);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_33);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_38, x_65, x_2, x_3, x_4, x_5, x_45);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_43);
if (x_67 == 0)
{
return x_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_43, 0);
x_69 = lean_ctor_get(x_43, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_43);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_40);
if (x_71 == 0)
{
return x_40;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_40, 0);
x_73 = lean_ctor_get(x_40, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_40);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_37);
if (x_75 == 0)
{
return x_37;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_37, 0);
x_77 = lean_ctor_get(x_37, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_37);
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
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_30);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_30, 0);
lean_dec(x_80);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_30, 1);
lean_inc(x_81);
lean_dec(x_30);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_29);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_30);
if (x_83 == 0)
{
return x_30;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_30, 0);
x_85 = lean_ctor_get(x_30, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_30);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_10);
if (x_87 == 0)
{
return x_10;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_10, 0);
x_89 = lean_ctor_get(x_10, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_10);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_7);
if (x_91 == 0)
{
return x_7;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_7, 0);
x_93 = lean_ctor_get(x_7, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_7);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 2;
lean_ctor_set_uint8(x_7, 9, x_14);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_whnf(x_1, x_15, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_19, x_2, x_3, x_4, x_5, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_20, x_2, x_3, x_4, x_5, x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_16, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_16, 0, x_36);
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = lean_ctor_get_uint8(x_7, 0);
x_45 = lean_ctor_get_uint8(x_7, 1);
x_46 = lean_ctor_get_uint8(x_7, 2);
x_47 = lean_ctor_get_uint8(x_7, 3);
x_48 = lean_ctor_get_uint8(x_7, 4);
x_49 = lean_ctor_get_uint8(x_7, 5);
x_50 = lean_ctor_get_uint8(x_7, 6);
x_51 = lean_ctor_get_uint8(x_7, 7);
x_52 = lean_ctor_get_uint8(x_7, 8);
x_53 = lean_ctor_get_uint8(x_7, 10);
x_54 = lean_ctor_get_uint8(x_7, 11);
lean_dec(x_7);
x_55 = 2;
x_56 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_56, 0, x_44);
lean_ctor_set_uint8(x_56, 1, x_45);
lean_ctor_set_uint8(x_56, 2, x_46);
lean_ctor_set_uint8(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, 4, x_48);
lean_ctor_set_uint8(x_56, 5, x_49);
lean_ctor_set_uint8(x_56, 6, x_50);
lean_ctor_set_uint8(x_56, 7, x_51);
lean_ctor_set_uint8(x_56, 8, x_52);
lean_ctor_set_uint8(x_56, 9, x_55);
lean_ctor_set_uint8(x_56, 10, x_53);
lean_ctor_set_uint8(x_56, 11, x_54);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
lean_ctor_set(x_57, 2, x_9);
lean_ctor_set(x_57, 3, x_10);
lean_ctor_set(x_57, 4, x_11);
lean_ctor_set(x_57, 5, x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = lean_whnf(x_1, x_57, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 5)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_61, x_2, x_3, x_4, x_5, x_60);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_62, x_2, x_3, x_4, x_5, x_65);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_67);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_58, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_74 = x_58;
} else {
 lean_dec_ref(x_58);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_ctor_get(x_58, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_79 = x_58;
} else {
 lean_dec_ref(x_58);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_isTypeApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_isMonad_x3f(x_19, x_2, x_3, x_4, x_5, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
lean_dec(x_31);
x_32 = 1;
x_33 = lean_box(x_32);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
return x_7;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_autoLift;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("MonadLiftT", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("liftM", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Internal", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("liftCoeM", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_3 = l_Lean_Meta_coerceMonadLift_x3f___closed__12;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coeM", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_3 = l_Lean_Meta_coerceMonadLift_x3f___closed__15;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_12, x_3, x_4, x_5, x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_17 = l_Lean_Meta_isTypeApp_x3f(x_9, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
x_30 = l_Lean_Meta_isTypeApp_x3f(x_15, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
lean_inc(x_41);
x_43 = l_Lean_Meta_isExprDefEq(x_41, x_28, x_3, x_4, x_5, x_6, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
lean_free_object(x_18);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_43, 1);
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_5, 2);
lean_inc(x_49);
x_50 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_51 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_49, x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_box(0);
lean_ctor_set(x_43, 0, x_52);
return x_43;
}
else
{
lean_object* x_53; 
lean_free_object(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_53 = lean_infer_type(x_41, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_56 = lean_whnf(x_54, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 7)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 3)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 2);
lean_inc(x_59);
lean_dec(x_57);
if (lean_obj_tag(x_59) == 3)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_63 = lean_infer_type(x_28, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_66 = lean_whnf(x_64, x_3, x_4, x_5, x_6, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 7)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 3)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 2);
lean_inc(x_69);
lean_dec(x_67);
if (lean_obj_tag(x_69) == 3)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
lean_dec(x_69);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_73 = l_Lean_Meta_decLevel(x_61, x_3, x_4, x_5, x_6, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_76 = l_Lean_Meta_decLevel(x_71, x_3, x_4, x_5, x_6, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_74);
x_80 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_74, x_77, x_79, x_3, x_4, x_5, x_6, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_62);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_80, 0);
lean_dec(x_84);
x_85 = lean_box(0);
lean_ctor_set(x_80, 0, x_85);
return x_80;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_dec(x_80);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
lean_dec(x_80);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_90 = l_Lean_Meta_decLevel(x_62, x_3, x_4, x_5, x_6, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_93 = l_Lean_Meta_decLevel(x_72, x_3, x_4, x_5, x_6, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_91);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_74);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_101 = l_Lean_Expr_const___override(x_100, x_99);
x_102 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_41);
x_103 = lean_array_push(x_102, x_41);
lean_inc(x_28);
x_104 = lean_array_push(x_103, x_28);
x_105 = l_Lean_mkAppN(x_101, x_104);
x_106 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_Meta_trySynthInstance(x_105, x_106, x_3, x_4, x_5, x_6, x_95);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 1)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_111 = l_Lean_Meta_getDecLevel(x_42, x_3, x_4, x_5, x_6, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_114 = l_Lean_Meta_getDecLevel(x_15, x_3, x_4, x_5, x_6, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_117 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_96);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_112);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_122);
x_124 = l_Lean_Expr_const___override(x_123, x_122);
x_125 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_41);
x_126 = lean_array_push(x_125, x_41);
lean_inc(x_28);
x_127 = lean_array_push(x_126, x_28);
lean_inc(x_110);
x_128 = lean_array_push(x_127, x_110);
lean_inc(x_42);
x_129 = lean_array_push(x_128, x_42);
lean_inc(x_1);
x_130 = lean_array_push(x_129, x_1);
x_131 = l_Lean_mkAppN(x_124, x_130);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_131);
x_132 = lean_infer_type(x_131, x_3, x_4, x_5, x_6, x_119);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_135 = l_Lean_Meta_isExprDefEq(x_9, x_133, x_3, x_4, x_5, x_6, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_131);
lean_free_object(x_31);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_139 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_139);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_139, 0);
lean_dec(x_142);
lean_ctor_set(x_139, 0, x_106);
return x_139;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_106);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_dec(x_139);
x_146 = lean_ctor_get(x_140, 0);
lean_inc(x_146);
lean_dec(x_140);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_147 = l_Lean_Meta_getLevel(x_42, x_3, x_4, x_5, x_6, x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_150 = l_Lean_Meta_getLevel(x_29, x_3, x_4, x_5, x_6, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_96);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_156 = l_Lean_Expr_const___override(x_155, x_154);
x_157 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_42);
x_158 = lean_array_push(x_157, x_42);
x_159 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_160 = lean_array_push(x_158, x_159);
lean_inc(x_29);
x_161 = lean_array_push(x_160, x_29);
x_162 = l_Lean_mkAppN(x_156, x_161);
x_163 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_164 = 0;
lean_inc(x_42);
x_165 = l_Lean_Expr_forallE___override(x_163, x_42, x_162, x_164);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_166 = l_Lean_Meta_trySynthInstance(x_165, x_106, x_3, x_4, x_5, x_6, x_152);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 1)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_171 = l_Lean_Expr_const___override(x_170, x_122);
x_172 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_173 = lean_array_push(x_172, x_41);
x_174 = lean_array_push(x_173, x_28);
x_175 = lean_array_push(x_174, x_42);
x_176 = lean_array_push(x_175, x_29);
x_177 = lean_array_push(x_176, x_110);
x_178 = lean_array_push(x_177, x_169);
x_179 = lean_array_push(x_178, x_146);
x_180 = lean_array_push(x_179, x_1);
x_181 = l_Lean_mkAppN(x_171, x_180);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_182 = l_Lean_Meta_expandCoe(x_181, x_3, x_4, x_5, x_6, x_168);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_183);
x_185 = lean_infer_type(x_183, x_3, x_4, x_5, x_6, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_188 = l_Lean_Meta_isExprDefEq(x_9, x_186, x_3, x_4, x_5, x_6, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
uint8_t x_191; 
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_191 = !lean_is_exclusive(x_188);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_188, 0);
lean_dec(x_192);
lean_ctor_set(x_188, 0, x_106);
return x_188;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
lean_dec(x_188);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_106);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
lean_dec(x_188);
x_196 = lean_box(0);
x_197 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_183, x_196, x_3, x_4, x_5, x_6, x_195);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
return x_197;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_197);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_202 = !lean_is_exclusive(x_188);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_188, 0);
lean_dec(x_203);
lean_ctor_set_tag(x_188, 0);
lean_ctor_set(x_188, 0, x_106);
return x_188;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_188, 1);
lean_inc(x_204);
lean_dec(x_188);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_106);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_183);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = !lean_is_exclusive(x_185);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_185, 0);
lean_dec(x_207);
lean_ctor_set_tag(x_185, 0);
lean_ctor_set(x_185, 0, x_106);
return x_185;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_185, 1);
lean_inc(x_208);
lean_dec(x_185);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_106);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_210 = !lean_is_exclusive(x_182);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_182, 0);
lean_dec(x_211);
lean_ctor_set_tag(x_182, 0);
lean_ctor_set(x_182, 0, x_106);
return x_182;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_182, 1);
lean_inc(x_212);
lean_dec(x_182);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_106);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_167);
lean_dec(x_146);
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_166);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_166, 0);
lean_dec(x_215);
lean_ctor_set(x_166, 0, x_106);
return x_166;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_166, 1);
lean_inc(x_216);
lean_dec(x_166);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_106);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_146);
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_166);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_166, 0);
lean_dec(x_219);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 0, x_106);
return x_166;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_166, 1);
lean_inc(x_220);
lean_dec(x_166);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_106);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_150);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_150, 0);
lean_dec(x_223);
lean_ctor_set_tag(x_150, 0);
lean_ctor_set(x_150, 0, x_106);
return x_150;
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_150, 1);
lean_inc(x_224);
lean_dec(x_150);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_106);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_146);
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_147);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_147, 0);
lean_dec(x_227);
lean_ctor_set_tag(x_147, 0);
lean_ctor_set(x_147, 0, x_106);
return x_147;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_147, 1);
lean_inc(x_228);
lean_dec(x_147);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_106);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_135);
if (x_230 == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_135, 0);
lean_dec(x_231);
lean_ctor_set(x_31, 0, x_131);
lean_ctor_set(x_135, 0, x_31);
return x_135;
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_135, 1);
lean_inc(x_232);
lean_dec(x_135);
lean_ctor_set(x_31, 0, x_131);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_31);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_131);
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_135);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_135, 0);
lean_dec(x_235);
lean_ctor_set_tag(x_135, 0);
lean_ctor_set(x_135, 0, x_106);
return x_135;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_135, 1);
lean_inc(x_236);
lean_dec(x_135);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_106);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_131);
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_132);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_132, 0);
lean_dec(x_239);
lean_ctor_set_tag(x_132, 0);
lean_ctor_set(x_132, 0, x_106);
return x_132;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_132, 1);
lean_inc(x_240);
lean_dec(x_132);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_106);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_117);
if (x_242 == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_117, 0);
lean_dec(x_243);
lean_ctor_set_tag(x_117, 0);
lean_ctor_set(x_117, 0, x_106);
return x_117;
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_117, 1);
lean_inc(x_244);
lean_dec(x_117);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_106);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_114);
if (x_246 == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_114, 0);
lean_dec(x_247);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 0, x_106);
return x_114;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_114, 1);
lean_inc(x_248);
lean_dec(x_114);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_106);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_110);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_111);
if (x_250 == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_111, 0);
lean_dec(x_251);
lean_ctor_set_tag(x_111, 0);
lean_ctor_set(x_111, 0, x_106);
return x_111;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_111, 1);
lean_inc(x_252);
lean_dec(x_111);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_106);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_108);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_107);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_107, 0);
lean_dec(x_255);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
else
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_107, 1);
lean_inc(x_256);
lean_dec(x_107);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_106);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_107);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_107, 0);
lean_dec(x_259);
lean_ctor_set_tag(x_107, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_107, 1);
lean_inc(x_260);
lean_dec(x_107);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_106);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_91);
lean_dec(x_74);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_93);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_93, 0);
lean_dec(x_263);
x_264 = lean_box(0);
lean_ctor_set_tag(x_93, 0);
lean_ctor_set(x_93, 0, x_264);
return x_93;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_93, 1);
lean_inc(x_265);
lean_dec(x_93);
x_266 = lean_box(0);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_90);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_90, 0);
lean_dec(x_269);
x_270 = lean_box(0);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 0, x_270);
return x_90;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_90, 1);
lean_inc(x_271);
lean_dec(x_90);
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_62);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_80);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_80, 0);
lean_dec(x_275);
x_276 = lean_box(0);
lean_ctor_set_tag(x_80, 0);
lean_ctor_set(x_80, 0, x_276);
return x_80;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_80, 1);
lean_inc(x_277);
lean_dec(x_80);
x_278 = lean_box(0);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_62);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_280 = !lean_is_exclusive(x_76);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_76, 0);
lean_dec(x_281);
x_282 = lean_box(0);
lean_ctor_set_tag(x_76, 0);
lean_ctor_set(x_76, 0, x_282);
return x_76;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_76, 1);
lean_inc(x_283);
lean_dec(x_76);
x_284 = lean_box(0);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_62);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_286 = !lean_is_exclusive(x_73);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_73, 0);
lean_dec(x_287);
x_288 = lean_box(0);
lean_ctor_set_tag(x_73, 0);
lean_ctor_set(x_73, 0, x_288);
return x_73;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_73, 1);
lean_inc(x_289);
lean_dec(x_73);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_66);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_66, 0);
lean_dec(x_293);
x_294 = lean_box(0);
lean_ctor_set(x_66, 0, x_294);
return x_66;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_66, 1);
lean_inc(x_295);
lean_dec(x_66);
x_296 = lean_box(0);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_66);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_66, 0);
lean_dec(x_299);
x_300 = lean_box(0);
lean_ctor_set(x_66, 0, x_300);
return x_66;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_66, 1);
lean_inc(x_301);
lean_dec(x_66);
x_302 = lean_box(0);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
}
else
{
uint8_t x_304; 
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_304 = !lean_is_exclusive(x_66);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_66, 0);
lean_dec(x_305);
x_306 = lean_box(0);
lean_ctor_set(x_66, 0, x_306);
return x_66;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_66, 1);
lean_inc(x_307);
lean_dec(x_66);
x_308 = lean_box(0);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_66);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_66, 0);
lean_dec(x_311);
x_312 = lean_box(0);
lean_ctor_set_tag(x_66, 0);
lean_ctor_set(x_66, 0, x_312);
return x_66;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_66, 1);
lean_inc(x_313);
lean_dec(x_66);
x_314 = lean_box(0);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
}
else
{
uint8_t x_316; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_316 = !lean_is_exclusive(x_63);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_63, 0);
lean_dec(x_317);
x_318 = lean_box(0);
lean_ctor_set_tag(x_63, 0);
lean_ctor_set(x_63, 0, x_318);
return x_63;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_63, 1);
lean_inc(x_319);
lean_dec(x_63);
x_320 = lean_box(0);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_56);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_56, 0);
lean_dec(x_323);
x_324 = lean_box(0);
lean_ctor_set(x_56, 0, x_324);
return x_56;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_56, 1);
lean_inc(x_325);
lean_dec(x_56);
x_326 = lean_box(0);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_328 = !lean_is_exclusive(x_56);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_56, 0);
lean_dec(x_329);
x_330 = lean_box(0);
lean_ctor_set(x_56, 0, x_330);
return x_56;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_56, 1);
lean_inc(x_331);
lean_dec(x_56);
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
}
else
{
uint8_t x_334; 
lean_dec(x_57);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_334 = !lean_is_exclusive(x_56);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_56, 0);
lean_dec(x_335);
x_336 = lean_box(0);
lean_ctor_set(x_56, 0, x_336);
return x_56;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_56, 1);
lean_inc(x_337);
lean_dec(x_56);
x_338 = lean_box(0);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_340 = !lean_is_exclusive(x_56);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_56, 0);
lean_dec(x_341);
x_342 = lean_box(0);
lean_ctor_set_tag(x_56, 0);
lean_ctor_set(x_56, 0, x_342);
return x_56;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_56, 1);
lean_inc(x_343);
lean_dec(x_56);
x_344 = lean_box(0);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
}
else
{
uint8_t x_346; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_346 = !lean_is_exclusive(x_53);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_53, 0);
lean_dec(x_347);
x_348 = lean_box(0);
lean_ctor_set_tag(x_53, 0);
lean_ctor_set(x_53, 0, x_348);
return x_53;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_53, 1);
lean_inc(x_349);
lean_dec(x_53);
x_350 = lean_box(0);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_352 = lean_ctor_get(x_43, 1);
lean_inc(x_352);
lean_dec(x_43);
x_353 = lean_ctor_get(x_5, 2);
lean_inc(x_353);
x_354 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_355 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_353, x_354);
lean_dec(x_353);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_356 = lean_box(0);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_352);
return x_357;
}
else
{
lean_object* x_358; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_358 = lean_infer_type(x_41, x_3, x_4, x_5, x_6, x_352);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_361 = lean_whnf(x_359, x_3, x_4, x_5, x_6, x_360);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_obj_tag(x_362) == 7)
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
if (lean_obj_tag(x_363) == 3)
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_362, 2);
lean_inc(x_364);
lean_dec(x_362);
if (lean_obj_tag(x_364) == 3)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_361, 1);
lean_inc(x_365);
lean_dec(x_361);
x_366 = lean_ctor_get(x_363, 0);
lean_inc(x_366);
lean_dec(x_363);
x_367 = lean_ctor_get(x_364, 0);
lean_inc(x_367);
lean_dec(x_364);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_368 = lean_infer_type(x_28, x_3, x_4, x_5, x_6, x_365);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_371 = lean_whnf(x_369, x_3, x_4, x_5, x_6, x_370);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 7)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 3)
{
lean_object* x_374; 
x_374 = lean_ctor_get(x_372, 2);
lean_inc(x_374);
lean_dec(x_372);
if (lean_obj_tag(x_374) == 3)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = lean_ctor_get(x_371, 1);
lean_inc(x_375);
lean_dec(x_371);
x_376 = lean_ctor_get(x_373, 0);
lean_inc(x_376);
lean_dec(x_373);
x_377 = lean_ctor_get(x_374, 0);
lean_inc(x_377);
lean_dec(x_374);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_378 = l_Lean_Meta_decLevel(x_366, x_3, x_4, x_5, x_6, x_375);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_381 = l_Lean_Meta_decLevel(x_376, x_3, x_4, x_5, x_6, x_380);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_384 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_379);
x_385 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_379, x_382, x_384, x_3, x_4, x_5, x_6, x_383);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; uint8_t x_387; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_unbox(x_386);
lean_dec(x_386);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_367);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_389 = x_385;
} else {
 lean_dec_ref(x_385);
 x_389 = lean_box(0);
}
x_390 = lean_box(0);
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_388);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_385, 1);
lean_inc(x_392);
lean_dec(x_385);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_393 = l_Lean_Meta_decLevel(x_367, x_3, x_4, x_5, x_6, x_392);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_396 = l_Lean_Meta_decLevel(x_377, x_3, x_4, x_5, x_6, x_395);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_box(0);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_394);
lean_ctor_set(x_401, 1, x_400);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_379);
lean_ctor_set(x_402, 1, x_401);
x_403 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_404 = l_Lean_Expr_const___override(x_403, x_402);
x_405 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_41);
x_406 = lean_array_push(x_405, x_41);
lean_inc(x_28);
x_407 = lean_array_push(x_406, x_28);
x_408 = l_Lean_mkAppN(x_404, x_407);
x_409 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_410 = l_Lean_Meta_trySynthInstance(x_408, x_409, x_3, x_4, x_5, x_6, x_398);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
if (lean_obj_tag(x_411) == 1)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_ctor_get(x_411, 0);
lean_inc(x_413);
lean_dec(x_411);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_414 = l_Lean_Meta_getDecLevel(x_42, x_3, x_4, x_5, x_6, x_412);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_417 = l_Lean_Meta_getDecLevel(x_15, x_3, x_4, x_5, x_6, x_416);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_420 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_399);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_418);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_415);
lean_ctor_set(x_425, 1, x_424);
x_426 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_425);
x_427 = l_Lean_Expr_const___override(x_426, x_425);
x_428 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_41);
x_429 = lean_array_push(x_428, x_41);
lean_inc(x_28);
x_430 = lean_array_push(x_429, x_28);
lean_inc(x_413);
x_431 = lean_array_push(x_430, x_413);
lean_inc(x_42);
x_432 = lean_array_push(x_431, x_42);
lean_inc(x_1);
x_433 = lean_array_push(x_432, x_1);
x_434 = l_Lean_mkAppN(x_427, x_433);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_434);
x_435 = lean_infer_type(x_434, x_3, x_4, x_5, x_6, x_422);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_438 = l_Lean_Meta_isExprDefEq(x_9, x_436, x_3, x_4, x_5, x_6, x_437);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; uint8_t x_440; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_unbox(x_439);
lean_dec(x_439);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_434);
lean_free_object(x_31);
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
lean_dec(x_438);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_442 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_441);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_445 = x_442;
} else {
 lean_dec_ref(x_442);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_409);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_442, 1);
lean_inc(x_447);
lean_dec(x_442);
x_448 = lean_ctor_get(x_443, 0);
lean_inc(x_448);
lean_dec(x_443);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_449 = l_Lean_Meta_getLevel(x_42, x_3, x_4, x_5, x_6, x_447);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_452 = l_Lean_Meta_getLevel(x_29, x_3, x_4, x_5, x_6, x_451);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_399);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_450);
lean_ctor_set(x_456, 1, x_455);
x_457 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_458 = l_Lean_Expr_const___override(x_457, x_456);
x_459 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_42);
x_460 = lean_array_push(x_459, x_42);
x_461 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_462 = lean_array_push(x_460, x_461);
lean_inc(x_29);
x_463 = lean_array_push(x_462, x_29);
x_464 = l_Lean_mkAppN(x_458, x_463);
x_465 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_466 = 0;
lean_inc(x_42);
x_467 = l_Lean_Expr_forallE___override(x_465, x_42, x_464, x_466);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_468 = l_Lean_Meta_trySynthInstance(x_467, x_409, x_3, x_4, x_5, x_6, x_454);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
if (lean_obj_tag(x_469) == 1)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = lean_ctor_get(x_469, 0);
lean_inc(x_471);
lean_dec(x_469);
x_472 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_473 = l_Lean_Expr_const___override(x_472, x_425);
x_474 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_475 = lean_array_push(x_474, x_41);
x_476 = lean_array_push(x_475, x_28);
x_477 = lean_array_push(x_476, x_42);
x_478 = lean_array_push(x_477, x_29);
x_479 = lean_array_push(x_478, x_413);
x_480 = lean_array_push(x_479, x_471);
x_481 = lean_array_push(x_480, x_448);
x_482 = lean_array_push(x_481, x_1);
x_483 = l_Lean_mkAppN(x_473, x_482);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_484 = l_Lean_Meta_expandCoe(x_483, x_3, x_4, x_5, x_6, x_470);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_485);
x_487 = lean_infer_type(x_485, x_3, x_4, x_5, x_6, x_486);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
lean_dec(x_487);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_490 = l_Lean_Meta_isExprDefEq(x_9, x_488, x_3, x_4, x_5, x_6, x_489);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; uint8_t x_492; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_unbox(x_491);
lean_dec(x_491);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_485);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_493 = lean_ctor_get(x_490, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_494 = x_490;
} else {
 lean_dec_ref(x_490);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_409);
lean_ctor_set(x_495, 1, x_493);
return x_495;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_496 = lean_ctor_get(x_490, 1);
lean_inc(x_496);
lean_dec(x_490);
x_497 = lean_box(0);
x_498 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_485, x_497, x_3, x_4, x_5, x_6, x_496);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_501 = x_498;
} else {
 lean_dec_ref(x_498);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_500);
return x_502;
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_485);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_503 = lean_ctor_get(x_490, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_504 = x_490;
} else {
 lean_dec_ref(x_490);
 x_504 = lean_box(0);
}
if (lean_is_scalar(x_504)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_504;
 lean_ctor_set_tag(x_505, 0);
}
lean_ctor_set(x_505, 0, x_409);
lean_ctor_set(x_505, 1, x_503);
return x_505;
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_485);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_506 = lean_ctor_get(x_487, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_507 = x_487;
} else {
 lean_dec_ref(x_487);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_507;
 lean_ctor_set_tag(x_508, 0);
}
lean_ctor_set(x_508, 0, x_409);
lean_ctor_set(x_508, 1, x_506);
return x_508;
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_509 = lean_ctor_get(x_484, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_510 = x_484;
} else {
 lean_dec_ref(x_484);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_510;
 lean_ctor_set_tag(x_511, 0);
}
lean_ctor_set(x_511, 0, x_409);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_469);
lean_dec(x_448);
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_512 = lean_ctor_get(x_468, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_513 = x_468;
} else {
 lean_dec_ref(x_468);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_409);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_448);
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_515 = lean_ctor_get(x_468, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_516 = x_468;
} else {
 lean_dec_ref(x_468);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_517 = x_516;
 lean_ctor_set_tag(x_517, 0);
}
lean_ctor_set(x_517, 0, x_409);
lean_ctor_set(x_517, 1, x_515);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_450);
lean_dec(x_448);
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_518 = lean_ctor_get(x_452, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_519 = x_452;
} else {
 lean_dec_ref(x_452);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_520 = x_519;
 lean_ctor_set_tag(x_520, 0);
}
lean_ctor_set(x_520, 0, x_409);
lean_ctor_set(x_520, 1, x_518);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_448);
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_521 = lean_ctor_get(x_449, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_522 = x_449;
} else {
 lean_dec_ref(x_449);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(0, 2, 0);
} else {
 x_523 = x_522;
 lean_ctor_set_tag(x_523, 0);
}
lean_ctor_set(x_523, 0, x_409);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_524 = lean_ctor_get(x_438, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_525 = x_438;
} else {
 lean_dec_ref(x_438);
 x_525 = lean_box(0);
}
lean_ctor_set(x_31, 0, x_434);
if (lean_is_scalar(x_525)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_525;
}
lean_ctor_set(x_526, 0, x_31);
lean_ctor_set(x_526, 1, x_524);
return x_526;
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_434);
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_527 = lean_ctor_get(x_438, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_528 = x_438;
} else {
 lean_dec_ref(x_438);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_528;
 lean_ctor_set_tag(x_529, 0);
}
lean_ctor_set(x_529, 0, x_409);
lean_ctor_set(x_529, 1, x_527);
return x_529;
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_434);
lean_dec(x_425);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_530 = lean_ctor_get(x_435, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_531 = x_435;
} else {
 lean_dec_ref(x_435);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_531;
 lean_ctor_set_tag(x_532, 0);
}
lean_ctor_set(x_532, 0, x_409);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_418);
lean_dec(x_415);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_533 = lean_ctor_get(x_420, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_534 = x_420;
} else {
 lean_dec_ref(x_420);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_534;
 lean_ctor_set_tag(x_535, 0);
}
lean_ctor_set(x_535, 0, x_409);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_415);
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_536 = lean_ctor_get(x_417, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_537 = x_417;
} else {
 lean_dec_ref(x_417);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_537;
 lean_ctor_set_tag(x_538, 0);
}
lean_ctor_set(x_538, 0, x_409);
lean_ctor_set(x_538, 1, x_536);
return x_538;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_413);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_539 = lean_ctor_get(x_414, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_540 = x_414;
} else {
 lean_dec_ref(x_414);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_540;
 lean_ctor_set_tag(x_541, 0);
}
lean_ctor_set(x_541, 0, x_409);
lean_ctor_set(x_541, 1, x_539);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_411);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_542 = lean_ctor_get(x_410, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_543 = x_410;
} else {
 lean_dec_ref(x_410);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_409);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_545 = lean_ctor_get(x_410, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_546 = x_410;
} else {
 lean_dec_ref(x_410);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_546;
 lean_ctor_set_tag(x_547, 0);
}
lean_ctor_set(x_547, 0, x_409);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_394);
lean_dec(x_379);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_548 = lean_ctor_get(x_396, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_549 = x_396;
} else {
 lean_dec_ref(x_396);
 x_549 = lean_box(0);
}
x_550 = lean_box(0);
if (lean_is_scalar(x_549)) {
 x_551 = lean_alloc_ctor(0, 2, 0);
} else {
 x_551 = x_549;
 lean_ctor_set_tag(x_551, 0);
}
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_548);
return x_551;
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_552 = lean_ctor_get(x_393, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_553 = x_393;
} else {
 lean_dec_ref(x_393);
 x_553 = lean_box(0);
}
x_554 = lean_box(0);
if (lean_is_scalar(x_553)) {
 x_555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_555 = x_553;
 lean_ctor_set_tag(x_555, 0);
}
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_552);
return x_555;
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_367);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_556 = lean_ctor_get(x_385, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_557 = x_385;
} else {
 lean_dec_ref(x_385);
 x_557 = lean_box(0);
}
x_558 = lean_box(0);
if (lean_is_scalar(x_557)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_557;
 lean_ctor_set_tag(x_559, 0);
}
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_556);
return x_559;
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_367);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_560 = lean_ctor_get(x_381, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_561 = x_381;
} else {
 lean_dec_ref(x_381);
 x_561 = lean_box(0);
}
x_562 = lean_box(0);
if (lean_is_scalar(x_561)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_561;
 lean_ctor_set_tag(x_563, 0);
}
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_560);
return x_563;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_367);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_564 = lean_ctor_get(x_378, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_565 = x_378;
} else {
 lean_dec_ref(x_378);
 x_565 = lean_box(0);
}
x_566 = lean_box(0);
if (lean_is_scalar(x_565)) {
 x_567 = lean_alloc_ctor(0, 2, 0);
} else {
 x_567 = x_565;
 lean_ctor_set_tag(x_567, 0);
}
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_564);
return x_567;
}
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_568 = lean_ctor_get(x_371, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_569 = x_371;
} else {
 lean_dec_ref(x_371);
 x_569 = lean_box(0);
}
x_570 = lean_box(0);
if (lean_is_scalar(x_569)) {
 x_571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_571 = x_569;
}
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_568);
return x_571;
}
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_572 = lean_ctor_get(x_371, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_573 = x_371;
} else {
 lean_dec_ref(x_371);
 x_573 = lean_box(0);
}
x_574 = lean_box(0);
if (lean_is_scalar(x_573)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_573;
}
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_572);
return x_575;
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_372);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_576 = lean_ctor_get(x_371, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_577 = x_371;
} else {
 lean_dec_ref(x_371);
 x_577 = lean_box(0);
}
x_578 = lean_box(0);
if (lean_is_scalar(x_577)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_577;
}
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_576);
return x_579;
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_580 = lean_ctor_get(x_371, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_581 = x_371;
} else {
 lean_dec_ref(x_371);
 x_581 = lean_box(0);
}
x_582 = lean_box(0);
if (lean_is_scalar(x_581)) {
 x_583 = lean_alloc_ctor(0, 2, 0);
} else {
 x_583 = x_581;
 lean_ctor_set_tag(x_583, 0);
}
lean_ctor_set(x_583, 0, x_582);
lean_ctor_set(x_583, 1, x_580);
return x_583;
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_584 = lean_ctor_get(x_368, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_585 = x_368;
} else {
 lean_dec_ref(x_368);
 x_585 = lean_box(0);
}
x_586 = lean_box(0);
if (lean_is_scalar(x_585)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_585;
 lean_ctor_set_tag(x_587, 0);
}
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_584);
return x_587;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_588 = lean_ctor_get(x_361, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_589 = x_361;
} else {
 lean_dec_ref(x_361);
 x_589 = lean_box(0);
}
x_590 = lean_box(0);
if (lean_is_scalar(x_589)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_589;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_588);
return x_591;
}
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_592 = lean_ctor_get(x_361, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_593 = x_361;
} else {
 lean_dec_ref(x_361);
 x_593 = lean_box(0);
}
x_594 = lean_box(0);
if (lean_is_scalar(x_593)) {
 x_595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_595 = x_593;
}
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_592);
return x_595;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_362);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_596 = lean_ctor_get(x_361, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_597 = x_361;
} else {
 lean_dec_ref(x_361);
 x_597 = lean_box(0);
}
x_598 = lean_box(0);
if (lean_is_scalar(x_597)) {
 x_599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_599 = x_597;
}
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_596);
return x_599;
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_600 = lean_ctor_get(x_361, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_601 = x_361;
} else {
 lean_dec_ref(x_361);
 x_601 = lean_box(0);
}
x_602 = lean_box(0);
if (lean_is_scalar(x_601)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_601;
 lean_ctor_set_tag(x_603, 0);
}
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_600);
return x_603;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_604 = lean_ctor_get(x_358, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_605 = x_358;
} else {
 lean_dec_ref(x_358);
 x_605 = lean_box(0);
}
x_606 = lean_box(0);
if (lean_is_scalar(x_605)) {
 x_607 = lean_alloc_ctor(0, 2, 0);
} else {
 x_607 = x_605;
 lean_ctor_set_tag(x_607, 0);
}
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_604);
return x_607;
}
}
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_15);
lean_dec(x_9);
x_608 = lean_ctor_get(x_43, 1);
lean_inc(x_608);
lean_dec(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_609 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_608);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
if (lean_obj_tag(x_610) == 0)
{
uint8_t x_611; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_free_object(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_611 = !lean_is_exclusive(x_609);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; 
x_612 = lean_ctor_get(x_609, 0);
lean_dec(x_612);
x_613 = lean_box(0);
lean_ctor_set(x_609, 0, x_613);
return x_609;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_609, 1);
lean_inc(x_614);
lean_dec(x_609);
x_615 = lean_box(0);
x_616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
}
else
{
lean_object* x_617; uint8_t x_618; 
x_617 = lean_ctor_get(x_609, 1);
lean_inc(x_617);
lean_dec(x_609);
x_618 = !lean_is_exclusive(x_610);
if (x_618 == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_619 = lean_ctor_get(x_610, 0);
lean_ctor_set(x_610, 0, x_41);
lean_ctor_set(x_31, 0, x_42);
lean_ctor_set(x_18, 0, x_29);
x_620 = lean_box(0);
x_621 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_621, 0, x_619);
x_622 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_622, 0, x_1);
x_623 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_624 = lean_array_push(x_623, x_610);
x_625 = lean_array_push(x_624, x_31);
x_626 = lean_array_push(x_625, x_18);
x_627 = lean_array_push(x_626, x_620);
x_628 = lean_array_push(x_627, x_621);
x_629 = lean_array_push(x_628, x_622);
x_630 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_631 = l_Lean_Meta_mkAppOptM(x_630, x_629, x_3, x_4, x_5, x_6, x_617);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
x_634 = l_Lean_Meta_expandCoe(x_632, x_3, x_4, x_5, x_6, x_633);
if (lean_obj_tag(x_634) == 0)
{
uint8_t x_635; 
x_635 = !lean_is_exclusive(x_634);
if (x_635 == 0)
{
lean_object* x_636; lean_object* x_637; 
x_636 = lean_ctor_get(x_634, 0);
x_637 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_634, 0, x_637);
return x_634;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_638 = lean_ctor_get(x_634, 0);
x_639 = lean_ctor_get(x_634, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_634);
x_640 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_640, 0, x_638);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_639);
return x_641;
}
}
else
{
uint8_t x_642; 
x_642 = !lean_is_exclusive(x_634);
if (x_642 == 0)
{
lean_object* x_643; 
x_643 = lean_ctor_get(x_634, 0);
lean_dec(x_643);
lean_ctor_set_tag(x_634, 0);
lean_ctor_set(x_634, 0, x_620);
return x_634;
}
else
{
lean_object* x_644; lean_object* x_645; 
x_644 = lean_ctor_get(x_634, 1);
lean_inc(x_644);
lean_dec(x_634);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_620);
lean_ctor_set(x_645, 1, x_644);
return x_645;
}
}
}
else
{
uint8_t x_646; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_646 = !lean_is_exclusive(x_631);
if (x_646 == 0)
{
lean_object* x_647; 
x_647 = lean_ctor_get(x_631, 0);
lean_dec(x_647);
lean_ctor_set_tag(x_631, 0);
lean_ctor_set(x_631, 0, x_620);
return x_631;
}
else
{
lean_object* x_648; lean_object* x_649; 
x_648 = lean_ctor_get(x_631, 1);
lean_inc(x_648);
lean_dec(x_631);
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_620);
lean_ctor_set(x_649, 1, x_648);
return x_649;
}
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_650 = lean_ctor_get(x_610, 0);
lean_inc(x_650);
lean_dec(x_610);
x_651 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_651, 0, x_41);
lean_ctor_set(x_31, 0, x_42);
lean_ctor_set(x_18, 0, x_29);
x_652 = lean_box(0);
x_653 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_653, 0, x_650);
x_654 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_654, 0, x_1);
x_655 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_656 = lean_array_push(x_655, x_651);
x_657 = lean_array_push(x_656, x_31);
x_658 = lean_array_push(x_657, x_18);
x_659 = lean_array_push(x_658, x_652);
x_660 = lean_array_push(x_659, x_653);
x_661 = lean_array_push(x_660, x_654);
x_662 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_663 = l_Lean_Meta_mkAppOptM(x_662, x_661, x_3, x_4, x_5, x_6, x_617);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec(x_663);
x_666 = l_Lean_Meta_expandCoe(x_664, x_3, x_4, x_5, x_6, x_665);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 lean_ctor_release(x_666, 1);
 x_669 = x_666;
} else {
 lean_dec_ref(x_666);
 x_669 = lean_box(0);
}
x_670 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_670, 0, x_667);
if (lean_is_scalar(x_669)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_669;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_668);
return x_671;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_672 = lean_ctor_get(x_666, 1);
lean_inc(x_672);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 lean_ctor_release(x_666, 1);
 x_673 = x_666;
} else {
 lean_dec_ref(x_666);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(0, 2, 0);
} else {
 x_674 = x_673;
 lean_ctor_set_tag(x_674, 0);
}
lean_ctor_set(x_674, 0, x_652);
lean_ctor_set(x_674, 1, x_672);
return x_674;
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_675 = lean_ctor_get(x_663, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_676 = x_663;
} else {
 lean_dec_ref(x_663);
 x_676 = lean_box(0);
}
if (lean_is_scalar(x_676)) {
 x_677 = lean_alloc_ctor(0, 2, 0);
} else {
 x_677 = x_676;
 lean_ctor_set_tag(x_677, 0);
}
lean_ctor_set(x_677, 0, x_652);
lean_ctor_set(x_677, 1, x_675);
return x_677;
}
}
}
}
}
else
{
uint8_t x_678; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_678 = !lean_is_exclusive(x_43);
if (x_678 == 0)
{
return x_43;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_43, 0);
x_680 = lean_ctor_get(x_43, 1);
lean_inc(x_680);
lean_inc(x_679);
lean_dec(x_43);
x_681 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_681, 0, x_679);
lean_ctor_set(x_681, 1, x_680);
return x_681;
}
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_682 = lean_ctor_get(x_31, 0);
lean_inc(x_682);
lean_dec(x_31);
x_683 = lean_ctor_get(x_30, 1);
lean_inc(x_683);
lean_dec(x_30);
x_684 = lean_ctor_get(x_682, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_682, 1);
lean_inc(x_685);
lean_dec(x_682);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
lean_inc(x_684);
x_686 = l_Lean_Meta_isExprDefEq(x_684, x_28, x_3, x_4, x_5, x_6, x_683);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; uint8_t x_688; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_unbox(x_687);
lean_dec(x_687);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
lean_free_object(x_18);
x_689 = lean_ctor_get(x_686, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_690 = x_686;
} else {
 lean_dec_ref(x_686);
 x_690 = lean_box(0);
}
x_691 = lean_ctor_get(x_5, 2);
lean_inc(x_691);
x_692 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_693 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_691, x_692);
lean_dec(x_691);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_694 = lean_box(0);
if (lean_is_scalar(x_690)) {
 x_695 = lean_alloc_ctor(0, 2, 0);
} else {
 x_695 = x_690;
}
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_689);
return x_695;
}
else
{
lean_object* x_696; 
lean_dec(x_690);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_684);
x_696 = lean_infer_type(x_684, x_3, x_4, x_5, x_6, x_689);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_699 = lean_whnf(x_697, x_3, x_4, x_5, x_6, x_698);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
if (lean_obj_tag(x_700) == 7)
{
lean_object* x_701; 
x_701 = lean_ctor_get(x_700, 1);
lean_inc(x_701);
if (lean_obj_tag(x_701) == 3)
{
lean_object* x_702; 
x_702 = lean_ctor_get(x_700, 2);
lean_inc(x_702);
lean_dec(x_700);
if (lean_obj_tag(x_702) == 3)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_703 = lean_ctor_get(x_699, 1);
lean_inc(x_703);
lean_dec(x_699);
x_704 = lean_ctor_get(x_701, 0);
lean_inc(x_704);
lean_dec(x_701);
x_705 = lean_ctor_get(x_702, 0);
lean_inc(x_705);
lean_dec(x_702);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_706 = lean_infer_type(x_28, x_3, x_4, x_5, x_6, x_703);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
lean_dec(x_706);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_709 = lean_whnf(x_707, x_3, x_4, x_5, x_6, x_708);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
if (lean_obj_tag(x_710) == 7)
{
lean_object* x_711; 
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
if (lean_obj_tag(x_711) == 3)
{
lean_object* x_712; 
x_712 = lean_ctor_get(x_710, 2);
lean_inc(x_712);
lean_dec(x_710);
if (lean_obj_tag(x_712) == 3)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_713 = lean_ctor_get(x_709, 1);
lean_inc(x_713);
lean_dec(x_709);
x_714 = lean_ctor_get(x_711, 0);
lean_inc(x_714);
lean_dec(x_711);
x_715 = lean_ctor_get(x_712, 0);
lean_inc(x_715);
lean_dec(x_712);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_716 = l_Lean_Meta_decLevel(x_704, x_3, x_4, x_5, x_6, x_713);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
lean_dec(x_716);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_719 = l_Lean_Meta_decLevel(x_714, x_3, x_4, x_5, x_6, x_718);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; uint8_t x_722; lean_object* x_723; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_717);
x_723 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_717, x_720, x_722, x_3, x_4, x_5, x_6, x_721);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; uint8_t x_725; 
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_unbox(x_724);
lean_dec(x_724);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_717);
lean_dec(x_715);
lean_dec(x_705);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_726 = lean_ctor_get(x_723, 1);
lean_inc(x_726);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_727 = x_723;
} else {
 lean_dec_ref(x_723);
 x_727 = lean_box(0);
}
x_728 = lean_box(0);
if (lean_is_scalar(x_727)) {
 x_729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_729 = x_727;
}
lean_ctor_set(x_729, 0, x_728);
lean_ctor_set(x_729, 1, x_726);
return x_729;
}
else
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_723, 1);
lean_inc(x_730);
lean_dec(x_723);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_731 = l_Lean_Meta_decLevel(x_705, x_3, x_4, x_5, x_6, x_730);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec(x_731);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_734 = l_Lean_Meta_decLevel(x_715, x_3, x_4, x_5, x_6, x_733);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = lean_box(0);
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_735);
lean_ctor_set(x_738, 1, x_737);
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_732);
lean_ctor_set(x_739, 1, x_738);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_717);
lean_ctor_set(x_740, 1, x_739);
x_741 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_742 = l_Lean_Expr_const___override(x_741, x_740);
x_743 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_684);
x_744 = lean_array_push(x_743, x_684);
lean_inc(x_28);
x_745 = lean_array_push(x_744, x_28);
x_746 = l_Lean_mkAppN(x_742, x_745);
x_747 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_748 = l_Lean_Meta_trySynthInstance(x_746, x_747, x_3, x_4, x_5, x_6, x_736);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
if (lean_obj_tag(x_749) == 1)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
lean_dec(x_748);
x_751 = lean_ctor_get(x_749, 0);
lean_inc(x_751);
lean_dec(x_749);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_685);
x_752 = l_Lean_Meta_getDecLevel(x_685, x_3, x_4, x_5, x_6, x_750);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
lean_dec(x_752);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_755 = l_Lean_Meta_getDecLevel(x_15, x_3, x_4, x_5, x_6, x_754);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_758 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_757);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_737);
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_756);
lean_ctor_set(x_762, 1, x_761);
x_763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_763, 0, x_753);
lean_ctor_set(x_763, 1, x_762);
x_764 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_763);
x_765 = l_Lean_Expr_const___override(x_764, x_763);
x_766 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_684);
x_767 = lean_array_push(x_766, x_684);
lean_inc(x_28);
x_768 = lean_array_push(x_767, x_28);
lean_inc(x_751);
x_769 = lean_array_push(x_768, x_751);
lean_inc(x_685);
x_770 = lean_array_push(x_769, x_685);
lean_inc(x_1);
x_771 = lean_array_push(x_770, x_1);
x_772 = l_Lean_mkAppN(x_765, x_771);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_772);
x_773 = lean_infer_type(x_772, x_3, x_4, x_5, x_6, x_760);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
lean_dec(x_773);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_776 = l_Lean_Meta_isExprDefEq(x_9, x_774, x_3, x_4, x_5, x_6, x_775);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; uint8_t x_778; 
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_unbox(x_777);
lean_dec(x_777);
if (x_778 == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
lean_dec(x_772);
x_779 = lean_ctor_get(x_776, 1);
lean_inc(x_779);
lean_dec(x_776);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_780 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_779);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_763);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_783 = x_780;
} else {
 lean_dec_ref(x_780);
 x_783 = lean_box(0);
}
if (lean_is_scalar(x_783)) {
 x_784 = lean_alloc_ctor(0, 2, 0);
} else {
 x_784 = x_783;
}
lean_ctor_set(x_784, 0, x_747);
lean_ctor_set(x_784, 1, x_782);
return x_784;
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_785 = lean_ctor_get(x_780, 1);
lean_inc(x_785);
lean_dec(x_780);
x_786 = lean_ctor_get(x_781, 0);
lean_inc(x_786);
lean_dec(x_781);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_685);
x_787 = l_Lean_Meta_getLevel(x_685, x_3, x_4, x_5, x_6, x_785);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec(x_787);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_790 = l_Lean_Meta_getLevel(x_29, x_3, x_4, x_5, x_6, x_789);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; lean_object* x_805; lean_object* x_806; 
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
lean_dec(x_790);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_737);
x_794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_794, 0, x_788);
lean_ctor_set(x_794, 1, x_793);
x_795 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_796 = l_Lean_Expr_const___override(x_795, x_794);
x_797 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_685);
x_798 = lean_array_push(x_797, x_685);
x_799 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_800 = lean_array_push(x_798, x_799);
lean_inc(x_29);
x_801 = lean_array_push(x_800, x_29);
x_802 = l_Lean_mkAppN(x_796, x_801);
x_803 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_804 = 0;
lean_inc(x_685);
x_805 = l_Lean_Expr_forallE___override(x_803, x_685, x_802, x_804);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_806 = l_Lean_Meta_trySynthInstance(x_805, x_747, x_3, x_4, x_5, x_6, x_792);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
if (lean_obj_tag(x_807) == 1)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
lean_dec(x_806);
x_809 = lean_ctor_get(x_807, 0);
lean_inc(x_809);
lean_dec(x_807);
x_810 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_811 = l_Lean_Expr_const___override(x_810, x_763);
x_812 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_813 = lean_array_push(x_812, x_684);
x_814 = lean_array_push(x_813, x_28);
x_815 = lean_array_push(x_814, x_685);
x_816 = lean_array_push(x_815, x_29);
x_817 = lean_array_push(x_816, x_751);
x_818 = lean_array_push(x_817, x_809);
x_819 = lean_array_push(x_818, x_786);
x_820 = lean_array_push(x_819, x_1);
x_821 = l_Lean_mkAppN(x_811, x_820);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_822 = l_Lean_Meta_expandCoe(x_821, x_3, x_4, x_5, x_6, x_808);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_823);
x_825 = lean_infer_type(x_823, x_3, x_4, x_5, x_6, x_824);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_828 = l_Lean_Meta_isExprDefEq(x_9, x_826, x_3, x_4, x_5, x_6, x_827);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; uint8_t x_830; 
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_unbox(x_829);
lean_dec(x_829);
if (x_830 == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
lean_dec(x_823);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_831 = lean_ctor_get(x_828, 1);
lean_inc(x_831);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_832 = x_828;
} else {
 lean_dec_ref(x_828);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 2, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_747);
lean_ctor_set(x_833, 1, x_831);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_834 = lean_ctor_get(x_828, 1);
lean_inc(x_834);
lean_dec(x_828);
x_835 = lean_box(0);
x_836 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_823, x_835, x_3, x_4, x_5, x_6, x_834);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
if (lean_is_exclusive(x_836)) {
 lean_ctor_release(x_836, 0);
 lean_ctor_release(x_836, 1);
 x_839 = x_836;
} else {
 lean_dec_ref(x_836);
 x_839 = lean_box(0);
}
if (lean_is_scalar(x_839)) {
 x_840 = lean_alloc_ctor(0, 2, 0);
} else {
 x_840 = x_839;
}
lean_ctor_set(x_840, 0, x_837);
lean_ctor_set(x_840, 1, x_838);
return x_840;
}
}
else
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_823);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_841 = lean_ctor_get(x_828, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_842 = x_828;
} else {
 lean_dec_ref(x_828);
 x_842 = lean_box(0);
}
if (lean_is_scalar(x_842)) {
 x_843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_843 = x_842;
 lean_ctor_set_tag(x_843, 0);
}
lean_ctor_set(x_843, 0, x_747);
lean_ctor_set(x_843, 1, x_841);
return x_843;
}
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_823);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_844 = lean_ctor_get(x_825, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_845 = x_825;
} else {
 lean_dec_ref(x_825);
 x_845 = lean_box(0);
}
if (lean_is_scalar(x_845)) {
 x_846 = lean_alloc_ctor(0, 2, 0);
} else {
 x_846 = x_845;
 lean_ctor_set_tag(x_846, 0);
}
lean_ctor_set(x_846, 0, x_747);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_847 = lean_ctor_get(x_822, 1);
lean_inc(x_847);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_848 = x_822;
} else {
 lean_dec_ref(x_822);
 x_848 = lean_box(0);
}
if (lean_is_scalar(x_848)) {
 x_849 = lean_alloc_ctor(0, 2, 0);
} else {
 x_849 = x_848;
 lean_ctor_set_tag(x_849, 0);
}
lean_ctor_set(x_849, 0, x_747);
lean_ctor_set(x_849, 1, x_847);
return x_849;
}
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
lean_dec(x_807);
lean_dec(x_786);
lean_dec(x_763);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_850 = lean_ctor_get(x_806, 1);
lean_inc(x_850);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_851 = x_806;
} else {
 lean_dec_ref(x_806);
 x_851 = lean_box(0);
}
if (lean_is_scalar(x_851)) {
 x_852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_852 = x_851;
}
lean_ctor_set(x_852, 0, x_747);
lean_ctor_set(x_852, 1, x_850);
return x_852;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_786);
lean_dec(x_763);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_853 = lean_ctor_get(x_806, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_854 = x_806;
} else {
 lean_dec_ref(x_806);
 x_854 = lean_box(0);
}
if (lean_is_scalar(x_854)) {
 x_855 = lean_alloc_ctor(0, 2, 0);
} else {
 x_855 = x_854;
 lean_ctor_set_tag(x_855, 0);
}
lean_ctor_set(x_855, 0, x_747);
lean_ctor_set(x_855, 1, x_853);
return x_855;
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec(x_788);
lean_dec(x_786);
lean_dec(x_763);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_856 = lean_ctor_get(x_790, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_857 = x_790;
} else {
 lean_dec_ref(x_790);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_858 = x_857;
 lean_ctor_set_tag(x_858, 0);
}
lean_ctor_set(x_858, 0, x_747);
lean_ctor_set(x_858, 1, x_856);
return x_858;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_dec(x_786);
lean_dec(x_763);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_859 = lean_ctor_get(x_787, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_860 = x_787;
} else {
 lean_dec_ref(x_787);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_861 = x_860;
 lean_ctor_set_tag(x_861, 0);
}
lean_ctor_set(x_861, 0, x_747);
lean_ctor_set(x_861, 1, x_859);
return x_861;
}
}
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_763);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_862 = lean_ctor_get(x_776, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_863 = x_776;
} else {
 lean_dec_ref(x_776);
 x_863 = lean_box(0);
}
x_864 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_864, 0, x_772);
if (lean_is_scalar(x_863)) {
 x_865 = lean_alloc_ctor(0, 2, 0);
} else {
 x_865 = x_863;
}
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_862);
return x_865;
}
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_772);
lean_dec(x_763);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_866 = lean_ctor_get(x_776, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_867 = x_776;
} else {
 lean_dec_ref(x_776);
 x_867 = lean_box(0);
}
if (lean_is_scalar(x_867)) {
 x_868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_868 = x_867;
 lean_ctor_set_tag(x_868, 0);
}
lean_ctor_set(x_868, 0, x_747);
lean_ctor_set(x_868, 1, x_866);
return x_868;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_772);
lean_dec(x_763);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_869 = lean_ctor_get(x_773, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_870 = x_773;
} else {
 lean_dec_ref(x_773);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_871 = x_870;
 lean_ctor_set_tag(x_871, 0);
}
lean_ctor_set(x_871, 0, x_747);
lean_ctor_set(x_871, 1, x_869);
return x_871;
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
lean_dec(x_756);
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_872 = lean_ctor_get(x_758, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_873 = x_758;
} else {
 lean_dec_ref(x_758);
 x_873 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_873;
 lean_ctor_set_tag(x_874, 0);
}
lean_ctor_set(x_874, 0, x_747);
lean_ctor_set(x_874, 1, x_872);
return x_874;
}
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_875 = lean_ctor_get(x_755, 1);
lean_inc(x_875);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_876 = x_755;
} else {
 lean_dec_ref(x_755);
 x_876 = lean_box(0);
}
if (lean_is_scalar(x_876)) {
 x_877 = lean_alloc_ctor(0, 2, 0);
} else {
 x_877 = x_876;
 lean_ctor_set_tag(x_877, 0);
}
lean_ctor_set(x_877, 0, x_747);
lean_ctor_set(x_877, 1, x_875);
return x_877;
}
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
lean_dec(x_751);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_878 = lean_ctor_get(x_752, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_879 = x_752;
} else {
 lean_dec_ref(x_752);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_879;
 lean_ctor_set_tag(x_880, 0);
}
lean_ctor_set(x_880, 0, x_747);
lean_ctor_set(x_880, 1, x_878);
return x_880;
}
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_749);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_881 = lean_ctor_get(x_748, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_882 = x_748;
} else {
 lean_dec_ref(x_748);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_747);
lean_ctor_set(x_883, 1, x_881);
return x_883;
}
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_884 = lean_ctor_get(x_748, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_885 = x_748;
} else {
 lean_dec_ref(x_748);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(0, 2, 0);
} else {
 x_886 = x_885;
 lean_ctor_set_tag(x_886, 0);
}
lean_ctor_set(x_886, 0, x_747);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_732);
lean_dec(x_717);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_887 = lean_ctor_get(x_734, 1);
lean_inc(x_887);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 x_888 = x_734;
} else {
 lean_dec_ref(x_734);
 x_888 = lean_box(0);
}
x_889 = lean_box(0);
if (lean_is_scalar(x_888)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_888;
 lean_ctor_set_tag(x_890, 0);
}
lean_ctor_set(x_890, 0, x_889);
lean_ctor_set(x_890, 1, x_887);
return x_890;
}
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
lean_dec(x_717);
lean_dec(x_715);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_891 = lean_ctor_get(x_731, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_892 = x_731;
} else {
 lean_dec_ref(x_731);
 x_892 = lean_box(0);
}
x_893 = lean_box(0);
if (lean_is_scalar(x_892)) {
 x_894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_894 = x_892;
 lean_ctor_set_tag(x_894, 0);
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_891);
return x_894;
}
}
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_717);
lean_dec(x_715);
lean_dec(x_705);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_895 = lean_ctor_get(x_723, 1);
lean_inc(x_895);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_896 = x_723;
} else {
 lean_dec_ref(x_723);
 x_896 = lean_box(0);
}
x_897 = lean_box(0);
if (lean_is_scalar(x_896)) {
 x_898 = lean_alloc_ctor(0, 2, 0);
} else {
 x_898 = x_896;
 lean_ctor_set_tag(x_898, 0);
}
lean_ctor_set(x_898, 0, x_897);
lean_ctor_set(x_898, 1, x_895);
return x_898;
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_717);
lean_dec(x_715);
lean_dec(x_705);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_899 = lean_ctor_get(x_719, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_900 = x_719;
} else {
 lean_dec_ref(x_719);
 x_900 = lean_box(0);
}
x_901 = lean_box(0);
if (lean_is_scalar(x_900)) {
 x_902 = lean_alloc_ctor(0, 2, 0);
} else {
 x_902 = x_900;
 lean_ctor_set_tag(x_902, 0);
}
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_899);
return x_902;
}
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_705);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_903 = lean_ctor_get(x_716, 1);
lean_inc(x_903);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_904 = x_716;
} else {
 lean_dec_ref(x_716);
 x_904 = lean_box(0);
}
x_905 = lean_box(0);
if (lean_is_scalar(x_904)) {
 x_906 = lean_alloc_ctor(0, 2, 0);
} else {
 x_906 = x_904;
 lean_ctor_set_tag(x_906, 0);
}
lean_ctor_set(x_906, 0, x_905);
lean_ctor_set(x_906, 1, x_903);
return x_906;
}
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_705);
lean_dec(x_704);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_907 = lean_ctor_get(x_709, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_908 = x_709;
} else {
 lean_dec_ref(x_709);
 x_908 = lean_box(0);
}
x_909 = lean_box(0);
if (lean_is_scalar(x_908)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_908;
}
lean_ctor_set(x_910, 0, x_909);
lean_ctor_set(x_910, 1, x_907);
return x_910;
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_705);
lean_dec(x_704);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_911 = lean_ctor_get(x_709, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_912 = x_709;
} else {
 lean_dec_ref(x_709);
 x_912 = lean_box(0);
}
x_913 = lean_box(0);
if (lean_is_scalar(x_912)) {
 x_914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_914 = x_912;
}
lean_ctor_set(x_914, 0, x_913);
lean_ctor_set(x_914, 1, x_911);
return x_914;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_710);
lean_dec(x_705);
lean_dec(x_704);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_915 = lean_ctor_get(x_709, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_916 = x_709;
} else {
 lean_dec_ref(x_709);
 x_916 = lean_box(0);
}
x_917 = lean_box(0);
if (lean_is_scalar(x_916)) {
 x_918 = lean_alloc_ctor(0, 2, 0);
} else {
 x_918 = x_916;
}
lean_ctor_set(x_918, 0, x_917);
lean_ctor_set(x_918, 1, x_915);
return x_918;
}
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
lean_dec(x_705);
lean_dec(x_704);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_919 = lean_ctor_get(x_709, 1);
lean_inc(x_919);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_920 = x_709;
} else {
 lean_dec_ref(x_709);
 x_920 = lean_box(0);
}
x_921 = lean_box(0);
if (lean_is_scalar(x_920)) {
 x_922 = lean_alloc_ctor(0, 2, 0);
} else {
 x_922 = x_920;
 lean_ctor_set_tag(x_922, 0);
}
lean_ctor_set(x_922, 0, x_921);
lean_ctor_set(x_922, 1, x_919);
return x_922;
}
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
lean_dec(x_705);
lean_dec(x_704);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_923 = lean_ctor_get(x_706, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_706)) {
 lean_ctor_release(x_706, 0);
 lean_ctor_release(x_706, 1);
 x_924 = x_706;
} else {
 lean_dec_ref(x_706);
 x_924 = lean_box(0);
}
x_925 = lean_box(0);
if (lean_is_scalar(x_924)) {
 x_926 = lean_alloc_ctor(0, 2, 0);
} else {
 x_926 = x_924;
 lean_ctor_set_tag(x_926, 0);
}
lean_ctor_set(x_926, 0, x_925);
lean_ctor_set(x_926, 1, x_923);
return x_926;
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_702);
lean_dec(x_701);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_927 = lean_ctor_get(x_699, 1);
lean_inc(x_927);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_928 = x_699;
} else {
 lean_dec_ref(x_699);
 x_928 = lean_box(0);
}
x_929 = lean_box(0);
if (lean_is_scalar(x_928)) {
 x_930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_930 = x_928;
}
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_927);
return x_930;
}
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_931 = lean_ctor_get(x_699, 1);
lean_inc(x_931);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_932 = x_699;
} else {
 lean_dec_ref(x_699);
 x_932 = lean_box(0);
}
x_933 = lean_box(0);
if (lean_is_scalar(x_932)) {
 x_934 = lean_alloc_ctor(0, 2, 0);
} else {
 x_934 = x_932;
}
lean_ctor_set(x_934, 0, x_933);
lean_ctor_set(x_934, 1, x_931);
return x_934;
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_700);
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_935 = lean_ctor_get(x_699, 1);
lean_inc(x_935);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_936 = x_699;
} else {
 lean_dec_ref(x_699);
 x_936 = lean_box(0);
}
x_937 = lean_box(0);
if (lean_is_scalar(x_936)) {
 x_938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_938 = x_936;
}
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_935);
return x_938;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_939 = lean_ctor_get(x_699, 1);
lean_inc(x_939);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_940 = x_699;
} else {
 lean_dec_ref(x_699);
 x_940 = lean_box(0);
}
x_941 = lean_box(0);
if (lean_is_scalar(x_940)) {
 x_942 = lean_alloc_ctor(0, 2, 0);
} else {
 x_942 = x_940;
 lean_ctor_set_tag(x_942, 0);
}
lean_ctor_set(x_942, 0, x_941);
lean_ctor_set(x_942, 1, x_939);
return x_942;
}
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_943 = lean_ctor_get(x_696, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_696)) {
 lean_ctor_release(x_696, 0);
 lean_ctor_release(x_696, 1);
 x_944 = x_696;
} else {
 lean_dec_ref(x_696);
 x_944 = lean_box(0);
}
x_945 = lean_box(0);
if (lean_is_scalar(x_944)) {
 x_946 = lean_alloc_ctor(0, 2, 0);
} else {
 x_946 = x_944;
 lean_ctor_set_tag(x_946, 0);
}
lean_ctor_set(x_946, 0, x_945);
lean_ctor_set(x_946, 1, x_943);
return x_946;
}
}
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; 
lean_dec(x_15);
lean_dec(x_9);
x_947 = lean_ctor_get(x_686, 1);
lean_inc(x_947);
lean_dec(x_686);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_948 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_947);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_free_object(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_951 = x_948;
} else {
 lean_dec_ref(x_948);
 x_951 = lean_box(0);
}
x_952 = lean_box(0);
if (lean_is_scalar(x_951)) {
 x_953 = lean_alloc_ctor(0, 2, 0);
} else {
 x_953 = x_951;
}
lean_ctor_set(x_953, 0, x_952);
lean_ctor_set(x_953, 1, x_950);
return x_953;
}
else
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_954 = lean_ctor_get(x_948, 1);
lean_inc(x_954);
lean_dec(x_948);
x_955 = lean_ctor_get(x_949, 0);
lean_inc(x_955);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 x_956 = x_949;
} else {
 lean_dec_ref(x_949);
 x_956 = lean_box(0);
}
if (lean_is_scalar(x_956)) {
 x_957 = lean_alloc_ctor(1, 1, 0);
} else {
 x_957 = x_956;
}
lean_ctor_set(x_957, 0, x_684);
x_958 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_958, 0, x_685);
lean_ctor_set(x_18, 0, x_29);
x_959 = lean_box(0);
x_960 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_960, 0, x_955);
x_961 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_961, 0, x_1);
x_962 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_963 = lean_array_push(x_962, x_957);
x_964 = lean_array_push(x_963, x_958);
x_965 = lean_array_push(x_964, x_18);
x_966 = lean_array_push(x_965, x_959);
x_967 = lean_array_push(x_966, x_960);
x_968 = lean_array_push(x_967, x_961);
x_969 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_970 = l_Lean_Meta_mkAppOptM(x_969, x_968, x_3, x_4, x_5, x_6, x_954);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec(x_970);
x_973 = l_Lean_Meta_expandCoe(x_971, x_3, x_4, x_5, x_6, x_972);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_973, 1);
lean_inc(x_975);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 x_976 = x_973;
} else {
 lean_dec_ref(x_973);
 x_976 = lean_box(0);
}
x_977 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_977, 0, x_974);
if (lean_is_scalar(x_976)) {
 x_978 = lean_alloc_ctor(0, 2, 0);
} else {
 x_978 = x_976;
}
lean_ctor_set(x_978, 0, x_977);
lean_ctor_set(x_978, 1, x_975);
return x_978;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_979 = lean_ctor_get(x_973, 1);
lean_inc(x_979);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 x_980 = x_973;
} else {
 lean_dec_ref(x_973);
 x_980 = lean_box(0);
}
if (lean_is_scalar(x_980)) {
 x_981 = lean_alloc_ctor(0, 2, 0);
} else {
 x_981 = x_980;
 lean_ctor_set_tag(x_981, 0);
}
lean_ctor_set(x_981, 0, x_959);
lean_ctor_set(x_981, 1, x_979);
return x_981;
}
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_982 = lean_ctor_get(x_970, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 lean_ctor_release(x_970, 1);
 x_983 = x_970;
} else {
 lean_dec_ref(x_970);
 x_983 = lean_box(0);
}
if (lean_is_scalar(x_983)) {
 x_984 = lean_alloc_ctor(0, 2, 0);
} else {
 x_984 = x_983;
 lean_ctor_set_tag(x_984, 0);
}
lean_ctor_set(x_984, 0, x_959);
lean_ctor_set(x_984, 1, x_982);
return x_984;
}
}
}
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_685);
lean_dec(x_684);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_985 = lean_ctor_get(x_686, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_686, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_987 = x_686;
} else {
 lean_dec_ref(x_686);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_985);
lean_ctor_set(x_988, 1, x_986);
return x_988;
}
}
}
}
else
{
uint8_t x_989; 
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_989 = !lean_is_exclusive(x_30);
if (x_989 == 0)
{
return x_30;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_30, 0);
x_991 = lean_ctor_get(x_30, 1);
lean_inc(x_991);
lean_inc(x_990);
lean_dec(x_30);
x_992 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_992, 0, x_990);
lean_ctor_set(x_992, 1, x_991);
return x_992;
}
}
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_993 = lean_ctor_get(x_18, 0);
lean_inc(x_993);
lean_dec(x_18);
x_994 = lean_ctor_get(x_17, 1);
lean_inc(x_994);
lean_dec(x_17);
x_995 = lean_ctor_get(x_993, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_993, 1);
lean_inc(x_996);
lean_dec(x_993);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
x_997 = l_Lean_Meta_isTypeApp_x3f(x_15, x_3, x_4, x_5, x_6, x_994);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; 
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 lean_ctor_release(x_997, 1);
 x_1000 = x_997;
} else {
 lean_dec_ref(x_997);
 x_1000 = lean_box(0);
}
x_1001 = lean_box(0);
if (lean_is_scalar(x_1000)) {
 x_1002 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1002 = x_1000;
}
lean_ctor_set(x_1002, 0, x_1001);
lean_ctor_set(x_1002, 1, x_999);
return x_1002;
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1003 = lean_ctor_get(x_998, 0);
lean_inc(x_1003);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 x_1004 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1004 = lean_box(0);
}
x_1005 = lean_ctor_get(x_997, 1);
lean_inc(x_1005);
lean_dec(x_997);
x_1006 = lean_ctor_get(x_1003, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1003, 1);
lean_inc(x_1007);
lean_dec(x_1003);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_995);
lean_inc(x_1006);
x_1008 = l_Lean_Meta_isExprDefEq(x_1006, x_995, x_3, x_4, x_5, x_6, x_1005);
if (lean_obj_tag(x_1008) == 0)
{
lean_object* x_1009; uint8_t x_1010; 
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_unbox(x_1009);
lean_dec(x_1009);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; uint8_t x_1015; 
x_1011 = lean_ctor_get(x_1008, 1);
lean_inc(x_1011);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 lean_ctor_release(x_1008, 1);
 x_1012 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1012 = lean_box(0);
}
x_1013 = lean_ctor_get(x_5, 2);
lean_inc(x_1013);
x_1014 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1015 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1013, x_1014);
lean_dec(x_1013);
if (x_1015 == 0)
{
lean_object* x_1016; lean_object* x_1017; 
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1016 = lean_box(0);
if (lean_is_scalar(x_1012)) {
 x_1017 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1017 = x_1012;
}
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1011);
return x_1017;
}
else
{
lean_object* x_1018; 
lean_dec(x_1012);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1006);
x_1018 = lean_infer_type(x_1006, x_3, x_4, x_5, x_6, x_1011);
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1018, 1);
lean_inc(x_1020);
lean_dec(x_1018);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1021 = lean_whnf(x_1019, x_3, x_4, x_5, x_6, x_1020);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; 
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
if (lean_obj_tag(x_1022) == 7)
{
lean_object* x_1023; 
x_1023 = lean_ctor_get(x_1022, 1);
lean_inc(x_1023);
if (lean_obj_tag(x_1023) == 3)
{
lean_object* x_1024; 
x_1024 = lean_ctor_get(x_1022, 2);
lean_inc(x_1024);
lean_dec(x_1022);
if (lean_obj_tag(x_1024) == 3)
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1025 = lean_ctor_get(x_1021, 1);
lean_inc(x_1025);
lean_dec(x_1021);
x_1026 = lean_ctor_get(x_1023, 0);
lean_inc(x_1026);
lean_dec(x_1023);
x_1027 = lean_ctor_get(x_1024, 0);
lean_inc(x_1027);
lean_dec(x_1024);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_995);
x_1028 = lean_infer_type(x_995, x_3, x_4, x_5, x_6, x_1025);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1028, 1);
lean_inc(x_1030);
lean_dec(x_1028);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1031 = lean_whnf(x_1029, x_3, x_4, x_5, x_6, x_1030);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
if (lean_obj_tag(x_1032) == 7)
{
lean_object* x_1033; 
x_1033 = lean_ctor_get(x_1032, 1);
lean_inc(x_1033);
if (lean_obj_tag(x_1033) == 3)
{
lean_object* x_1034; 
x_1034 = lean_ctor_get(x_1032, 2);
lean_inc(x_1034);
lean_dec(x_1032);
if (lean_obj_tag(x_1034) == 3)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1035 = lean_ctor_get(x_1031, 1);
lean_inc(x_1035);
lean_dec(x_1031);
x_1036 = lean_ctor_get(x_1033, 0);
lean_inc(x_1036);
lean_dec(x_1033);
x_1037 = lean_ctor_get(x_1034, 0);
lean_inc(x_1037);
lean_dec(x_1034);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1038 = l_Lean_Meta_decLevel(x_1026, x_3, x_4, x_5, x_6, x_1035);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
lean_dec(x_1038);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1041 = l_Lean_Meta_decLevel(x_1036, x_3, x_4, x_5, x_6, x_1040);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; lean_object* x_1043; uint8_t x_1044; lean_object* x_1045; 
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
lean_dec(x_1041);
x_1044 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1039);
x_1045 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1039, x_1042, x_1044, x_3, x_4, x_5, x_6, x_1043);
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1046; uint8_t x_1047; 
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
x_1047 = lean_unbox(x_1046);
lean_dec(x_1046);
if (x_1047 == 0)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1027);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1048 = lean_ctor_get(x_1045, 1);
lean_inc(x_1048);
if (lean_is_exclusive(x_1045)) {
 lean_ctor_release(x_1045, 0);
 lean_ctor_release(x_1045, 1);
 x_1049 = x_1045;
} else {
 lean_dec_ref(x_1045);
 x_1049 = lean_box(0);
}
x_1050 = lean_box(0);
if (lean_is_scalar(x_1049)) {
 x_1051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1051 = x_1049;
}
lean_ctor_set(x_1051, 0, x_1050);
lean_ctor_set(x_1051, 1, x_1048);
return x_1051;
}
else
{
lean_object* x_1052; lean_object* x_1053; 
x_1052 = lean_ctor_get(x_1045, 1);
lean_inc(x_1052);
lean_dec(x_1045);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1053 = l_Lean_Meta_decLevel(x_1027, x_3, x_4, x_5, x_6, x_1052);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1053, 1);
lean_inc(x_1055);
lean_dec(x_1053);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1056 = l_Lean_Meta_decLevel(x_1037, x_3, x_4, x_5, x_6, x_1055);
if (lean_obj_tag(x_1056) == 0)
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1056, 1);
lean_inc(x_1058);
lean_dec(x_1056);
x_1059 = lean_box(0);
x_1060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1060, 0, x_1057);
lean_ctor_set(x_1060, 1, x_1059);
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1054);
lean_ctor_set(x_1061, 1, x_1060);
x_1062 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1062, 0, x_1039);
lean_ctor_set(x_1062, 1, x_1061);
x_1063 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1064 = l_Lean_Expr_const___override(x_1063, x_1062);
x_1065 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_1006);
x_1066 = lean_array_push(x_1065, x_1006);
lean_inc(x_995);
x_1067 = lean_array_push(x_1066, x_995);
x_1068 = l_Lean_mkAppN(x_1064, x_1067);
x_1069 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1070 = l_Lean_Meta_trySynthInstance(x_1068, x_1069, x_3, x_4, x_5, x_6, x_1058);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
if (lean_obj_tag(x_1071) == 1)
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
lean_dec(x_1070);
x_1073 = lean_ctor_get(x_1071, 0);
lean_inc(x_1073);
lean_dec(x_1071);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1007);
x_1074 = l_Lean_Meta_getDecLevel(x_1007, x_3, x_4, x_5, x_6, x_1072);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
lean_dec(x_1074);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1077 = l_Lean_Meta_getDecLevel(x_15, x_3, x_4, x_5, x_6, x_1076);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
lean_dec(x_1077);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1080 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_1079);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1080, 1);
lean_inc(x_1082);
lean_dec(x_1080);
x_1083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1083, 0, x_1081);
lean_ctor_set(x_1083, 1, x_1059);
x_1084 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1084, 0, x_1078);
lean_ctor_set(x_1084, 1, x_1083);
x_1085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1085, 0, x_1075);
lean_ctor_set(x_1085, 1, x_1084);
x_1086 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_1085);
x_1087 = l_Lean_Expr_const___override(x_1086, x_1085);
x_1088 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_1006);
x_1089 = lean_array_push(x_1088, x_1006);
lean_inc(x_995);
x_1090 = lean_array_push(x_1089, x_995);
lean_inc(x_1073);
x_1091 = lean_array_push(x_1090, x_1073);
lean_inc(x_1007);
x_1092 = lean_array_push(x_1091, x_1007);
lean_inc(x_1);
x_1093 = lean_array_push(x_1092, x_1);
x_1094 = l_Lean_mkAppN(x_1087, x_1093);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1094);
x_1095 = lean_infer_type(x_1094, x_3, x_4, x_5, x_6, x_1082);
if (lean_obj_tag(x_1095) == 0)
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = lean_ctor_get(x_1095, 0);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1095, 1);
lean_inc(x_1097);
lean_dec(x_1095);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_1098 = l_Lean_Meta_isExprDefEq(x_9, x_1096, x_3, x_4, x_5, x_6, x_1097);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; uint8_t x_1100; 
x_1099 = lean_ctor_get(x_1098, 0);
lean_inc(x_1099);
x_1100 = lean_unbox(x_1099);
lean_dec(x_1099);
if (x_1100 == 0)
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_1094);
lean_dec(x_1004);
x_1101 = lean_ctor_get(x_1098, 1);
lean_inc(x_1101);
lean_dec(x_1098);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_995);
x_1102 = l_Lean_Meta_isMonad_x3f(x_995, x_3, x_4, x_5, x_6, x_1101);
x_1103 = lean_ctor_get(x_1102, 0);
lean_inc(x_1103);
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
lean_dec(x_1085);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1104 = lean_ctor_get(x_1102, 1);
lean_inc(x_1104);
if (lean_is_exclusive(x_1102)) {
 lean_ctor_release(x_1102, 0);
 lean_ctor_release(x_1102, 1);
 x_1105 = x_1102;
} else {
 lean_dec_ref(x_1102);
 x_1105 = lean_box(0);
}
if (lean_is_scalar(x_1105)) {
 x_1106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1106 = x_1105;
}
lean_ctor_set(x_1106, 0, x_1069);
lean_ctor_set(x_1106, 1, x_1104);
return x_1106;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1102, 1);
lean_inc(x_1107);
lean_dec(x_1102);
x_1108 = lean_ctor_get(x_1103, 0);
lean_inc(x_1108);
lean_dec(x_1103);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1007);
x_1109 = l_Lean_Meta_getLevel(x_1007, x_3, x_4, x_5, x_6, x_1107);
if (lean_obj_tag(x_1109) == 0)
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
x_1110 = lean_ctor_get(x_1109, 0);
lean_inc(x_1110);
x_1111 = lean_ctor_get(x_1109, 1);
lean_inc(x_1111);
lean_dec(x_1109);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_996);
x_1112 = l_Lean_Meta_getLevel(x_996, x_3, x_4, x_5, x_6, x_1111);
if (lean_obj_tag(x_1112) == 0)
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; uint8_t x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1113 = lean_ctor_get(x_1112, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1112, 1);
lean_inc(x_1114);
lean_dec(x_1112);
x_1115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1115, 0, x_1113);
lean_ctor_set(x_1115, 1, x_1059);
x_1116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1116, 0, x_1110);
lean_ctor_set(x_1116, 1, x_1115);
x_1117 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1118 = l_Lean_Expr_const___override(x_1117, x_1116);
x_1119 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_1007);
x_1120 = lean_array_push(x_1119, x_1007);
x_1121 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_1122 = lean_array_push(x_1120, x_1121);
lean_inc(x_996);
x_1123 = lean_array_push(x_1122, x_996);
x_1124 = l_Lean_mkAppN(x_1118, x_1123);
x_1125 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_1126 = 0;
lean_inc(x_1007);
x_1127 = l_Lean_Expr_forallE___override(x_1125, x_1007, x_1124, x_1126);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1128 = l_Lean_Meta_trySynthInstance(x_1127, x_1069, x_3, x_4, x_5, x_6, x_1114);
if (lean_obj_tag(x_1128) == 0)
{
lean_object* x_1129; 
x_1129 = lean_ctor_get(x_1128, 0);
lean_inc(x_1129);
if (lean_obj_tag(x_1129) == 1)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1130 = lean_ctor_get(x_1128, 1);
lean_inc(x_1130);
lean_dec(x_1128);
x_1131 = lean_ctor_get(x_1129, 0);
lean_inc(x_1131);
lean_dec(x_1129);
x_1132 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_1133 = l_Lean_Expr_const___override(x_1132, x_1085);
x_1134 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_1135 = lean_array_push(x_1134, x_1006);
x_1136 = lean_array_push(x_1135, x_995);
x_1137 = lean_array_push(x_1136, x_1007);
x_1138 = lean_array_push(x_1137, x_996);
x_1139 = lean_array_push(x_1138, x_1073);
x_1140 = lean_array_push(x_1139, x_1131);
x_1141 = lean_array_push(x_1140, x_1108);
x_1142 = lean_array_push(x_1141, x_1);
x_1143 = l_Lean_mkAppN(x_1133, x_1142);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1144 = l_Lean_Meta_expandCoe(x_1143, x_3, x_4, x_5, x_6, x_1130);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
lean_dec(x_1144);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1145);
x_1147 = lean_infer_type(x_1145, x_3, x_4, x_5, x_6, x_1146);
if (lean_obj_tag(x_1147) == 0)
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1148 = lean_ctor_get(x_1147, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1147, 1);
lean_inc(x_1149);
lean_dec(x_1147);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1150 = l_Lean_Meta_isExprDefEq(x_9, x_1148, x_3, x_4, x_5, x_6, x_1149);
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; uint8_t x_1152; 
x_1151 = lean_ctor_get(x_1150, 0);
lean_inc(x_1151);
x_1152 = lean_unbox(x_1151);
lean_dec(x_1151);
if (x_1152 == 0)
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_1145);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1153 = lean_ctor_get(x_1150, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_1150)) {
 lean_ctor_release(x_1150, 0);
 lean_ctor_release(x_1150, 1);
 x_1154 = x_1150;
} else {
 lean_dec_ref(x_1150);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_1069);
lean_ctor_set(x_1155, 1, x_1153);
return x_1155;
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
x_1156 = lean_ctor_get(x_1150, 1);
lean_inc(x_1156);
lean_dec(x_1150);
x_1157 = lean_box(0);
x_1158 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1145, x_1157, x_3, x_4, x_5, x_6, x_1156);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1158, 1);
lean_inc(x_1160);
if (lean_is_exclusive(x_1158)) {
 lean_ctor_release(x_1158, 0);
 lean_ctor_release(x_1158, 1);
 x_1161 = x_1158;
} else {
 lean_dec_ref(x_1158);
 x_1161 = lean_box(0);
}
if (lean_is_scalar(x_1161)) {
 x_1162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1162 = x_1161;
}
lean_ctor_set(x_1162, 0, x_1159);
lean_ctor_set(x_1162, 1, x_1160);
return x_1162;
}
}
else
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_1145);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1163 = lean_ctor_get(x_1150, 1);
lean_inc(x_1163);
if (lean_is_exclusive(x_1150)) {
 lean_ctor_release(x_1150, 0);
 lean_ctor_release(x_1150, 1);
 x_1164 = x_1150;
} else {
 lean_dec_ref(x_1150);
 x_1164 = lean_box(0);
}
if (lean_is_scalar(x_1164)) {
 x_1165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1165 = x_1164;
 lean_ctor_set_tag(x_1165, 0);
}
lean_ctor_set(x_1165, 0, x_1069);
lean_ctor_set(x_1165, 1, x_1163);
return x_1165;
}
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1145);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1166 = lean_ctor_get(x_1147, 1);
lean_inc(x_1166);
if (lean_is_exclusive(x_1147)) {
 lean_ctor_release(x_1147, 0);
 lean_ctor_release(x_1147, 1);
 x_1167 = x_1147;
} else {
 lean_dec_ref(x_1147);
 x_1167 = lean_box(0);
}
if (lean_is_scalar(x_1167)) {
 x_1168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1168 = x_1167;
 lean_ctor_set_tag(x_1168, 0);
}
lean_ctor_set(x_1168, 0, x_1069);
lean_ctor_set(x_1168, 1, x_1166);
return x_1168;
}
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1169 = lean_ctor_get(x_1144, 1);
lean_inc(x_1169);
if (lean_is_exclusive(x_1144)) {
 lean_ctor_release(x_1144, 0);
 lean_ctor_release(x_1144, 1);
 x_1170 = x_1144;
} else {
 lean_dec_ref(x_1144);
 x_1170 = lean_box(0);
}
if (lean_is_scalar(x_1170)) {
 x_1171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1171 = x_1170;
 lean_ctor_set_tag(x_1171, 0);
}
lean_ctor_set(x_1171, 0, x_1069);
lean_ctor_set(x_1171, 1, x_1169);
return x_1171;
}
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
lean_dec(x_1129);
lean_dec(x_1108);
lean_dec(x_1085);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1172 = lean_ctor_get(x_1128, 1);
lean_inc(x_1172);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1173 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1173 = lean_box(0);
}
if (lean_is_scalar(x_1173)) {
 x_1174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1174 = x_1173;
}
lean_ctor_set(x_1174, 0, x_1069);
lean_ctor_set(x_1174, 1, x_1172);
return x_1174;
}
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
lean_dec(x_1108);
lean_dec(x_1085);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1175 = lean_ctor_get(x_1128, 1);
lean_inc(x_1175);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1176 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1176 = lean_box(0);
}
if (lean_is_scalar(x_1176)) {
 x_1177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1177 = x_1176;
 lean_ctor_set_tag(x_1177, 0);
}
lean_ctor_set(x_1177, 0, x_1069);
lean_ctor_set(x_1177, 1, x_1175);
return x_1177;
}
}
else
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
lean_dec(x_1110);
lean_dec(x_1108);
lean_dec(x_1085);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1178 = lean_ctor_get(x_1112, 1);
lean_inc(x_1178);
if (lean_is_exclusive(x_1112)) {
 lean_ctor_release(x_1112, 0);
 lean_ctor_release(x_1112, 1);
 x_1179 = x_1112;
} else {
 lean_dec_ref(x_1112);
 x_1179 = lean_box(0);
}
if (lean_is_scalar(x_1179)) {
 x_1180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1180 = x_1179;
 lean_ctor_set_tag(x_1180, 0);
}
lean_ctor_set(x_1180, 0, x_1069);
lean_ctor_set(x_1180, 1, x_1178);
return x_1180;
}
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
lean_dec(x_1108);
lean_dec(x_1085);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1181 = lean_ctor_get(x_1109, 1);
lean_inc(x_1181);
if (lean_is_exclusive(x_1109)) {
 lean_ctor_release(x_1109, 0);
 lean_ctor_release(x_1109, 1);
 x_1182 = x_1109;
} else {
 lean_dec_ref(x_1109);
 x_1182 = lean_box(0);
}
if (lean_is_scalar(x_1182)) {
 x_1183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1183 = x_1182;
 lean_ctor_set_tag(x_1183, 0);
}
lean_ctor_set(x_1183, 0, x_1069);
lean_ctor_set(x_1183, 1, x_1181);
return x_1183;
}
}
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
lean_dec(x_1085);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1184 = lean_ctor_get(x_1098, 1);
lean_inc(x_1184);
if (lean_is_exclusive(x_1098)) {
 lean_ctor_release(x_1098, 0);
 lean_ctor_release(x_1098, 1);
 x_1185 = x_1098;
} else {
 lean_dec_ref(x_1098);
 x_1185 = lean_box(0);
}
if (lean_is_scalar(x_1004)) {
 x_1186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1186 = x_1004;
}
lean_ctor_set(x_1186, 0, x_1094);
if (lean_is_scalar(x_1185)) {
 x_1187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1187 = x_1185;
}
lean_ctor_set(x_1187, 0, x_1186);
lean_ctor_set(x_1187, 1, x_1184);
return x_1187;
}
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
lean_dec(x_1094);
lean_dec(x_1085);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1188 = lean_ctor_get(x_1098, 1);
lean_inc(x_1188);
if (lean_is_exclusive(x_1098)) {
 lean_ctor_release(x_1098, 0);
 lean_ctor_release(x_1098, 1);
 x_1189 = x_1098;
} else {
 lean_dec_ref(x_1098);
 x_1189 = lean_box(0);
}
if (lean_is_scalar(x_1189)) {
 x_1190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1190 = x_1189;
 lean_ctor_set_tag(x_1190, 0);
}
lean_ctor_set(x_1190, 0, x_1069);
lean_ctor_set(x_1190, 1, x_1188);
return x_1190;
}
}
else
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
lean_dec(x_1094);
lean_dec(x_1085);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1191 = lean_ctor_get(x_1095, 1);
lean_inc(x_1191);
if (lean_is_exclusive(x_1095)) {
 lean_ctor_release(x_1095, 0);
 lean_ctor_release(x_1095, 1);
 x_1192 = x_1095;
} else {
 lean_dec_ref(x_1095);
 x_1192 = lean_box(0);
}
if (lean_is_scalar(x_1192)) {
 x_1193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1193 = x_1192;
 lean_ctor_set_tag(x_1193, 0);
}
lean_ctor_set(x_1193, 0, x_1069);
lean_ctor_set(x_1193, 1, x_1191);
return x_1193;
}
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
lean_dec(x_1078);
lean_dec(x_1075);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1194 = lean_ctor_get(x_1080, 1);
lean_inc(x_1194);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 lean_ctor_release(x_1080, 1);
 x_1195 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1195 = lean_box(0);
}
if (lean_is_scalar(x_1195)) {
 x_1196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1196 = x_1195;
 lean_ctor_set_tag(x_1196, 0);
}
lean_ctor_set(x_1196, 0, x_1069);
lean_ctor_set(x_1196, 1, x_1194);
return x_1196;
}
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
lean_dec(x_1075);
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1197 = lean_ctor_get(x_1077, 1);
lean_inc(x_1197);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1198 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1198 = lean_box(0);
}
if (lean_is_scalar(x_1198)) {
 x_1199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1199 = x_1198;
 lean_ctor_set_tag(x_1199, 0);
}
lean_ctor_set(x_1199, 0, x_1069);
lean_ctor_set(x_1199, 1, x_1197);
return x_1199;
}
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
lean_dec(x_1073);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1200 = lean_ctor_get(x_1074, 1);
lean_inc(x_1200);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1201 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1201 = lean_box(0);
}
if (lean_is_scalar(x_1201)) {
 x_1202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1202 = x_1201;
 lean_ctor_set_tag(x_1202, 0);
}
lean_ctor_set(x_1202, 0, x_1069);
lean_ctor_set(x_1202, 1, x_1200);
return x_1202;
}
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
lean_dec(x_1071);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1203 = lean_ctor_get(x_1070, 1);
lean_inc(x_1203);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 lean_ctor_release(x_1070, 1);
 x_1204 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1204 = lean_box(0);
}
if (lean_is_scalar(x_1204)) {
 x_1205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1205 = x_1204;
}
lean_ctor_set(x_1205, 0, x_1069);
lean_ctor_set(x_1205, 1, x_1203);
return x_1205;
}
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1206 = lean_ctor_get(x_1070, 1);
lean_inc(x_1206);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 lean_ctor_release(x_1070, 1);
 x_1207 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1207 = lean_box(0);
}
if (lean_is_scalar(x_1207)) {
 x_1208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1208 = x_1207;
 lean_ctor_set_tag(x_1208, 0);
}
lean_ctor_set(x_1208, 0, x_1069);
lean_ctor_set(x_1208, 1, x_1206);
return x_1208;
}
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
lean_dec(x_1054);
lean_dec(x_1039);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1209 = lean_ctor_get(x_1056, 1);
lean_inc(x_1209);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1210 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1210 = lean_box(0);
}
x_1211 = lean_box(0);
if (lean_is_scalar(x_1210)) {
 x_1212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1212 = x_1210;
 lean_ctor_set_tag(x_1212, 0);
}
lean_ctor_set(x_1212, 0, x_1211);
lean_ctor_set(x_1212, 1, x_1209);
return x_1212;
}
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1213 = lean_ctor_get(x_1053, 1);
lean_inc(x_1213);
if (lean_is_exclusive(x_1053)) {
 lean_ctor_release(x_1053, 0);
 lean_ctor_release(x_1053, 1);
 x_1214 = x_1053;
} else {
 lean_dec_ref(x_1053);
 x_1214 = lean_box(0);
}
x_1215 = lean_box(0);
if (lean_is_scalar(x_1214)) {
 x_1216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1216 = x_1214;
 lean_ctor_set_tag(x_1216, 0);
}
lean_ctor_set(x_1216, 0, x_1215);
lean_ctor_set(x_1216, 1, x_1213);
return x_1216;
}
}
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1027);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1217 = lean_ctor_get(x_1045, 1);
lean_inc(x_1217);
if (lean_is_exclusive(x_1045)) {
 lean_ctor_release(x_1045, 0);
 lean_ctor_release(x_1045, 1);
 x_1218 = x_1045;
} else {
 lean_dec_ref(x_1045);
 x_1218 = lean_box(0);
}
x_1219 = lean_box(0);
if (lean_is_scalar(x_1218)) {
 x_1220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1220 = x_1218;
 lean_ctor_set_tag(x_1220, 0);
}
lean_ctor_set(x_1220, 0, x_1219);
lean_ctor_set(x_1220, 1, x_1217);
return x_1220;
}
}
else
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1027);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1221 = lean_ctor_get(x_1041, 1);
lean_inc(x_1221);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1222 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1222 = lean_box(0);
}
x_1223 = lean_box(0);
if (lean_is_scalar(x_1222)) {
 x_1224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1224 = x_1222;
 lean_ctor_set_tag(x_1224, 0);
}
lean_ctor_set(x_1224, 0, x_1223);
lean_ctor_set(x_1224, 1, x_1221);
return x_1224;
}
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1027);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1225 = lean_ctor_get(x_1038, 1);
lean_inc(x_1225);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1226 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1226 = lean_box(0);
}
x_1227 = lean_box(0);
if (lean_is_scalar(x_1226)) {
 x_1228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1228 = x_1226;
 lean_ctor_set_tag(x_1228, 0);
}
lean_ctor_set(x_1228, 0, x_1227);
lean_ctor_set(x_1228, 1, x_1225);
return x_1228;
}
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1229 = lean_ctor_get(x_1031, 1);
lean_inc(x_1229);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1230 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1230 = lean_box(0);
}
x_1231 = lean_box(0);
if (lean_is_scalar(x_1230)) {
 x_1232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1232 = x_1230;
}
lean_ctor_set(x_1232, 0, x_1231);
lean_ctor_set(x_1232, 1, x_1229);
return x_1232;
}
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1233 = lean_ctor_get(x_1031, 1);
lean_inc(x_1233);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1234 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1234 = lean_box(0);
}
x_1235 = lean_box(0);
if (lean_is_scalar(x_1234)) {
 x_1236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1236 = x_1234;
}
lean_ctor_set(x_1236, 0, x_1235);
lean_ctor_set(x_1236, 1, x_1233);
return x_1236;
}
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
lean_dec(x_1032);
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1237 = lean_ctor_get(x_1031, 1);
lean_inc(x_1237);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1238 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1238 = lean_box(0);
}
x_1239 = lean_box(0);
if (lean_is_scalar(x_1238)) {
 x_1240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1240 = x_1238;
}
lean_ctor_set(x_1240, 0, x_1239);
lean_ctor_set(x_1240, 1, x_1237);
return x_1240;
}
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1241 = lean_ctor_get(x_1031, 1);
lean_inc(x_1241);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1242 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1242 = lean_box(0);
}
x_1243 = lean_box(0);
if (lean_is_scalar(x_1242)) {
 x_1244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1244 = x_1242;
 lean_ctor_set_tag(x_1244, 0);
}
lean_ctor_set(x_1244, 0, x_1243);
lean_ctor_set(x_1244, 1, x_1241);
return x_1244;
}
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1245 = lean_ctor_get(x_1028, 1);
lean_inc(x_1245);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 lean_ctor_release(x_1028, 1);
 x_1246 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1246 = lean_box(0);
}
x_1247 = lean_box(0);
if (lean_is_scalar(x_1246)) {
 x_1248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1248 = x_1246;
 lean_ctor_set_tag(x_1248, 0);
}
lean_ctor_set(x_1248, 0, x_1247);
lean_ctor_set(x_1248, 1, x_1245);
return x_1248;
}
}
else
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1249 = lean_ctor_get(x_1021, 1);
lean_inc(x_1249);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1250 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1250 = lean_box(0);
}
x_1251 = lean_box(0);
if (lean_is_scalar(x_1250)) {
 x_1252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1252 = x_1250;
}
lean_ctor_set(x_1252, 0, x_1251);
lean_ctor_set(x_1252, 1, x_1249);
return x_1252;
}
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1253 = lean_ctor_get(x_1021, 1);
lean_inc(x_1253);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1254 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1254 = lean_box(0);
}
x_1255 = lean_box(0);
if (lean_is_scalar(x_1254)) {
 x_1256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1256 = x_1254;
}
lean_ctor_set(x_1256, 0, x_1255);
lean_ctor_set(x_1256, 1, x_1253);
return x_1256;
}
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
lean_dec(x_1022);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1257 = lean_ctor_get(x_1021, 1);
lean_inc(x_1257);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1258 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1258 = lean_box(0);
}
x_1259 = lean_box(0);
if (lean_is_scalar(x_1258)) {
 x_1260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1260 = x_1258;
}
lean_ctor_set(x_1260, 0, x_1259);
lean_ctor_set(x_1260, 1, x_1257);
return x_1260;
}
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1261 = lean_ctor_get(x_1021, 1);
lean_inc(x_1261);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1262 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1262 = lean_box(0);
}
x_1263 = lean_box(0);
if (lean_is_scalar(x_1262)) {
 x_1264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1264 = x_1262;
 lean_ctor_set_tag(x_1264, 0);
}
lean_ctor_set(x_1264, 0, x_1263);
lean_ctor_set(x_1264, 1, x_1261);
return x_1264;
}
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1265 = lean_ctor_get(x_1018, 1);
lean_inc(x_1265);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 x_1266 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1266 = lean_box(0);
}
x_1267 = lean_box(0);
if (lean_is_scalar(x_1266)) {
 x_1268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1268 = x_1266;
 lean_ctor_set_tag(x_1268, 0);
}
lean_ctor_set(x_1268, 0, x_1267);
lean_ctor_set(x_1268, 1, x_1265);
return x_1268;
}
}
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
lean_dec(x_15);
lean_dec(x_9);
x_1269 = lean_ctor_get(x_1008, 1);
lean_inc(x_1269);
lean_dec(x_1008);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1270 = l_Lean_Meta_isMonad_x3f(x_995, x_3, x_4, x_5, x_6, x_1269);
x_1271 = lean_ctor_get(x_1270, 0);
lean_inc(x_1271);
if (lean_obj_tag(x_1271) == 0)
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1272 = lean_ctor_get(x_1270, 1);
lean_inc(x_1272);
if (lean_is_exclusive(x_1270)) {
 lean_ctor_release(x_1270, 0);
 lean_ctor_release(x_1270, 1);
 x_1273 = x_1270;
} else {
 lean_dec_ref(x_1270);
 x_1273 = lean_box(0);
}
x_1274 = lean_box(0);
if (lean_is_scalar(x_1273)) {
 x_1275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1275 = x_1273;
}
lean_ctor_set(x_1275, 0, x_1274);
lean_ctor_set(x_1275, 1, x_1272);
return x_1275;
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
x_1276 = lean_ctor_get(x_1270, 1);
lean_inc(x_1276);
lean_dec(x_1270);
x_1277 = lean_ctor_get(x_1271, 0);
lean_inc(x_1277);
if (lean_is_exclusive(x_1271)) {
 lean_ctor_release(x_1271, 0);
 x_1278 = x_1271;
} else {
 lean_dec_ref(x_1271);
 x_1278 = lean_box(0);
}
if (lean_is_scalar(x_1278)) {
 x_1279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1279 = x_1278;
}
lean_ctor_set(x_1279, 0, x_1006);
if (lean_is_scalar(x_1004)) {
 x_1280 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1280 = x_1004;
}
lean_ctor_set(x_1280, 0, x_1007);
x_1281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1281, 0, x_996);
x_1282 = lean_box(0);
x_1283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1283, 0, x_1277);
x_1284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1284, 0, x_1);
x_1285 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_1286 = lean_array_push(x_1285, x_1279);
x_1287 = lean_array_push(x_1286, x_1280);
x_1288 = lean_array_push(x_1287, x_1281);
x_1289 = lean_array_push(x_1288, x_1282);
x_1290 = lean_array_push(x_1289, x_1283);
x_1291 = lean_array_push(x_1290, x_1284);
x_1292 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1293 = l_Lean_Meta_mkAppOptM(x_1292, x_1291, x_3, x_4, x_5, x_6, x_1276);
if (lean_obj_tag(x_1293) == 0)
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1294 = lean_ctor_get(x_1293, 0);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_1293, 1);
lean_inc(x_1295);
lean_dec(x_1293);
x_1296 = l_Lean_Meta_expandCoe(x_1294, x_3, x_4, x_5, x_6, x_1295);
if (lean_obj_tag(x_1296) == 0)
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1297 = lean_ctor_get(x_1296, 0);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1296, 1);
lean_inc(x_1298);
if (lean_is_exclusive(x_1296)) {
 lean_ctor_release(x_1296, 0);
 lean_ctor_release(x_1296, 1);
 x_1299 = x_1296;
} else {
 lean_dec_ref(x_1296);
 x_1299 = lean_box(0);
}
x_1300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1300, 0, x_1297);
if (lean_is_scalar(x_1299)) {
 x_1301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1301 = x_1299;
}
lean_ctor_set(x_1301, 0, x_1300);
lean_ctor_set(x_1301, 1, x_1298);
return x_1301;
}
else
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; 
x_1302 = lean_ctor_get(x_1296, 1);
lean_inc(x_1302);
if (lean_is_exclusive(x_1296)) {
 lean_ctor_release(x_1296, 0);
 lean_ctor_release(x_1296, 1);
 x_1303 = x_1296;
} else {
 lean_dec_ref(x_1296);
 x_1303 = lean_box(0);
}
if (lean_is_scalar(x_1303)) {
 x_1304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1304 = x_1303;
 lean_ctor_set_tag(x_1304, 0);
}
lean_ctor_set(x_1304, 0, x_1282);
lean_ctor_set(x_1304, 1, x_1302);
return x_1304;
}
}
else
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1305 = lean_ctor_get(x_1293, 1);
lean_inc(x_1305);
if (lean_is_exclusive(x_1293)) {
 lean_ctor_release(x_1293, 0);
 lean_ctor_release(x_1293, 1);
 x_1306 = x_1293;
} else {
 lean_dec_ref(x_1293);
 x_1306 = lean_box(0);
}
if (lean_is_scalar(x_1306)) {
 x_1307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1307 = x_1306;
 lean_ctor_set_tag(x_1307, 0);
}
lean_ctor_set(x_1307, 0, x_1282);
lean_ctor_set(x_1307, 1, x_1305);
return x_1307;
}
}
}
}
else
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1308 = lean_ctor_get(x_1008, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1008, 1);
lean_inc(x_1309);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 lean_ctor_release(x_1008, 1);
 x_1310 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1310 = lean_box(0);
}
if (lean_is_scalar(x_1310)) {
 x_1311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1311 = x_1310;
}
lean_ctor_set(x_1311, 0, x_1308);
lean_ctor_set(x_1311, 1, x_1309);
return x_1311;
}
}
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1312 = lean_ctor_get(x_997, 0);
lean_inc(x_1312);
x_1313 = lean_ctor_get(x_997, 1);
lean_inc(x_1313);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 lean_ctor_release(x_997, 1);
 x_1314 = x_997;
} else {
 lean_dec_ref(x_997);
 x_1314 = lean_box(0);
}
if (lean_is_scalar(x_1314)) {
 x_1315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1315 = x_1314;
}
lean_ctor_set(x_1315, 0, x_1312);
lean_ctor_set(x_1315, 1, x_1313);
return x_1315;
}
}
}
}
else
{
uint8_t x_1316; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1316 = !lean_is_exclusive(x_17);
if (x_1316 == 0)
{
return x_17;
}
else
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; 
x_1317 = lean_ctor_get(x_17, 0);
x_1318 = lean_ctor_get(x_17, 1);
lean_inc(x_1318);
lean_inc(x_1317);
lean_dec(x_17);
x_1319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1319, 0, x_1317);
lean_ctor_set(x_1319, 1, x_1318);
return x_1319;
}
}
}
else
{
uint8_t x_1320; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1320 = !lean_is_exclusive(x_11);
if (x_1320 == 0)
{
return x_11;
}
else
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; 
x_1321 = lean_ctor_get(x_11, 0);
x_1322 = lean_ctor_get(x_11, 1);
lean_inc(x_1322);
lean_inc(x_1321);
lean_dec(x_11);
x_1323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1323, 0, x_1321);
lean_ctor_set(x_1323, 1, x_1322);
return x_1323;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_coerceSimple_x3f(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_whnfR(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_isForall(x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Meta_coerceSimple_x3f(x_2, x_1, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
lean_object* x_14; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_14 = l_Lean_Meta_coerceToFunction_x3f(x_2, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_coerceSimple_x3f(x_2, x_1, x_4, x_5, x_6, x_7, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_20 = lean_infer_type(x_19, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_23 = l_Lean_Meta_isExprDefEq(x_21, x_1, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_coerceSimple_x3f(x_2, x_1, x_4, x_5, x_6, x_7, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_19);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
return x_9;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_coerceMonadLift_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l_Lean_Meta_coerce_x3f___lambda__2(x_2, x_1, x_11, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_coerce_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_coerce_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Coe(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__8);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_coeDeclAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_coeDeclAttr);
lean_dec_ref(res);
}l_Lean_Meta_isCoeDecl___closed__1 = _init_l_Lean_Meta_isCoeDecl___closed__1();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__1);
l_Lean_Meta_expandCoe___lambda__1___closed__1 = _init_l_Lean_Meta_expandCoe___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_expandCoe___lambda__1___closed__1);
l_Lean_Meta_expandCoe___lambda__2___closed__1 = _init_l_Lean_Meta_expandCoe___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_expandCoe___lambda__2___closed__1);
l_Lean_Meta_expandCoe___closed__1 = _init_l_Lean_Meta_expandCoe___closed__1();
lean_mark_persistent(l_Lean_Meta_expandCoe___closed__1);
l_Lean_Meta_expandCoe___closed__2 = _init_l_Lean_Meta_expandCoe___closed__2();
lean_mark_persistent(l_Lean_Meta_expandCoe___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_290_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_autoLift = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_autoLift);
lean_dec_ref(res);
}l_Lean_Meta_coerceSimple_x3f___closed__1 = _init_l_Lean_Meta_coerceSimple_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__1);
l_Lean_Meta_coerceSimple_x3f___closed__2 = _init_l_Lean_Meta_coerceSimple_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__2);
l_Lean_Meta_coerceSimple_x3f___closed__3 = _init_l_Lean_Meta_coerceSimple_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__3);
l_Lean_Meta_coerceSimple_x3f___closed__4 = _init_l_Lean_Meta_coerceSimple_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__4);
l_Lean_Meta_coerceSimple_x3f___closed__5 = _init_l_Lean_Meta_coerceSimple_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__5);
l_Lean_Meta_coerceSimple_x3f___closed__6 = _init_l_Lean_Meta_coerceSimple_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__6);
l_Lean_Meta_coerceSimple_x3f___closed__7 = _init_l_Lean_Meta_coerceSimple_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__7);
l_Lean_Meta_coerceSimple_x3f___closed__8 = _init_l_Lean_Meta_coerceSimple_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__8);
l_Lean_Meta_coerceSimple_x3f___closed__9 = _init_l_Lean_Meta_coerceSimple_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__9);
l_Lean_Meta_coerceSimple_x3f___closed__10 = _init_l_Lean_Meta_coerceSimple_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__10);
l_Lean_Meta_coerceSimple_x3f___closed__11 = _init_l_Lean_Meta_coerceSimple_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__11);
l_Lean_Meta_coerceSimple_x3f___closed__12 = _init_l_Lean_Meta_coerceSimple_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__12);
l_Lean_Meta_coerceSimple_x3f___closed__13 = _init_l_Lean_Meta_coerceSimple_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_coerceSimple_x3f___closed__13);
l_Lean_Meta_coerceToFunction_x3f___closed__1 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__1);
l_Lean_Meta_coerceToFunction_x3f___closed__2 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__2);
l_Lean_Meta_coerceToFunction_x3f___closed__3 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__3);
l_Lean_Meta_coerceToFunction_x3f___closed__4 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__4);
l_Lean_Meta_coerceToFunction_x3f___closed__5 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__5);
l_Lean_Meta_coerceToFunction_x3f___closed__6 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__6);
l_Lean_Meta_coerceToFunction_x3f___closed__7 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__7);
l_Lean_Meta_coerceToFunction_x3f___closed__8 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__8);
l_Lean_Meta_coerceToFunction_x3f___closed__9 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__9);
l_Lean_Meta_coerceToSort_x3f___closed__1 = _init_l_Lean_Meta_coerceToSort_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___closed__1);
l_Lean_Meta_coerceToSort_x3f___closed__2 = _init_l_Lean_Meta_coerceToSort_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___closed__2);
l_Lean_Meta_coerceToSort_x3f___closed__3 = _init_l_Lean_Meta_coerceToSort_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___closed__3);
l_Lean_Meta_coerceToSort_x3f___closed__4 = _init_l_Lean_Meta_coerceToSort_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___closed__4);
l_Lean_Meta_coerceToSort_x3f___closed__5 = _init_l_Lean_Meta_coerceToSort_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___closed__5);
l_Lean_Meta_coerceToSort_x3f___closed__6 = _init_l_Lean_Meta_coerceToSort_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___closed__6);
l_Lean_Meta_coerceToSort_x3f___closed__7 = _init_l_Lean_Meta_coerceToSort_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___closed__7);
l_Lean_Meta_coerceMonadLift_x3f___closed__1 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__1);
l_Lean_Meta_coerceMonadLift_x3f___closed__2 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__2);
l_Lean_Meta_coerceMonadLift_x3f___closed__3 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__3);
l_Lean_Meta_coerceMonadLift_x3f___closed__4 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__4);
l_Lean_Meta_coerceMonadLift_x3f___closed__5 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__5);
l_Lean_Meta_coerceMonadLift_x3f___closed__6 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__6);
l_Lean_Meta_coerceMonadLift_x3f___closed__7 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__7);
l_Lean_Meta_coerceMonadLift_x3f___closed__8 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__8);
l_Lean_Meta_coerceMonadLift_x3f___closed__9 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__9);
l_Lean_Meta_coerceMonadLift_x3f___closed__10 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__10);
l_Lean_Meta_coerceMonadLift_x3f___closed__11 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__11);
l_Lean_Meta_coerceMonadLift_x3f___closed__12 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__12);
l_Lean_Meta_coerceMonadLift_x3f___closed__13 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__13);
l_Lean_Meta_coerceMonadLift_x3f___closed__14 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__14);
l_Lean_Meta_coerceMonadLift_x3f___closed__15 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__15);
l_Lean_Meta_coerceMonadLift_x3f___closed__16 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__16);
l_Lean_Meta_coerceMonadLift_x3f___closed__17 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__17);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
