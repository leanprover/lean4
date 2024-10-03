// Lean compiler output
// Module: Lean.Meta.Coe
// Imports: Lean.Meta.Transform Lean.Meta.SynthInstance Lean.Meta.AppBuilder
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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__7;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__3;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__4;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__6;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__5;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__8;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__9;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__1;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__7;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__6;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__2;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__10;
uint8_t l_Lean_Expr_isSort(lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__3;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__6;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__8;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__2;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219_(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__3;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__4;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__1;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__4;
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
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__6;
static lean_object* l_Lean_Meta_expandCoe___lambda__2___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__12;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__7;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__6;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
x_1 = lean_mk_string_unchecked("coe_decl", 8, 8);
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
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("coeDeclAttr", 11, 11);
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
x_1 = lean_mk_string_unchecked("auxiliary definition used to implement coercion (unfolded during elaboration)", 77, 77);
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
lean_dec(x_1);
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
lean_dec(x_16);
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
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = l_Lean_Expr_headBeta(x_29);
lean_ctor_set(x_22, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Lean_Expr_headBeta(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_21, 0, x_33);
return x_21;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_36 = x_22;
} else {
 lean_dec_ref(x_22);
 x_36 = lean_box(0);
}
x_37 = l_Lean_Expr_headBeta(x_35);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
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
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
x_14 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_11, x_12, x_13, x_13, x_2, x_3, x_4, x_5, x_6);
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
uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
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
x_34 = lean_ctor_get_uint8(x_8, 12);
lean_dec(x_8);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_36, 0, x_23);
lean_ctor_set_uint8(x_36, 1, x_24);
lean_ctor_set_uint8(x_36, 2, x_25);
lean_ctor_set_uint8(x_36, 3, x_26);
lean_ctor_set_uint8(x_36, 4, x_27);
lean_ctor_set_uint8(x_36, 5, x_28);
lean_ctor_set_uint8(x_36, 6, x_29);
lean_ctor_set_uint8(x_36, 7, x_30);
lean_ctor_set_uint8(x_36, 8, x_31);
lean_ctor_set_uint8(x_36, 9, x_35);
lean_ctor_set_uint8(x_36, 10, x_32);
lean_ctor_set_uint8(x_36, 11, x_33);
lean_ctor_set_uint8(x_36, 12, x_34);
lean_ctor_set(x_2, 0, x_36);
x_37 = l_Lean_Meta_expandCoe___closed__1;
x_38 = l_Lean_Meta_expandCoe___closed__2;
x_39 = 0;
x_40 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_37, x_38, x_39, x_39, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_ctor_get(x_2, 1);
x_51 = lean_ctor_get(x_2, 2);
x_52 = lean_ctor_get(x_2, 3);
x_53 = lean_ctor_get(x_2, 4);
x_54 = lean_ctor_get(x_2, 5);
x_55 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_56 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_2);
x_57 = lean_ctor_get_uint8(x_49, 0);
x_58 = lean_ctor_get_uint8(x_49, 1);
x_59 = lean_ctor_get_uint8(x_49, 2);
x_60 = lean_ctor_get_uint8(x_49, 3);
x_61 = lean_ctor_get_uint8(x_49, 4);
x_62 = lean_ctor_get_uint8(x_49, 5);
x_63 = lean_ctor_get_uint8(x_49, 6);
x_64 = lean_ctor_get_uint8(x_49, 7);
x_65 = lean_ctor_get_uint8(x_49, 8);
x_66 = lean_ctor_get_uint8(x_49, 10);
x_67 = lean_ctor_get_uint8(x_49, 11);
x_68 = lean_ctor_get_uint8(x_49, 12);
if (lean_is_exclusive(x_49)) {
 x_69 = x_49;
} else {
 lean_dec_ref(x_49);
 x_69 = lean_box(0);
}
x_70 = 3;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 0, 13);
} else {
 x_71 = x_69;
}
lean_ctor_set_uint8(x_71, 0, x_57);
lean_ctor_set_uint8(x_71, 1, x_58);
lean_ctor_set_uint8(x_71, 2, x_59);
lean_ctor_set_uint8(x_71, 3, x_60);
lean_ctor_set_uint8(x_71, 4, x_61);
lean_ctor_set_uint8(x_71, 5, x_62);
lean_ctor_set_uint8(x_71, 6, x_63);
lean_ctor_set_uint8(x_71, 7, x_64);
lean_ctor_set_uint8(x_71, 8, x_65);
lean_ctor_set_uint8(x_71, 9, x_70);
lean_ctor_set_uint8(x_71, 10, x_66);
lean_ctor_set_uint8(x_71, 11, x_67);
lean_ctor_set_uint8(x_71, 12, x_68);
x_72 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_50);
lean_ctor_set(x_72, 2, x_51);
lean_ctor_set(x_72, 3, x_52);
lean_ctor_set(x_72, 4, x_53);
lean_ctor_set(x_72, 5, x_54);
lean_ctor_set_uint8(x_72, sizeof(void*)*6, x_55);
lean_ctor_set_uint8(x_72, sizeof(void*)*6 + 1, x_56);
x_73 = l_Lean_Meta_expandCoe___closed__1;
x_74 = l_Lean_Meta_expandCoe___closed__2;
x_75 = 0;
x_76 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_73, x_74, x_75, x_75, x_72, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("autoLift", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("insert monadic lifts (i.e., `liftM` and coercions) when needed", 62, 62);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__6;
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
x_1 = lean_mk_string_unchecked("CoeT", 4, 4);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("coe", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__1;
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not coerce", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nto", 3, 3);
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
x_1 = lean_mk_string_unchecked("\ncoerced expression has wrong type:", 35, 35);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__3;
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
lean_inc(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_17);
lean_inc(x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_mk(x_24);
x_26 = l_Lean_mkAppN(x_21, x_25);
lean_dec(x_25);
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
x_38 = l_Lean_Meta_coerceSimple_x3f___closed__4;
x_39 = l_Lean_Expr_const___override(x_38, x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_17);
lean_inc(x_2);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_1);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_mk(x_43);
x_45 = l_Lean_mkAppN(x_39, x_44);
lean_dec(x_44);
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
x_57 = l_Lean_Meta_coerceSimple_x3f___closed__6;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Meta_coerceSimple_x3f___closed__8;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_indentExpr(x_2);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_coerceSimple_x3f___closed__10;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_indentExpr(x_47);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_coerceSimple_x3f___closed__11;
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
x_1 = lean_mk_string_unchecked("CoeFun", 6, 6);
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
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to coerce", 16, 16);
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
x_1 = lean_mk_string_unchecked("\nto a function, after applying `CoeFun.coe`, result is still not a function", 75, 75);
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
x_1 = lean_mk_string_unchecked("\nthis is often due to incorrect `CoeFun` instances, the synthesized instance was", 80, 80);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_17 = l_Lean_Expr_sort___override(x_15);
lean_inc(x_8);
x_18 = l_Lean_mkArrow(x_8, x_17, x_4, x_5, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = 0;
x_24 = lean_box(0);
lean_inc(x_2);
x_25 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_22, x_23, x_24, x_2, x_3, x_4, x_5, x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_29);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_11);
x_30 = l_Lean_Meta_coerceToFunction_x3f___closed__2;
lean_inc(x_18);
x_31 = l_Lean_Expr_const___override(x_30, x_18);
lean_inc(x_27);
lean_inc(x_8);
x_32 = l_Lean_mkAppB(x_31, x_8, x_27);
x_33 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Meta_trySynthInstance(x_32, x_33, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_coerceToFunction_x3f___closed__3;
x_39 = l_Lean_Expr_const___override(x_38, x_18);
lean_inc(x_1);
lean_inc(x_37);
x_40 = l_Lean_mkApp4(x_39, x_8, x_27, x_37, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_41 = l_Lean_Meta_expandCoe(x_40, x_2, x_3, x_4, x_5, x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_42);
x_44 = lean_infer_type(x_42, x_2, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_47 = lean_whnf(x_45, x_2, x_3, x_4, x_5, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Expr_isForall(x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_51 = l_Lean_indentExpr(x_1);
x_52 = l_Lean_Meta_coerceToFunction_x3f___closed__5;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_51);
lean_ctor_set(x_13, 0, x_52);
x_53 = l_Lean_Meta_coerceToFunction_x3f___closed__7;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_13);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_indentExpr(x_42);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_coerceToFunction_x3f___closed__9;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_indentExpr(x_37);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Meta_coerceSimple_x3f___closed__11;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_62, x_2, x_3, x_4, x_5, x_49);
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
lean_dec(x_37);
lean_free_object(x_13);
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_42, x_68, x_2, x_3, x_4, x_5, x_49);
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
lean_dec(x_42);
lean_dec(x_37);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_47);
if (x_70 == 0)
{
return x_47;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
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
lean_dec(x_42);
lean_dec(x_37);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_44);
if (x_74 == 0)
{
return x_44;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_44, 0);
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_44);
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
lean_dec(x_37);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_41);
if (x_78 == 0)
{
return x_41;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_41, 0);
x_80 = lean_ctor_get(x_41, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_41);
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
lean_dec(x_35);
lean_dec(x_18);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_34);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_34, 0);
lean_dec(x_83);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_34, 1);
lean_inc(x_84);
lean_dec(x_34);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_33);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_18);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_34);
if (x_86 == 0)
{
return x_34;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_34, 0);
x_88 = lean_ctor_get(x_34, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_34);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_25, 0);
x_91 = lean_ctor_get(x_25, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_25);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_15);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_93);
lean_ctor_set(x_18, 0, x_11);
x_94 = l_Lean_Meta_coerceToFunction_x3f___closed__2;
lean_inc(x_18);
x_95 = l_Lean_Expr_const___override(x_94, x_18);
lean_inc(x_90);
lean_inc(x_8);
x_96 = l_Lean_mkAppB(x_95, x_8, x_90);
x_97 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_98 = l_Lean_Meta_trySynthInstance(x_96, x_97, x_2, x_3, x_4, x_5, x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Meta_coerceToFunction_x3f___closed__3;
x_103 = l_Lean_Expr_const___override(x_102, x_18);
lean_inc(x_1);
lean_inc(x_101);
x_104 = l_Lean_mkApp4(x_103, x_8, x_90, x_101, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_105 = l_Lean_Meta_expandCoe(x_104, x_2, x_3, x_4, x_5, x_100);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_106);
x_108 = lean_infer_type(x_106, x_2, x_3, x_4, x_5, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_111 = lean_whnf(x_109, x_2, x_3, x_4, x_5, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Expr_isForall(x_112);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_115 = l_Lean_indentExpr(x_1);
x_116 = l_Lean_Meta_coerceToFunction_x3f___closed__5;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_115);
lean_ctor_set(x_13, 0, x_116);
x_117 = l_Lean_Meta_coerceToFunction_x3f___closed__7;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_13);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_indentExpr(x_106);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Meta_coerceToFunction_x3f___closed__9;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_indentExpr(x_101);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_Meta_coerceSimple_x3f___closed__11;
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_126, x_2, x_3, x_4, x_5, x_113);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_101);
lean_free_object(x_13);
lean_dec(x_1);
x_132 = lean_box(0);
x_133 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_106, x_132, x_2, x_3, x_4, x_5, x_113);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_106);
lean_dec(x_101);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_111, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_111, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_136 = x_111;
} else {
 lean_dec_ref(x_111);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_106);
lean_dec(x_101);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_ctor_get(x_108, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_108, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_140 = x_108;
} else {
 lean_dec_ref(x_108);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_101);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_ctor_get(x_105, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_105, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_144 = x_105;
} else {
 lean_dec_ref(x_105);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_99);
lean_dec(x_18);
lean_dec(x_90);
lean_free_object(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_98, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_147 = x_98;
} else {
 lean_dec_ref(x_98);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_97);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_18);
lean_dec(x_90);
lean_free_object(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_98, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_98, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_151 = x_98;
} else {
 lean_dec_ref(x_98);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_153 = lean_ctor_get(x_18, 0);
x_154 = lean_ctor_get(x_18, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_18);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_153);
x_156 = 0;
x_157 = lean_box(0);
lean_inc(x_2);
x_158 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_155, x_156, x_157, x_2, x_3, x_4, x_5, x_154);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_161;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_15);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_11);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_Meta_coerceToFunction_x3f___closed__2;
lean_inc(x_164);
x_166 = l_Lean_Expr_const___override(x_165, x_164);
lean_inc(x_159);
lean_inc(x_8);
x_167 = l_Lean_mkAppB(x_166, x_8, x_159);
x_168 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_169 = l_Lean_Meta_trySynthInstance(x_167, x_168, x_2, x_3, x_4, x_5, x_160);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 1)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Meta_coerceToFunction_x3f___closed__3;
x_174 = l_Lean_Expr_const___override(x_173, x_164);
lean_inc(x_1);
lean_inc(x_172);
x_175 = l_Lean_mkApp4(x_174, x_8, x_159, x_172, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_176 = l_Lean_Meta_expandCoe(x_175, x_2, x_3, x_4, x_5, x_171);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_177);
x_179 = lean_infer_type(x_177, x_2, x_3, x_4, x_5, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_182 = lean_whnf(x_180, x_2, x_3, x_4, x_5, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lean_Expr_isForall(x_183);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_186 = l_Lean_indentExpr(x_1);
x_187 = l_Lean_Meta_coerceToFunction_x3f___closed__5;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_186);
lean_ctor_set(x_13, 0, x_187);
x_188 = l_Lean_Meta_coerceToFunction_x3f___closed__7;
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_13);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_indentExpr(x_177);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_Meta_coerceToFunction_x3f___closed__9;
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_indentExpr(x_172);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Meta_coerceSimple_x3f___closed__11;
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_197, x_2, x_3, x_4, x_5, x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_172);
lean_free_object(x_13);
lean_dec(x_1);
x_203 = lean_box(0);
x_204 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_177, x_203, x_2, x_3, x_4, x_5, x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_177);
lean_dec(x_172);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_ctor_get(x_182, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_182, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_207 = x_182;
} else {
 lean_dec_ref(x_182);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_177);
lean_dec(x_172);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_179, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_179, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_211 = x_179;
} else {
 lean_dec_ref(x_179);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_172);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_176, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_176, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_215 = x_176;
} else {
 lean_dec_ref(x_176);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_170);
lean_dec(x_164);
lean_dec(x_159);
lean_free_object(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_169, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_218 = x_169;
} else {
 lean_dec_ref(x_169);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_168);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_164);
lean_dec(x_159);
lean_free_object(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_169, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_169, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_222 = x_169;
} else {
 lean_dec_ref(x_169);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_224 = lean_ctor_get(x_13, 0);
x_225 = lean_ctor_get(x_13, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_13);
lean_inc(x_224);
x_226 = l_Lean_Expr_sort___override(x_224);
lean_inc(x_8);
x_227 = l_Lean_mkArrow(x_8, x_226, x_4, x_5, x_225);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_228);
x_232 = 0;
x_233 = lean_box(0);
lean_inc(x_2);
x_234 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_231, x_232, x_233, x_2, x_3, x_4, x_5, x_229);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_box(0);
if (lean_is_scalar(x_237)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_237;
 lean_ctor_set_tag(x_239, 1);
}
lean_ctor_set(x_239, 0, x_224);
lean_ctor_set(x_239, 1, x_238);
if (lean_is_scalar(x_230)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_230;
 lean_ctor_set_tag(x_240, 1);
}
lean_ctor_set(x_240, 0, x_11);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_Meta_coerceToFunction_x3f___closed__2;
lean_inc(x_240);
x_242 = l_Lean_Expr_const___override(x_241, x_240);
lean_inc(x_235);
lean_inc(x_8);
x_243 = l_Lean_mkAppB(x_242, x_8, x_235);
x_244 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_245 = l_Lean_Meta_trySynthInstance(x_243, x_244, x_2, x_3, x_4, x_5, x_236);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 1)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_Meta_coerceToFunction_x3f___closed__3;
x_250 = l_Lean_Expr_const___override(x_249, x_240);
lean_inc(x_1);
lean_inc(x_248);
x_251 = l_Lean_mkApp4(x_250, x_8, x_235, x_248, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_252 = l_Lean_Meta_expandCoe(x_251, x_2, x_3, x_4, x_5, x_247);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_253);
x_255 = lean_infer_type(x_253, x_2, x_3, x_4, x_5, x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_258 = lean_whnf(x_256, x_2, x_3, x_4, x_5, x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = l_Lean_Expr_isForall(x_259);
lean_dec(x_259);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_262 = l_Lean_indentExpr(x_1);
x_263 = l_Lean_Meta_coerceToFunction_x3f___closed__5;
x_264 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
x_265 = l_Lean_Meta_coerceToFunction_x3f___closed__7;
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_Lean_indentExpr(x_253);
x_268 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lean_Meta_coerceToFunction_x3f___closed__9;
x_270 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
x_271 = l_Lean_indentExpr(x_248);
x_272 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = l_Lean_Meta_coerceSimple_x3f___closed__11;
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
x_275 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_274, x_2, x_3, x_4, x_5, x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_248);
lean_dec(x_1);
x_280 = lean_box(0);
x_281 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_253, x_280, x_2, x_3, x_4, x_5, x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_253);
lean_dec(x_248);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_282 = lean_ctor_get(x_258, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_258, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_284 = x_258;
} else {
 lean_dec_ref(x_258);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_253);
lean_dec(x_248);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_286 = lean_ctor_get(x_255, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_255, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_288 = x_255;
} else {
 lean_dec_ref(x_255);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_248);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_290 = lean_ctor_get(x_252, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_252, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_292 = x_252;
} else {
 lean_dec_ref(x_252);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_246);
lean_dec(x_240);
lean_dec(x_235);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = lean_ctor_get(x_245, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_295 = x_245;
} else {
 lean_dec_ref(x_245);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_244);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_240);
lean_dec(x_235);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = lean_ctor_get(x_245, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_245, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_299 = x_245;
} else {
 lean_dec_ref(x_245);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
}
else
{
uint8_t x_301; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_301 = !lean_is_exclusive(x_10);
if (x_301 == 0)
{
return x_10;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_10, 0);
x_303 = lean_ctor_get(x_10, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_10);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_7);
if (x_305 == 0)
{
return x_7;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_7, 0);
x_307 = lean_ctor_get(x_7, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_7);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
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
x_1 = lean_mk_string_unchecked("CoeSort", 7, 7);
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
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nto a type, after applying `CoeSort.coe`, result is still not a type", 68, 68);
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
x_1 = lean_mk_string_unchecked("\nthis is often due to incorrect `CoeSort` instances, the synthesized instance was", 81, 81);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_17 = l_Lean_Expr_sort___override(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = 0;
x_20 = lean_box(0);
lean_inc(x_2);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_18, x_19, x_20, x_2, x_3, x_4, x_5, x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box(0);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_25);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_11);
x_26 = l_Lean_Meta_coerceToSort_x3f___closed__2;
lean_inc(x_13);
x_27 = l_Lean_Expr_const___override(x_26, x_13);
lean_inc(x_23);
lean_inc(x_8);
x_28 = l_Lean_mkAppB(x_27, x_8, x_23);
x_29 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = l_Lean_Meta_trySynthInstance(x_28, x_29, x_2, x_3, x_4, x_5, x_24);
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
x_35 = l_Lean_Expr_const___override(x_34, x_13);
lean_inc(x_1);
lean_inc(x_33);
x_36 = l_Lean_mkApp4(x_35, x_8, x_23, x_33, x_1);
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
x_58 = l_Lean_Meta_coerceSimple_x3f___closed__11;
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
lean_dec(x_13);
lean_dec(x_23);
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
lean_dec(x_13);
lean_dec(x_23);
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
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_21, 0);
x_88 = lean_ctor_get(x_21, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_21);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_15);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_90);
lean_ctor_set(x_13, 0, x_11);
x_91 = l_Lean_Meta_coerceToSort_x3f___closed__2;
lean_inc(x_13);
x_92 = l_Lean_Expr_const___override(x_91, x_13);
lean_inc(x_87);
lean_inc(x_8);
x_93 = l_Lean_mkAppB(x_92, x_8, x_87);
x_94 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_95 = l_Lean_Meta_trySynthInstance(x_93, x_94, x_2, x_3, x_4, x_5, x_88);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 1)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Meta_coerceToSort_x3f___closed__3;
x_100 = l_Lean_Expr_const___override(x_99, x_13);
lean_inc(x_1);
lean_inc(x_98);
x_101 = l_Lean_mkApp4(x_100, x_8, x_87, x_98, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_102 = l_Lean_Meta_expandCoe(x_101, x_2, x_3, x_4, x_5, x_97);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_103);
x_105 = lean_infer_type(x_103, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_108 = lean_whnf(x_106, x_2, x_3, x_4, x_5, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Expr_isSort(x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_112 = l_Lean_indentExpr(x_1);
x_113 = l_Lean_Meta_coerceToFunction_x3f___closed__5;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Lean_Meta_coerceToSort_x3f___closed__5;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_indentExpr(x_103);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Meta_coerceToSort_x3f___closed__7;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_indentExpr(x_98);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Meta_coerceSimple_x3f___closed__11;
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_124, x_2, x_3, x_4, x_5, x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_98);
lean_dec(x_1);
x_130 = lean_box(0);
x_131 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_103, x_130, x_2, x_3, x_4, x_5, x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_108, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_108, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_134 = x_108;
} else {
 lean_dec_ref(x_108);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_105, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_105, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_138 = x_105;
} else {
 lean_dec_ref(x_105);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = lean_ctor_get(x_102, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_102, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_142 = x_102;
} else {
 lean_dec_ref(x_102);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_96);
lean_dec(x_13);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_95, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_145 = x_95;
} else {
 lean_dec_ref(x_95);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_94);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_13);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_ctor_get(x_95, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_95, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_149 = x_95;
} else {
 lean_dec_ref(x_95);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_151 = lean_ctor_get(x_13, 0);
x_152 = lean_ctor_get(x_13, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_13);
lean_inc(x_151);
x_153 = l_Lean_Expr_sort___override(x_151);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = 0;
x_156 = lean_box(0);
lean_inc(x_2);
x_157 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_154, x_155, x_156, x_2, x_3, x_4, x_5, x_152);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_box(0);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_160;
 lean_ctor_set_tag(x_162, 1);
}
lean_ctor_set(x_162, 0, x_151);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_11);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Meta_coerceToSort_x3f___closed__2;
lean_inc(x_163);
x_165 = l_Lean_Expr_const___override(x_164, x_163);
lean_inc(x_158);
lean_inc(x_8);
x_166 = l_Lean_mkAppB(x_165, x_8, x_158);
x_167 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_168 = l_Lean_Meta_trySynthInstance(x_166, x_167, x_2, x_3, x_4, x_5, x_159);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 1)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Meta_coerceToSort_x3f___closed__3;
x_173 = l_Lean_Expr_const___override(x_172, x_163);
lean_inc(x_1);
lean_inc(x_171);
x_174 = l_Lean_mkApp4(x_173, x_8, x_158, x_171, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_175 = l_Lean_Meta_expandCoe(x_174, x_2, x_3, x_4, x_5, x_170);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_176);
x_178 = lean_infer_type(x_176, x_2, x_3, x_4, x_5, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_181 = lean_whnf(x_179, x_2, x_3, x_4, x_5, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_Expr_isSort(x_182);
lean_dec(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_185 = l_Lean_indentExpr(x_1);
x_186 = l_Lean_Meta_coerceToFunction_x3f___closed__5;
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = l_Lean_Meta_coerceToSort_x3f___closed__5;
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_indentExpr(x_176);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_Meta_coerceToSort_x3f___closed__7;
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_indentExpr(x_171);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Meta_coerceSimple_x3f___closed__11;
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_197, x_2, x_3, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_171);
lean_dec(x_1);
x_203 = lean_box(0);
x_204 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_176, x_203, x_2, x_3, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_ctor_get(x_181, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_181, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_207 = x_181;
} else {
 lean_dec_ref(x_181);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_178, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_178, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_211 = x_178;
} else {
 lean_dec_ref(x_178);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_175, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_175, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_215 = x_175;
} else {
 lean_dec_ref(x_175);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_168, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_218 = x_168;
} else {
 lean_dec_ref(x_168);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_167);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_163);
lean_dec(x_158);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_168, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_168, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_222 = x_168;
} else {
 lean_dec_ref(x_168);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_10);
if (x_224 == 0)
{
return x_10;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_10, 0);
x_226 = lean_ctor_get(x_10, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_10);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_7);
if (x_228 == 0)
{
return x_7;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_7, 0);
x_230 = lean_ctor_get(x_7, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_7);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
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
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_16 = 2;
lean_ctor_set_uint8(x_7, 9, x_16);
x_17 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_10);
lean_ctor_set(x_17, 4, x_11);
lean_ctor_set(x_17, 5, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*6, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*6 + 1, x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = lean_whnf(x_1, x_17, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 5)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_21, x_2, x_3, x_4, x_5, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_22, x_2, x_3, x_4, x_5, x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_23, 1, x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
lean_ctor_set(x_23, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_22, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_18, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_18, 0, x_45);
return x_18;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_dec(x_18);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_55 = lean_ctor_get_uint8(x_7, 0);
x_56 = lean_ctor_get_uint8(x_7, 1);
x_57 = lean_ctor_get_uint8(x_7, 2);
x_58 = lean_ctor_get_uint8(x_7, 3);
x_59 = lean_ctor_get_uint8(x_7, 4);
x_60 = lean_ctor_get_uint8(x_7, 5);
x_61 = lean_ctor_get_uint8(x_7, 6);
x_62 = lean_ctor_get_uint8(x_7, 7);
x_63 = lean_ctor_get_uint8(x_7, 8);
x_64 = lean_ctor_get_uint8(x_7, 10);
x_65 = lean_ctor_get_uint8(x_7, 11);
x_66 = lean_ctor_get_uint8(x_7, 12);
lean_dec(x_7);
x_67 = 2;
x_68 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_68, 0, x_55);
lean_ctor_set_uint8(x_68, 1, x_56);
lean_ctor_set_uint8(x_68, 2, x_57);
lean_ctor_set_uint8(x_68, 3, x_58);
lean_ctor_set_uint8(x_68, 4, x_59);
lean_ctor_set_uint8(x_68, 5, x_60);
lean_ctor_set_uint8(x_68, 6, x_61);
lean_ctor_set_uint8(x_68, 7, x_62);
lean_ctor_set_uint8(x_68, 8, x_63);
lean_ctor_set_uint8(x_68, 9, x_67);
lean_ctor_set_uint8(x_68, 10, x_64);
lean_ctor_set_uint8(x_68, 11, x_65);
lean_ctor_set_uint8(x_68, 12, x_66);
x_69 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_8);
lean_ctor_set(x_69, 2, x_9);
lean_ctor_set(x_69, 3, x_10);
lean_ctor_set(x_69, 4, x_11);
lean_ctor_set(x_69, 5, x_12);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_53);
lean_ctor_set_uint8(x_69, sizeof(void*)*6 + 1, x_54);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_70 = lean_whnf(x_1, x_69, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 5)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_73, x_2, x_3, x_4, x_5, x_72);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_74, x_2, x_3, x_4, x_5, x_77);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_87 = x_70;
} else {
 lean_dec_ref(x_70);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_ctor_get(x_70, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_70, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_92 = x_70;
} else {
 lean_dec_ref(x_70);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
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
else
{
uint8_t x_38; 
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
return x_7;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
x_1 = lean_mk_string_unchecked("MonadLiftT", 10, 10);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("liftM", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Internal", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("liftCoeM", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_3 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("coeM", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_3 = l_Lean_Meta_coerceMonadLift_x3f___closed__12;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_17; lean_object* x_18; lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_35 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_36, x_3, x_4, x_5, x_6, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_42 = l_Lean_Meta_isTypeApp_x3f(x_33, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_56 = l_Lean_Meta_isTypeApp_x3f(x_40, x_3, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
lean_dec(x_56);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
lean_inc(x_68);
x_70 = l_Lean_Meta_isExprDefEq(x_68, x_54, x_3, x_4, x_5, x_6, x_66);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_free_object(x_43);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_70, 1);
x_75 = lean_ctor_get(x_70, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_5, 2);
lean_inc(x_76);
x_77 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_78 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = lean_box(0);
lean_ctor_set(x_70, 0, x_79);
return x_70;
}
else
{
lean_object* x_80; 
lean_free_object(x_70);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_68);
x_80 = lean_infer_type(x_68, x_3, x_4, x_5, x_6, x_74);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_83 = lean_whnf(x_81, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 7)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 3)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 2);
lean_inc(x_86);
lean_dec(x_84);
if (lean_obj_tag(x_86) == 3)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_90 = lean_infer_type(x_54, x_3, x_4, x_5, x_6, x_87);
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
x_93 = lean_whnf(x_91, x_3, x_4, x_5, x_6, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 7)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 3)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 2);
lean_inc(x_96);
lean_dec(x_94);
if (lean_obj_tag(x_96) == 3)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
lean_dec(x_96);
x_100 = l_Lean_Meta_decLevel(x_88, x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
x_104 = l_Lean_Meta_decLevel(x_98, x_3, x_4, x_5, x_6, x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
x_108 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_102);
x_109 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_102, x_106, x_108, x_3, x_4, x_5, x_6, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
lean_free_object(x_104);
lean_free_object(x_100);
lean_dec(x_102);
lean_dec(x_99);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_109, 0);
lean_dec(x_113);
x_114 = lean_box(0);
lean_ctor_set(x_109, 0, x_114);
return x_109;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_109, 1);
lean_inc(x_118);
lean_dec(x_109);
x_119 = l_Lean_Meta_decLevel(x_89, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = l_Lean_Meta_decLevel(x_99, x_3, x_4, x_5, x_6, x_122);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_123, 1);
x_126 = lean_box(0);
lean_ctor_set_tag(x_123, 1);
lean_ctor_set(x_123, 1, x_126);
lean_ctor_set_tag(x_119, 1);
lean_ctor_set(x_119, 1, x_123);
lean_ctor_set_tag(x_104, 1);
lean_ctor_set(x_104, 1, x_119);
lean_ctor_set(x_104, 0, x_102);
x_127 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_128 = l_Lean_Expr_const___override(x_127, x_104);
lean_inc(x_54);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_126);
lean_ctor_set(x_100, 0, x_54);
lean_inc(x_68);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 1, x_100);
x_129 = lean_array_mk(x_65);
x_130 = l_Lean_mkAppN(x_128, x_129);
lean_dec(x_129);
x_131 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_132 = l_Lean_Meta_trySynthInstance(x_130, x_131, x_3, x_4, x_5, x_6, x_125);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 1)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_136 = l_Lean_Meta_getDecLevel(x_69, x_3, x_4, x_5, x_6, x_134);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_140 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_139);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_144 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_144, 1);
lean_ctor_set_tag(x_144, 1);
lean_ctor_set(x_144, 1, x_126);
lean_ctor_set_tag(x_140, 1);
lean_ctor_set(x_140, 1, x_144);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_140);
x_147 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_136);
x_148 = l_Lean_Expr_const___override(x_147, x_136);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_126);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_135);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_135);
lean_inc(x_54);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_54);
lean_ctor_set(x_149, 1, x_31);
lean_inc(x_68);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_68);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_array_mk(x_150);
x_152 = l_Lean_mkAppN(x_148, x_151);
lean_dec(x_151);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_152);
x_153 = lean_infer_type(x_152, x_3, x_4, x_5, x_6, x_146);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_157 = l_Lean_Meta_isExprDefEq(x_33, x_155, x_3, x_4, x_5, x_6, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_152);
lean_free_object(x_57);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_161 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
lean_free_object(x_153);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = !lean_is_exclusive(x_161);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_161, 0);
lean_dec(x_164);
lean_ctor_set(x_161, 0, x_131);
return x_161;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
lean_dec(x_161);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_131);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
lean_dec(x_161);
x_168 = lean_ctor_get(x_162, 0);
lean_inc(x_168);
lean_dec(x_162);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_169 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_167);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_173 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_172);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
x_175 = lean_ctor_get(x_173, 1);
lean_ctor_set_tag(x_173, 1);
lean_ctor_set(x_173, 1, x_126);
lean_ctor_set_tag(x_169, 1);
lean_ctor_set(x_169, 1, x_173);
x_176 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_177 = l_Lean_Expr_const___override(x_176, x_169);
lean_inc(x_55);
lean_ctor_set_tag(x_153, 1);
lean_ctor_set(x_153, 1, x_126);
lean_ctor_set(x_153, 0, x_55);
x_178 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_153);
lean_inc(x_69);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_69);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_array_mk(x_180);
x_182 = l_Lean_mkAppN(x_177, x_181);
lean_dec(x_181);
x_183 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_184 = 0;
lean_inc(x_69);
x_185 = l_Lean_Expr_forallE___override(x_183, x_69, x_182, x_184);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_186 = l_Lean_Meta_trySynthInstance(x_185, x_131, x_3, x_4, x_5, x_6, x_175);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 1)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_191 = l_Lean_Expr_const___override(x_190, x_136);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_168);
lean_ctor_set(x_192, 1, x_51);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_189);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_135);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_55);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_69);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_54);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_68);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_array_mk(x_198);
x_200 = l_Lean_mkAppN(x_191, x_199);
lean_dec(x_199);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_201 = l_Lean_Meta_expandCoe(x_200, x_3, x_4, x_5, x_6, x_188);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_202);
x_204 = lean_infer_type(x_202, x_3, x_4, x_5, x_6, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_207 = l_Lean_Meta_isExprDefEq(x_33, x_205, x_3, x_4, x_5, x_6, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
uint8_t x_210; 
lean_dec(x_202);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_210 = !lean_is_exclusive(x_207);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_207, 0);
lean_dec(x_211);
lean_ctor_set(x_207, 0, x_131);
return x_207;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
lean_dec(x_207);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_131);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_214 = lean_ctor_get(x_207, 1);
lean_inc(x_214);
lean_dec(x_207);
x_215 = lean_box(0);
x_216 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_202, x_215, x_3, x_4, x_5, x_6, x_214);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
return x_216;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_216, 0);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_216);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_202);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_221 = lean_ctor_get(x_207, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_207, 1);
lean_inc(x_222);
lean_dec(x_207);
x_8 = x_221;
x_9 = x_222;
goto block_16;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_202);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_223 = lean_ctor_get(x_204, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_204, 1);
lean_inc(x_224);
lean_dec(x_204);
x_8 = x_223;
x_9 = x_224;
goto block_16;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_225 = lean_ctor_get(x_201, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_201, 1);
lean_inc(x_226);
lean_dec(x_201);
x_8 = x_225;
x_9 = x_226;
goto block_16;
}
}
else
{
uint8_t x_227; 
lean_dec(x_187);
lean_dec(x_168);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_227 = !lean_is_exclusive(x_186);
if (x_227 == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_186, 0);
lean_dec(x_228);
lean_ctor_set(x_186, 0, x_131);
return x_186;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_186, 1);
lean_inc(x_229);
lean_dec(x_186);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_131);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_168);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_231 = lean_ctor_get(x_186, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_186, 1);
lean_inc(x_232);
lean_dec(x_186);
x_8 = x_231;
x_9 = x_232;
goto block_16;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; 
x_233 = lean_ctor_get(x_173, 0);
x_234 = lean_ctor_get(x_173, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_173);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_126);
lean_ctor_set_tag(x_169, 1);
lean_ctor_set(x_169, 1, x_235);
x_236 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_237 = l_Lean_Expr_const___override(x_236, x_169);
lean_inc(x_55);
lean_ctor_set_tag(x_153, 1);
lean_ctor_set(x_153, 1, x_126);
lean_ctor_set(x_153, 0, x_55);
x_238 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_153);
lean_inc(x_69);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_69);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_array_mk(x_240);
x_242 = l_Lean_mkAppN(x_237, x_241);
lean_dec(x_241);
x_243 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_244 = 0;
lean_inc(x_69);
x_245 = l_Lean_Expr_forallE___override(x_243, x_69, x_242, x_244);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_246 = l_Lean_Meta_trySynthInstance(x_245, x_131, x_3, x_4, x_5, x_6, x_234);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
if (lean_obj_tag(x_247) == 1)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_ctor_get(x_247, 0);
lean_inc(x_249);
lean_dec(x_247);
x_250 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_251 = l_Lean_Expr_const___override(x_250, x_136);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_168);
lean_ctor_set(x_252, 1, x_51);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_135);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_55);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_69);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_54);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_68);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_array_mk(x_258);
x_260 = l_Lean_mkAppN(x_251, x_259);
lean_dec(x_259);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_261 = l_Lean_Meta_expandCoe(x_260, x_3, x_4, x_5, x_6, x_248);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_262);
x_264 = lean_infer_type(x_262, x_3, x_4, x_5, x_6, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_267 = l_Lean_Meta_isExprDefEq(x_33, x_265, x_3, x_4, x_5, x_6, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; uint8_t x_269; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_unbox(x_268);
lean_dec(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_262);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_271 = x_267;
} else {
 lean_dec_ref(x_267);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_131);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_273 = lean_ctor_get(x_267, 1);
lean_inc(x_273);
lean_dec(x_267);
x_274 = lean_box(0);
x_275 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_262, x_274, x_3, x_4, x_5, x_6, x_273);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_262);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_280 = lean_ctor_get(x_267, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_267, 1);
lean_inc(x_281);
lean_dec(x_267);
x_8 = x_280;
x_9 = x_281;
goto block_16;
}
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_262);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_282 = lean_ctor_get(x_264, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_264, 1);
lean_inc(x_283);
lean_dec(x_264);
x_8 = x_282;
x_9 = x_283;
goto block_16;
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_284 = lean_ctor_get(x_261, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_261, 1);
lean_inc(x_285);
lean_dec(x_261);
x_8 = x_284;
x_9 = x_285;
goto block_16;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_247);
lean_dec(x_168);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_286 = lean_ctor_get(x_246, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_287 = x_246;
} else {
 lean_dec_ref(x_246);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_131);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_168);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_289 = lean_ctor_get(x_246, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_246, 1);
lean_inc(x_290);
lean_dec(x_246);
x_8 = x_289;
x_9 = x_290;
goto block_16;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_free_object(x_169);
lean_dec(x_171);
lean_dec(x_168);
lean_free_object(x_153);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_291 = lean_ctor_get(x_173, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_173, 1);
lean_inc(x_292);
lean_dec(x_173);
x_8 = x_291;
x_9 = x_292;
goto block_16;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_169, 0);
x_294 = lean_ctor_get(x_169, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_169);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_295 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_298 = x_295;
} else {
 lean_dec_ref(x_295);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
 lean_ctor_set_tag(x_299, 1);
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_126);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_293);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_302 = l_Lean_Expr_const___override(x_301, x_300);
lean_inc(x_55);
lean_ctor_set_tag(x_153, 1);
lean_ctor_set(x_153, 1, x_126);
lean_ctor_set(x_153, 0, x_55);
x_303 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_153);
lean_inc(x_69);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_69);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_array_mk(x_305);
x_307 = l_Lean_mkAppN(x_302, x_306);
lean_dec(x_306);
x_308 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_309 = 0;
lean_inc(x_69);
x_310 = l_Lean_Expr_forallE___override(x_308, x_69, x_307, x_309);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_311 = l_Lean_Meta_trySynthInstance(x_310, x_131, x_3, x_4, x_5, x_6, x_297);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
if (lean_obj_tag(x_312) == 1)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
lean_dec(x_312);
x_315 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_316 = l_Lean_Expr_const___override(x_315, x_136);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_168);
lean_ctor_set(x_317, 1, x_51);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_314);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_135);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_55);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_69);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_54);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_68);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_array_mk(x_323);
x_325 = l_Lean_mkAppN(x_316, x_324);
lean_dec(x_324);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_326 = l_Lean_Meta_expandCoe(x_325, x_3, x_4, x_5, x_6, x_313);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_327);
x_329 = lean_infer_type(x_327, x_3, x_4, x_5, x_6, x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_332 = l_Lean_Meta_isExprDefEq(x_33, x_330, x_3, x_4, x_5, x_6, x_331);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; uint8_t x_334; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_unbox(x_333);
lean_dec(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_327);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_336 = x_332;
} else {
 lean_dec_ref(x_332);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_131);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_338 = lean_ctor_get(x_332, 1);
lean_inc(x_338);
lean_dec(x_332);
x_339 = lean_box(0);
x_340 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_327, x_339, x_3, x_4, x_5, x_6, x_338);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_327);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_345 = lean_ctor_get(x_332, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_332, 1);
lean_inc(x_346);
lean_dec(x_332);
x_8 = x_345;
x_9 = x_346;
goto block_16;
}
}
else
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_327);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_347 = lean_ctor_get(x_329, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_329, 1);
lean_inc(x_348);
lean_dec(x_329);
x_8 = x_347;
x_9 = x_348;
goto block_16;
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_349 = lean_ctor_get(x_326, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_326, 1);
lean_inc(x_350);
lean_dec(x_326);
x_8 = x_349;
x_9 = x_350;
goto block_16;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_312);
lean_dec(x_168);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_351 = lean_ctor_get(x_311, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_352 = x_311;
} else {
 lean_dec_ref(x_311);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_131);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_168);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_354 = lean_ctor_get(x_311, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_311, 1);
lean_inc(x_355);
lean_dec(x_311);
x_8 = x_354;
x_9 = x_355;
goto block_16;
}
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_293);
lean_dec(x_168);
lean_free_object(x_153);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_356 = lean_ctor_get(x_295, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_295, 1);
lean_inc(x_357);
lean_dec(x_295);
x_8 = x_356;
x_9 = x_357;
goto block_16;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_168);
lean_free_object(x_153);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_358 = lean_ctor_get(x_169, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_169, 1);
lean_inc(x_359);
lean_dec(x_169);
x_8 = x_358;
x_9 = x_359;
goto block_16;
}
}
}
else
{
lean_object* x_360; lean_object* x_361; 
lean_free_object(x_153);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_360 = lean_ctor_get(x_161, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_161, 1);
lean_inc(x_361);
lean_dec(x_161);
x_8 = x_360;
x_9 = x_361;
goto block_16;
}
}
else
{
uint8_t x_362; 
lean_free_object(x_153);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_362 = !lean_is_exclusive(x_157);
if (x_362 == 0)
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_157, 0);
lean_dec(x_363);
lean_ctor_set(x_57, 0, x_152);
lean_ctor_set(x_157, 0, x_57);
return x_157;
}
else
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_157, 1);
lean_inc(x_364);
lean_dec(x_157);
lean_ctor_set(x_57, 0, x_152);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_57);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_free_object(x_153);
lean_dec(x_152);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_366 = lean_ctor_get(x_157, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_157, 1);
lean_inc(x_367);
lean_dec(x_157);
x_8 = x_366;
x_9 = x_367;
goto block_16;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_153, 0);
x_369 = lean_ctor_get(x_153, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_153);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_370 = l_Lean_Meta_isExprDefEq(x_33, x_368, x_3, x_4, x_5, x_6, x_369);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; uint8_t x_372; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_unbox(x_371);
lean_dec(x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_152);
lean_free_object(x_57);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
lean_dec(x_370);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_374 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_373);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_377 = x_374;
} else {
 lean_dec_ref(x_374);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_131);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_374, 1);
lean_inc(x_379);
lean_dec(x_374);
x_380 = lean_ctor_get(x_375, 0);
lean_inc(x_380);
lean_dec(x_375);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_381 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_379);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_384 = x_381;
} else {
 lean_dec_ref(x_381);
 x_384 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_385 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_383);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_388 = x_385;
} else {
 lean_dec_ref(x_385);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
 lean_ctor_set_tag(x_389, 1);
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_126);
if (lean_is_scalar(x_384)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_384;
 lean_ctor_set_tag(x_390, 1);
}
lean_ctor_set(x_390, 0, x_382);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_392 = l_Lean_Expr_const___override(x_391, x_390);
lean_inc(x_55);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_55);
lean_ctor_set(x_393, 1, x_126);
x_394 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_393);
lean_inc(x_69);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_69);
lean_ctor_set(x_396, 1, x_395);
x_397 = lean_array_mk(x_396);
x_398 = l_Lean_mkAppN(x_392, x_397);
lean_dec(x_397);
x_399 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_400 = 0;
lean_inc(x_69);
x_401 = l_Lean_Expr_forallE___override(x_399, x_69, x_398, x_400);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_402 = l_Lean_Meta_trySynthInstance(x_401, x_131, x_3, x_4, x_5, x_6, x_387);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
if (lean_obj_tag(x_403) == 1)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_ctor_get(x_403, 0);
lean_inc(x_405);
lean_dec(x_403);
x_406 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_407 = l_Lean_Expr_const___override(x_406, x_136);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_380);
lean_ctor_set(x_408, 1, x_51);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_405);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_135);
lean_ctor_set(x_410, 1, x_409);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_55);
lean_ctor_set(x_411, 1, x_410);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_69);
lean_ctor_set(x_412, 1, x_411);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_54);
lean_ctor_set(x_413, 1, x_412);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_68);
lean_ctor_set(x_414, 1, x_413);
x_415 = lean_array_mk(x_414);
x_416 = l_Lean_mkAppN(x_407, x_415);
lean_dec(x_415);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_417 = l_Lean_Meta_expandCoe(x_416, x_3, x_4, x_5, x_6, x_404);
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
lean_inc(x_418);
x_420 = lean_infer_type(x_418, x_3, x_4, x_5, x_6, x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_423 = l_Lean_Meta_isExprDefEq(x_33, x_421, x_3, x_4, x_5, x_6, x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; uint8_t x_425; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_unbox(x_424);
lean_dec(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_418);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_427 = x_423;
} else {
 lean_dec_ref(x_423);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_131);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_429 = lean_ctor_get(x_423, 1);
lean_inc(x_429);
lean_dec(x_423);
x_430 = lean_box(0);
x_431 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_418, x_430, x_3, x_4, x_5, x_6, x_429);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_434 = x_431;
} else {
 lean_dec_ref(x_431);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_418);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_436 = lean_ctor_get(x_423, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 1);
lean_inc(x_437);
lean_dec(x_423);
x_8 = x_436;
x_9 = x_437;
goto block_16;
}
}
else
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_418);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_438 = lean_ctor_get(x_420, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_420, 1);
lean_inc(x_439);
lean_dec(x_420);
x_8 = x_438;
x_9 = x_439;
goto block_16;
}
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_440 = lean_ctor_get(x_417, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_417, 1);
lean_inc(x_441);
lean_dec(x_417);
x_8 = x_440;
x_9 = x_441;
goto block_16;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_403);
lean_dec(x_380);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_442 = lean_ctor_get(x_402, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_443 = x_402;
} else {
 lean_dec_ref(x_402);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_131);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_380);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_445 = lean_ctor_get(x_402, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_402, 1);
lean_inc(x_446);
lean_dec(x_402);
x_8 = x_445;
x_9 = x_446;
goto block_16;
}
}
else
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_380);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_447 = lean_ctor_get(x_385, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_385, 1);
lean_inc(x_448);
lean_dec(x_385);
x_8 = x_447;
x_9 = x_448;
goto block_16;
}
}
else
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_380);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_449 = lean_ctor_get(x_381, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_381, 1);
lean_inc(x_450);
lean_dec(x_381);
x_8 = x_449;
x_9 = x_450;
goto block_16;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_451 = lean_ctor_get(x_374, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_374, 1);
lean_inc(x_452);
lean_dec(x_374);
x_8 = x_451;
x_9 = x_452;
goto block_16;
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_453 = lean_ctor_get(x_370, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_454 = x_370;
} else {
 lean_dec_ref(x_370);
 x_454 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_152);
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_57);
lean_ctor_set(x_455, 1, x_453);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; 
lean_dec(x_152);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_456 = lean_ctor_get(x_370, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_370, 1);
lean_inc(x_457);
lean_dec(x_370);
x_8 = x_456;
x_9 = x_457;
goto block_16;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_152);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_458 = lean_ctor_get(x_153, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_153, 1);
lean_inc(x_459);
lean_dec(x_153);
x_8 = x_458;
x_9 = x_459;
goto block_16;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_460 = lean_ctor_get(x_144, 0);
x_461 = lean_ctor_get(x_144, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_144);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_126);
lean_ctor_set_tag(x_140, 1);
lean_ctor_set(x_140, 1, x_462);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_140);
x_463 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_136);
x_464 = l_Lean_Expr_const___override(x_463, x_136);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_126);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_135);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_135);
lean_inc(x_54);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_54);
lean_ctor_set(x_465, 1, x_31);
lean_inc(x_68);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_68);
lean_ctor_set(x_466, 1, x_465);
x_467 = lean_array_mk(x_466);
x_468 = l_Lean_mkAppN(x_464, x_467);
lean_dec(x_467);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_468);
x_469 = lean_infer_type(x_468, x_3, x_4, x_5, x_6, x_461);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_473 = l_Lean_Meta_isExprDefEq(x_33, x_470, x_3, x_4, x_5, x_6, x_471);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; uint8_t x_475; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_unbox(x_474);
lean_dec(x_474);
if (x_475 == 0)
{
lean_object* x_476; lean_object* x_477; 
lean_dec(x_468);
lean_free_object(x_57);
x_476 = lean_ctor_get(x_473, 1);
lean_inc(x_476);
lean_dec(x_473);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_477 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_476);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_472);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_480 = x_477;
} else {
 lean_dec_ref(x_477);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_131);
lean_ctor_set(x_481, 1, x_479);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_477, 1);
lean_inc(x_482);
lean_dec(x_477);
x_483 = lean_ctor_get(x_478, 0);
lean_inc(x_483);
lean_dec(x_478);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_484 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_482);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_487 = x_484;
} else {
 lean_dec_ref(x_484);
 x_487 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_488 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_486);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; lean_object* x_505; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_491 = x_488;
} else {
 lean_dec_ref(x_488);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
 lean_ctor_set_tag(x_492, 1);
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_126);
if (lean_is_scalar(x_487)) {
 x_493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_493 = x_487;
 lean_ctor_set_tag(x_493, 1);
}
lean_ctor_set(x_493, 0, x_485);
lean_ctor_set(x_493, 1, x_492);
x_494 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_495 = l_Lean_Expr_const___override(x_494, x_493);
lean_inc(x_55);
if (lean_is_scalar(x_472)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_472;
 lean_ctor_set_tag(x_496, 1);
}
lean_ctor_set(x_496, 0, x_55);
lean_ctor_set(x_496, 1, x_126);
x_497 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_496);
lean_inc(x_69);
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_69);
lean_ctor_set(x_499, 1, x_498);
x_500 = lean_array_mk(x_499);
x_501 = l_Lean_mkAppN(x_495, x_500);
lean_dec(x_500);
x_502 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_503 = 0;
lean_inc(x_69);
x_504 = l_Lean_Expr_forallE___override(x_502, x_69, x_501, x_503);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_505 = l_Lean_Meta_trySynthInstance(x_504, x_131, x_3, x_4, x_5, x_6, x_490);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
if (lean_obj_tag(x_506) == 1)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
lean_dec(x_506);
x_509 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_510 = l_Lean_Expr_const___override(x_509, x_136);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_483);
lean_ctor_set(x_511, 1, x_51);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_508);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_135);
lean_ctor_set(x_513, 1, x_512);
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_55);
lean_ctor_set(x_514, 1, x_513);
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_69);
lean_ctor_set(x_515, 1, x_514);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_54);
lean_ctor_set(x_516, 1, x_515);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_68);
lean_ctor_set(x_517, 1, x_516);
x_518 = lean_array_mk(x_517);
x_519 = l_Lean_mkAppN(x_510, x_518);
lean_dec(x_518);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_520 = l_Lean_Meta_expandCoe(x_519, x_3, x_4, x_5, x_6, x_507);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
lean_dec(x_520);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_521);
x_523 = lean_infer_type(x_521, x_3, x_4, x_5, x_6, x_522);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_526 = l_Lean_Meta_isExprDefEq(x_33, x_524, x_3, x_4, x_5, x_6, x_525);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; uint8_t x_528; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_unbox(x_527);
lean_dec(x_527);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_521);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_529 = lean_ctor_get(x_526, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_530 = x_526;
} else {
 lean_dec_ref(x_526);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_131);
lean_ctor_set(x_531, 1, x_529);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_532 = lean_ctor_get(x_526, 1);
lean_inc(x_532);
lean_dec(x_526);
x_533 = lean_box(0);
x_534 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_521, x_533, x_3, x_4, x_5, x_6, x_532);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_537 = x_534;
} else {
 lean_dec_ref(x_534);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_535);
lean_ctor_set(x_538, 1, x_536);
return x_538;
}
}
else
{
lean_object* x_539; lean_object* x_540; 
lean_dec(x_521);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_539 = lean_ctor_get(x_526, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_526, 1);
lean_inc(x_540);
lean_dec(x_526);
x_8 = x_539;
x_9 = x_540;
goto block_16;
}
}
else
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_521);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_541 = lean_ctor_get(x_523, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_523, 1);
lean_inc(x_542);
lean_dec(x_523);
x_8 = x_541;
x_9 = x_542;
goto block_16;
}
}
else
{
lean_object* x_543; lean_object* x_544; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_543 = lean_ctor_get(x_520, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_520, 1);
lean_inc(x_544);
lean_dec(x_520);
x_8 = x_543;
x_9 = x_544;
goto block_16;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_506);
lean_dec(x_483);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_545 = lean_ctor_get(x_505, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_546 = x_505;
} else {
 lean_dec_ref(x_505);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_131);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
else
{
lean_object* x_548; lean_object* x_549; 
lean_dec(x_483);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_548 = lean_ctor_get(x_505, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_505, 1);
lean_inc(x_549);
lean_dec(x_505);
x_8 = x_548;
x_9 = x_549;
goto block_16;
}
}
else
{
lean_object* x_550; lean_object* x_551; 
lean_dec(x_487);
lean_dec(x_485);
lean_dec(x_483);
lean_dec(x_472);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_550 = lean_ctor_get(x_488, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_488, 1);
lean_inc(x_551);
lean_dec(x_488);
x_8 = x_550;
x_9 = x_551;
goto block_16;
}
}
else
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_483);
lean_dec(x_472);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_552 = lean_ctor_get(x_484, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_484, 1);
lean_inc(x_553);
lean_dec(x_484);
x_8 = x_552;
x_9 = x_553;
goto block_16;
}
}
}
else
{
lean_object* x_554; lean_object* x_555; 
lean_dec(x_472);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_554 = lean_ctor_get(x_477, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_477, 1);
lean_inc(x_555);
lean_dec(x_477);
x_8 = x_554;
x_9 = x_555;
goto block_16;
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_472);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_556 = lean_ctor_get(x_473, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_557 = x_473;
} else {
 lean_dec_ref(x_473);
 x_557 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_468);
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_57);
lean_ctor_set(x_558, 1, x_556);
return x_558;
}
}
else
{
lean_object* x_559; lean_object* x_560; 
lean_dec(x_472);
lean_dec(x_468);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_559 = lean_ctor_get(x_473, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_473, 1);
lean_inc(x_560);
lean_dec(x_473);
x_8 = x_559;
x_9 = x_560;
goto block_16;
}
}
else
{
lean_object* x_561; lean_object* x_562; 
lean_dec(x_468);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_561 = lean_ctor_get(x_469, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_469, 1);
lean_inc(x_562);
lean_dec(x_469);
x_8 = x_561;
x_9 = x_562;
goto block_16;
}
}
}
else
{
lean_object* x_563; lean_object* x_564; 
lean_free_object(x_140);
lean_dec(x_142);
lean_free_object(x_136);
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_563 = lean_ctor_get(x_144, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_144, 1);
lean_inc(x_564);
lean_dec(x_144);
x_8 = x_563;
x_9 = x_564;
goto block_16;
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_140, 0);
x_566 = lean_ctor_get(x_140, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_140);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_567 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_566);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_570 = x_567;
} else {
 lean_dec_ref(x_567);
 x_570 = lean_box(0);
}
if (lean_is_scalar(x_570)) {
 x_571 = lean_alloc_ctor(1, 2, 0);
} else {
 x_571 = x_570;
 lean_ctor_set_tag(x_571, 1);
}
lean_ctor_set(x_571, 0, x_568);
lean_ctor_set(x_571, 1, x_126);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_565);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_572);
x_573 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_136);
x_574 = l_Lean_Expr_const___override(x_573, x_136);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_126);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_135);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_135);
lean_inc(x_54);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_54);
lean_ctor_set(x_575, 1, x_31);
lean_inc(x_68);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_68);
lean_ctor_set(x_576, 1, x_575);
x_577 = lean_array_mk(x_576);
x_578 = l_Lean_mkAppN(x_574, x_577);
lean_dec(x_577);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_578);
x_579 = lean_infer_type(x_578, x_3, x_4, x_5, x_6, x_569);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_582 = x_579;
} else {
 lean_dec_ref(x_579);
 x_582 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_583 = l_Lean_Meta_isExprDefEq(x_33, x_580, x_3, x_4, x_5, x_6, x_581);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; uint8_t x_585; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_unbox(x_584);
lean_dec(x_584);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; 
lean_dec(x_578);
lean_free_object(x_57);
x_586 = lean_ctor_get(x_583, 1);
lean_inc(x_586);
lean_dec(x_583);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_587 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_586);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_582);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_590 = x_587;
} else {
 lean_dec_ref(x_587);
 x_590 = lean_box(0);
}
if (lean_is_scalar(x_590)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_590;
}
lean_ctor_set(x_591, 0, x_131);
lean_ctor_set(x_591, 1, x_589);
return x_591;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_587, 1);
lean_inc(x_592);
lean_dec(x_587);
x_593 = lean_ctor_get(x_588, 0);
lean_inc(x_593);
lean_dec(x_588);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_594 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_592);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_597 = x_594;
} else {
 lean_dec_ref(x_594);
 x_597 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_598 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_596);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; lean_object* x_614; lean_object* x_615; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_601 = x_598;
} else {
 lean_dec_ref(x_598);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_602 = x_601;
 lean_ctor_set_tag(x_602, 1);
}
lean_ctor_set(x_602, 0, x_599);
lean_ctor_set(x_602, 1, x_126);
if (lean_is_scalar(x_597)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_597;
 lean_ctor_set_tag(x_603, 1);
}
lean_ctor_set(x_603, 0, x_595);
lean_ctor_set(x_603, 1, x_602);
x_604 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_605 = l_Lean_Expr_const___override(x_604, x_603);
lean_inc(x_55);
if (lean_is_scalar(x_582)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_582;
 lean_ctor_set_tag(x_606, 1);
}
lean_ctor_set(x_606, 0, x_55);
lean_ctor_set(x_606, 1, x_126);
x_607 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_606);
lean_inc(x_69);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_69);
lean_ctor_set(x_609, 1, x_608);
x_610 = lean_array_mk(x_609);
x_611 = l_Lean_mkAppN(x_605, x_610);
lean_dec(x_610);
x_612 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_613 = 0;
lean_inc(x_69);
x_614 = l_Lean_Expr_forallE___override(x_612, x_69, x_611, x_613);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_615 = l_Lean_Meta_trySynthInstance(x_614, x_131, x_3, x_4, x_5, x_6, x_600);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
if (lean_obj_tag(x_616) == 1)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
x_618 = lean_ctor_get(x_616, 0);
lean_inc(x_618);
lean_dec(x_616);
x_619 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_620 = l_Lean_Expr_const___override(x_619, x_136);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_593);
lean_ctor_set(x_621, 1, x_51);
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_618);
lean_ctor_set(x_622, 1, x_621);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_135);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_55);
lean_ctor_set(x_624, 1, x_623);
x_625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_625, 0, x_69);
lean_ctor_set(x_625, 1, x_624);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_54);
lean_ctor_set(x_626, 1, x_625);
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_68);
lean_ctor_set(x_627, 1, x_626);
x_628 = lean_array_mk(x_627);
x_629 = l_Lean_mkAppN(x_620, x_628);
lean_dec(x_628);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_630 = l_Lean_Meta_expandCoe(x_629, x_3, x_4, x_5, x_6, x_617);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 1);
lean_inc(x_632);
lean_dec(x_630);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_631);
x_633 = lean_infer_type(x_631, x_3, x_4, x_5, x_6, x_632);
if (lean_obj_tag(x_633) == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_633, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_633, 1);
lean_inc(x_635);
lean_dec(x_633);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_636 = l_Lean_Meta_isExprDefEq(x_33, x_634, x_3, x_4, x_5, x_6, x_635);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; uint8_t x_638; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_unbox(x_637);
lean_dec(x_637);
if (x_638 == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_631);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_640 = x_636;
} else {
 lean_dec_ref(x_636);
 x_640 = lean_box(0);
}
if (lean_is_scalar(x_640)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_640;
}
lean_ctor_set(x_641, 0, x_131);
lean_ctor_set(x_641, 1, x_639);
return x_641;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_642 = lean_ctor_get(x_636, 1);
lean_inc(x_642);
lean_dec(x_636);
x_643 = lean_box(0);
x_644 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_631, x_643, x_3, x_4, x_5, x_6, x_642);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_647 = x_644;
} else {
 lean_dec_ref(x_644);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_645);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; 
lean_dec(x_631);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_649 = lean_ctor_get(x_636, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_636, 1);
lean_inc(x_650);
lean_dec(x_636);
x_8 = x_649;
x_9 = x_650;
goto block_16;
}
}
else
{
lean_object* x_651; lean_object* x_652; 
lean_dec(x_631);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_651 = lean_ctor_get(x_633, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_633, 1);
lean_inc(x_652);
lean_dec(x_633);
x_8 = x_651;
x_9 = x_652;
goto block_16;
}
}
else
{
lean_object* x_653; lean_object* x_654; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_653 = lean_ctor_get(x_630, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_630, 1);
lean_inc(x_654);
lean_dec(x_630);
x_8 = x_653;
x_9 = x_654;
goto block_16;
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_616);
lean_dec(x_593);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_655 = lean_ctor_get(x_615, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_656 = x_615;
} else {
 lean_dec_ref(x_615);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_131);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
}
else
{
lean_object* x_658; lean_object* x_659; 
lean_dec(x_593);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_658 = lean_ctor_get(x_615, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_615, 1);
lean_inc(x_659);
lean_dec(x_615);
x_8 = x_658;
x_9 = x_659;
goto block_16;
}
}
else
{
lean_object* x_660; lean_object* x_661; 
lean_dec(x_597);
lean_dec(x_595);
lean_dec(x_593);
lean_dec(x_582);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_660 = lean_ctor_get(x_598, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_598, 1);
lean_inc(x_661);
lean_dec(x_598);
x_8 = x_660;
x_9 = x_661;
goto block_16;
}
}
else
{
lean_object* x_662; lean_object* x_663; 
lean_dec(x_593);
lean_dec(x_582);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_662 = lean_ctor_get(x_594, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_594, 1);
lean_inc(x_663);
lean_dec(x_594);
x_8 = x_662;
x_9 = x_663;
goto block_16;
}
}
}
else
{
lean_object* x_664; lean_object* x_665; 
lean_dec(x_582);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_664 = lean_ctor_get(x_587, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_587, 1);
lean_inc(x_665);
lean_dec(x_587);
x_8 = x_664;
x_9 = x_665;
goto block_16;
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_582);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_666 = lean_ctor_get(x_583, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_667 = x_583;
} else {
 lean_dec_ref(x_583);
 x_667 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_578);
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_57);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
}
else
{
lean_object* x_669; lean_object* x_670; 
lean_dec(x_582);
lean_dec(x_578);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_669 = lean_ctor_get(x_583, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_583, 1);
lean_inc(x_670);
lean_dec(x_583);
x_8 = x_669;
x_9 = x_670;
goto block_16;
}
}
else
{
lean_object* x_671; lean_object* x_672; 
lean_dec(x_578);
lean_dec(x_51);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_671 = lean_ctor_get(x_579, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_579, 1);
lean_inc(x_672);
lean_dec(x_579);
x_8 = x_671;
x_9 = x_672;
goto block_16;
}
}
else
{
lean_object* x_673; lean_object* x_674; 
lean_dec(x_565);
lean_free_object(x_136);
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_673 = lean_ctor_get(x_567, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_567, 1);
lean_inc(x_674);
lean_dec(x_567);
x_8 = x_673;
x_9 = x_674;
goto block_16;
}
}
}
else
{
lean_object* x_675; lean_object* x_676; 
lean_free_object(x_136);
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_675 = lean_ctor_get(x_140, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_140, 1);
lean_inc(x_676);
lean_dec(x_140);
x_8 = x_675;
x_9 = x_676;
goto block_16;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_136, 0);
x_678 = lean_ctor_get(x_136, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_136);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_679 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_678);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_682 = x_679;
} else {
 lean_dec_ref(x_679);
 x_682 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_683 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_681);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_686 = x_683;
} else {
 lean_dec_ref(x_683);
 x_686 = lean_box(0);
}
if (lean_is_scalar(x_686)) {
 x_687 = lean_alloc_ctor(1, 2, 0);
} else {
 x_687 = x_686;
 lean_ctor_set_tag(x_687, 1);
}
lean_ctor_set(x_687, 0, x_684);
lean_ctor_set(x_687, 1, x_126);
if (lean_is_scalar(x_682)) {
 x_688 = lean_alloc_ctor(1, 2, 0);
} else {
 x_688 = x_682;
 lean_ctor_set_tag(x_688, 1);
}
lean_ctor_set(x_688, 0, x_680);
lean_ctor_set(x_688, 1, x_687);
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_677);
lean_ctor_set(x_689, 1, x_688);
x_690 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_689);
x_691 = l_Lean_Expr_const___override(x_690, x_689);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_126);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_135);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_135);
lean_inc(x_54);
x_692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_692, 0, x_54);
lean_ctor_set(x_692, 1, x_31);
lean_inc(x_68);
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_68);
lean_ctor_set(x_693, 1, x_692);
x_694 = lean_array_mk(x_693);
x_695 = l_Lean_mkAppN(x_691, x_694);
lean_dec(x_694);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_695);
x_696 = lean_infer_type(x_695, x_3, x_4, x_5, x_6, x_685);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_696)) {
 lean_ctor_release(x_696, 0);
 lean_ctor_release(x_696, 1);
 x_699 = x_696;
} else {
 lean_dec_ref(x_696);
 x_699 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_700 = l_Lean_Meta_isExprDefEq(x_33, x_697, x_3, x_4, x_5, x_6, x_698);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; uint8_t x_702; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_unbox(x_701);
lean_dec(x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; 
lean_dec(x_695);
lean_free_object(x_57);
x_703 = lean_ctor_get(x_700, 1);
lean_inc(x_703);
lean_dec(x_700);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_704 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_703);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; 
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_699);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_706 = lean_ctor_get(x_704, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 x_707 = x_704;
} else {
 lean_dec_ref(x_704);
 x_707 = lean_box(0);
}
if (lean_is_scalar(x_707)) {
 x_708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_708 = x_707;
}
lean_ctor_set(x_708, 0, x_131);
lean_ctor_set(x_708, 1, x_706);
return x_708;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_704, 1);
lean_inc(x_709);
lean_dec(x_704);
x_710 = lean_ctor_get(x_705, 0);
lean_inc(x_710);
lean_dec(x_705);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_711 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_709);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_714 = x_711;
} else {
 lean_dec_ref(x_711);
 x_714 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_715 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_713);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; lean_object* x_731; lean_object* x_732; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_718 = x_715;
} else {
 lean_dec_ref(x_715);
 x_718 = lean_box(0);
}
if (lean_is_scalar(x_718)) {
 x_719 = lean_alloc_ctor(1, 2, 0);
} else {
 x_719 = x_718;
 lean_ctor_set_tag(x_719, 1);
}
lean_ctor_set(x_719, 0, x_716);
lean_ctor_set(x_719, 1, x_126);
if (lean_is_scalar(x_714)) {
 x_720 = lean_alloc_ctor(1, 2, 0);
} else {
 x_720 = x_714;
 lean_ctor_set_tag(x_720, 1);
}
lean_ctor_set(x_720, 0, x_712);
lean_ctor_set(x_720, 1, x_719);
x_721 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_722 = l_Lean_Expr_const___override(x_721, x_720);
lean_inc(x_55);
if (lean_is_scalar(x_699)) {
 x_723 = lean_alloc_ctor(1, 2, 0);
} else {
 x_723 = x_699;
 lean_ctor_set_tag(x_723, 1);
}
lean_ctor_set(x_723, 0, x_55);
lean_ctor_set(x_723, 1, x_126);
x_724 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_723);
lean_inc(x_69);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_69);
lean_ctor_set(x_726, 1, x_725);
x_727 = lean_array_mk(x_726);
x_728 = l_Lean_mkAppN(x_722, x_727);
lean_dec(x_727);
x_729 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_730 = 0;
lean_inc(x_69);
x_731 = l_Lean_Expr_forallE___override(x_729, x_69, x_728, x_730);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_732 = l_Lean_Meta_trySynthInstance(x_731, x_131, x_3, x_4, x_5, x_6, x_717);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
if (lean_obj_tag(x_733) == 1)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_735 = lean_ctor_get(x_733, 0);
lean_inc(x_735);
lean_dec(x_733);
x_736 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_737 = l_Lean_Expr_const___override(x_736, x_689);
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_710);
lean_ctor_set(x_738, 1, x_51);
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_735);
lean_ctor_set(x_739, 1, x_738);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_135);
lean_ctor_set(x_740, 1, x_739);
x_741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_741, 0, x_55);
lean_ctor_set(x_741, 1, x_740);
x_742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_742, 0, x_69);
lean_ctor_set(x_742, 1, x_741);
x_743 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_743, 0, x_54);
lean_ctor_set(x_743, 1, x_742);
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_68);
lean_ctor_set(x_744, 1, x_743);
x_745 = lean_array_mk(x_744);
x_746 = l_Lean_mkAppN(x_737, x_745);
lean_dec(x_745);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_747 = l_Lean_Meta_expandCoe(x_746, x_3, x_4, x_5, x_6, x_734);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
lean_dec(x_747);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_748);
x_750 = lean_infer_type(x_748, x_3, x_4, x_5, x_6, x_749);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_753 = l_Lean_Meta_isExprDefEq(x_33, x_751, x_3, x_4, x_5, x_6, x_752);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; uint8_t x_755; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_unbox(x_754);
lean_dec(x_754);
if (x_755 == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_748);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_756 = lean_ctor_get(x_753, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_757 = x_753;
} else {
 lean_dec_ref(x_753);
 x_757 = lean_box(0);
}
if (lean_is_scalar(x_757)) {
 x_758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_758 = x_757;
}
lean_ctor_set(x_758, 0, x_131);
lean_ctor_set(x_758, 1, x_756);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_759 = lean_ctor_get(x_753, 1);
lean_inc(x_759);
lean_dec(x_753);
x_760 = lean_box(0);
x_761 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_748, x_760, x_3, x_4, x_5, x_6, x_759);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_764 = x_761;
} else {
 lean_dec_ref(x_761);
 x_764 = lean_box(0);
}
if (lean_is_scalar(x_764)) {
 x_765 = lean_alloc_ctor(0, 2, 0);
} else {
 x_765 = x_764;
}
lean_ctor_set(x_765, 0, x_762);
lean_ctor_set(x_765, 1, x_763);
return x_765;
}
}
else
{
lean_object* x_766; lean_object* x_767; 
lean_dec(x_748);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_766 = lean_ctor_get(x_753, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_753, 1);
lean_inc(x_767);
lean_dec(x_753);
x_8 = x_766;
x_9 = x_767;
goto block_16;
}
}
else
{
lean_object* x_768; lean_object* x_769; 
lean_dec(x_748);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_768 = lean_ctor_get(x_750, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_750, 1);
lean_inc(x_769);
lean_dec(x_750);
x_8 = x_768;
x_9 = x_769;
goto block_16;
}
}
else
{
lean_object* x_770; lean_object* x_771; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_770 = lean_ctor_get(x_747, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_747, 1);
lean_inc(x_771);
lean_dec(x_747);
x_8 = x_770;
x_9 = x_771;
goto block_16;
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_733);
lean_dec(x_710);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_772 = lean_ctor_get(x_732, 1);
lean_inc(x_772);
if (lean_is_exclusive(x_732)) {
 lean_ctor_release(x_732, 0);
 lean_ctor_release(x_732, 1);
 x_773 = x_732;
} else {
 lean_dec_ref(x_732);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_774 = x_773;
}
lean_ctor_set(x_774, 0, x_131);
lean_ctor_set(x_774, 1, x_772);
return x_774;
}
}
else
{
lean_object* x_775; lean_object* x_776; 
lean_dec(x_710);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_775 = lean_ctor_get(x_732, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_732, 1);
lean_inc(x_776);
lean_dec(x_732);
x_8 = x_775;
x_9 = x_776;
goto block_16;
}
}
else
{
lean_object* x_777; lean_object* x_778; 
lean_dec(x_714);
lean_dec(x_712);
lean_dec(x_710);
lean_dec(x_699);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_777 = lean_ctor_get(x_715, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_715, 1);
lean_inc(x_778);
lean_dec(x_715);
x_8 = x_777;
x_9 = x_778;
goto block_16;
}
}
else
{
lean_object* x_779; lean_object* x_780; 
lean_dec(x_710);
lean_dec(x_699);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_779 = lean_ctor_get(x_711, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_711, 1);
lean_inc(x_780);
lean_dec(x_711);
x_8 = x_779;
x_9 = x_780;
goto block_16;
}
}
}
else
{
lean_object* x_781; lean_object* x_782; 
lean_dec(x_699);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_781 = lean_ctor_get(x_704, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_704, 1);
lean_inc(x_782);
lean_dec(x_704);
x_8 = x_781;
x_9 = x_782;
goto block_16;
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_699);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_783 = lean_ctor_get(x_700, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_784 = x_700;
} else {
 lean_dec_ref(x_700);
 x_784 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_695);
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_57);
lean_ctor_set(x_785, 1, x_783);
return x_785;
}
}
else
{
lean_object* x_786; lean_object* x_787; 
lean_dec(x_699);
lean_dec(x_695);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_786 = lean_ctor_get(x_700, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_700, 1);
lean_inc(x_787);
lean_dec(x_700);
x_8 = x_786;
x_9 = x_787;
goto block_16;
}
}
else
{
lean_object* x_788; lean_object* x_789; 
lean_dec(x_695);
lean_dec(x_51);
lean_dec(x_689);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_788 = lean_ctor_get(x_696, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_696, 1);
lean_inc(x_789);
lean_dec(x_696);
x_8 = x_788;
x_9 = x_789;
goto block_16;
}
}
else
{
lean_object* x_790; lean_object* x_791; 
lean_dec(x_682);
lean_dec(x_680);
lean_dec(x_677);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_790 = lean_ctor_get(x_683, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_683, 1);
lean_inc(x_791);
lean_dec(x_683);
x_8 = x_790;
x_9 = x_791;
goto block_16;
}
}
else
{
lean_object* x_792; lean_object* x_793; 
lean_dec(x_677);
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_792 = lean_ctor_get(x_679, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_679, 1);
lean_inc(x_793);
lean_dec(x_679);
x_8 = x_792;
x_9 = x_793;
goto block_16;
}
}
}
else
{
lean_object* x_794; lean_object* x_795; 
lean_dec(x_135);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_794 = lean_ctor_get(x_136, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_136, 1);
lean_inc(x_795);
lean_dec(x_136);
x_8 = x_794;
x_9 = x_795;
goto block_16;
}
}
else
{
uint8_t x_796; 
lean_dec(x_133);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_796 = !lean_is_exclusive(x_132);
if (x_796 == 0)
{
lean_object* x_797; 
x_797 = lean_ctor_get(x_132, 0);
lean_dec(x_797);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
else
{
lean_object* x_798; lean_object* x_799; 
x_798 = lean_ctor_get(x_132, 1);
lean_inc(x_798);
lean_dec(x_132);
x_799 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_799, 0, x_131);
lean_ctor_set(x_799, 1, x_798);
return x_799;
}
}
}
else
{
lean_object* x_800; lean_object* x_801; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_800 = lean_ctor_get(x_132, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_132, 1);
lean_inc(x_801);
lean_dec(x_132);
x_8 = x_800;
x_9 = x_801;
goto block_16;
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_802 = lean_ctor_get(x_123, 0);
x_803 = lean_ctor_get(x_123, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_123);
x_804 = lean_box(0);
x_805 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_805, 0, x_802);
lean_ctor_set(x_805, 1, x_804);
lean_ctor_set_tag(x_119, 1);
lean_ctor_set(x_119, 1, x_805);
lean_ctor_set_tag(x_104, 1);
lean_ctor_set(x_104, 1, x_119);
lean_ctor_set(x_104, 0, x_102);
x_806 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_807 = l_Lean_Expr_const___override(x_806, x_104);
lean_inc(x_54);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_804);
lean_ctor_set(x_100, 0, x_54);
lean_inc(x_68);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 1, x_100);
x_808 = lean_array_mk(x_65);
x_809 = l_Lean_mkAppN(x_807, x_808);
lean_dec(x_808);
x_810 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_811 = l_Lean_Meta_trySynthInstance(x_809, x_810, x_3, x_4, x_5, x_6, x_803);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
if (lean_obj_tag(x_812) == 1)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
x_814 = lean_ctor_get(x_812, 0);
lean_inc(x_814);
lean_dec(x_812);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_815 = l_Lean_Meta_getDecLevel(x_69, x_3, x_4, x_5, x_6, x_813);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
if (lean_is_exclusive(x_815)) {
 lean_ctor_release(x_815, 0);
 lean_ctor_release(x_815, 1);
 x_818 = x_815;
} else {
 lean_dec_ref(x_815);
 x_818 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_819 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_817);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_822 = x_819;
} else {
 lean_dec_ref(x_819);
 x_822 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_823 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_821);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_823, 1);
lean_inc(x_825);
if (lean_is_exclusive(x_823)) {
 lean_ctor_release(x_823, 0);
 lean_ctor_release(x_823, 1);
 x_826 = x_823;
} else {
 lean_dec_ref(x_823);
 x_826 = lean_box(0);
}
if (lean_is_scalar(x_826)) {
 x_827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_827 = x_826;
 lean_ctor_set_tag(x_827, 1);
}
lean_ctor_set(x_827, 0, x_824);
lean_ctor_set(x_827, 1, x_804);
if (lean_is_scalar(x_822)) {
 x_828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_828 = x_822;
 lean_ctor_set_tag(x_828, 1);
}
lean_ctor_set(x_828, 0, x_820);
lean_ctor_set(x_828, 1, x_827);
if (lean_is_scalar(x_818)) {
 x_829 = lean_alloc_ctor(1, 2, 0);
} else {
 x_829 = x_818;
 lean_ctor_set_tag(x_829, 1);
}
lean_ctor_set(x_829, 0, x_816);
lean_ctor_set(x_829, 1, x_828);
x_830 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_829);
x_831 = l_Lean_Expr_const___override(x_830, x_829);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_804);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_814);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_814);
lean_inc(x_54);
x_832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_832, 0, x_54);
lean_ctor_set(x_832, 1, x_31);
lean_inc(x_68);
x_833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_833, 0, x_68);
lean_ctor_set(x_833, 1, x_832);
x_834 = lean_array_mk(x_833);
x_835 = l_Lean_mkAppN(x_831, x_834);
lean_dec(x_834);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_835);
x_836 = lean_infer_type(x_835, x_3, x_4, x_5, x_6, x_825);
if (lean_obj_tag(x_836) == 0)
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_840 = l_Lean_Meta_isExprDefEq(x_33, x_837, x_3, x_4, x_5, x_6, x_838);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; uint8_t x_842; 
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_unbox(x_841);
lean_dec(x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; 
lean_dec(x_835);
lean_free_object(x_57);
x_843 = lean_ctor_get(x_840, 1);
lean_inc(x_843);
lean_dec(x_840);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_844 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_843);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; 
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_dec(x_839);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_846 = lean_ctor_get(x_844, 1);
lean_inc(x_846);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_847 = x_844;
} else {
 lean_dec_ref(x_844);
 x_847 = lean_box(0);
}
if (lean_is_scalar(x_847)) {
 x_848 = lean_alloc_ctor(0, 2, 0);
} else {
 x_848 = x_847;
}
lean_ctor_set(x_848, 0, x_810);
lean_ctor_set(x_848, 1, x_846);
return x_848;
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_849 = lean_ctor_get(x_844, 1);
lean_inc(x_849);
lean_dec(x_844);
x_850 = lean_ctor_get(x_845, 0);
lean_inc(x_850);
lean_dec(x_845);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_851 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_849);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_854 = x_851;
} else {
 lean_dec_ref(x_851);
 x_854 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_855 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_853);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; uint8_t x_870; lean_object* x_871; lean_object* x_872; 
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_858 = x_855;
} else {
 lean_dec_ref(x_855);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(1, 2, 0);
} else {
 x_859 = x_858;
 lean_ctor_set_tag(x_859, 1);
}
lean_ctor_set(x_859, 0, x_856);
lean_ctor_set(x_859, 1, x_804);
if (lean_is_scalar(x_854)) {
 x_860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_860 = x_854;
 lean_ctor_set_tag(x_860, 1);
}
lean_ctor_set(x_860, 0, x_852);
lean_ctor_set(x_860, 1, x_859);
x_861 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_862 = l_Lean_Expr_const___override(x_861, x_860);
lean_inc(x_55);
if (lean_is_scalar(x_839)) {
 x_863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_863 = x_839;
 lean_ctor_set_tag(x_863, 1);
}
lean_ctor_set(x_863, 0, x_55);
lean_ctor_set(x_863, 1, x_804);
x_864 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_863);
lean_inc(x_69);
x_866 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_866, 0, x_69);
lean_ctor_set(x_866, 1, x_865);
x_867 = lean_array_mk(x_866);
x_868 = l_Lean_mkAppN(x_862, x_867);
lean_dec(x_867);
x_869 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_870 = 0;
lean_inc(x_69);
x_871 = l_Lean_Expr_forallE___override(x_869, x_69, x_868, x_870);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_872 = l_Lean_Meta_trySynthInstance(x_871, x_810, x_3, x_4, x_5, x_6, x_857);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
if (lean_obj_tag(x_873) == 1)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_ctor_get(x_873, 0);
lean_inc(x_875);
lean_dec(x_873);
x_876 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_877 = l_Lean_Expr_const___override(x_876, x_829);
x_878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_878, 0, x_850);
lean_ctor_set(x_878, 1, x_51);
x_879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_879, 0, x_875);
lean_ctor_set(x_879, 1, x_878);
x_880 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_880, 0, x_814);
lean_ctor_set(x_880, 1, x_879);
x_881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_881, 0, x_55);
lean_ctor_set(x_881, 1, x_880);
x_882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_882, 0, x_69);
lean_ctor_set(x_882, 1, x_881);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_54);
lean_ctor_set(x_883, 1, x_882);
x_884 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_884, 0, x_68);
lean_ctor_set(x_884, 1, x_883);
x_885 = lean_array_mk(x_884);
x_886 = l_Lean_mkAppN(x_877, x_885);
lean_dec(x_885);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_887 = l_Lean_Meta_expandCoe(x_886, x_3, x_4, x_5, x_6, x_874);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
lean_dec(x_887);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_888);
x_890 = lean_infer_type(x_888, x_3, x_4, x_5, x_6, x_889);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_893 = l_Lean_Meta_isExprDefEq(x_33, x_891, x_3, x_4, x_5, x_6, x_892);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; uint8_t x_895; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_unbox(x_894);
lean_dec(x_894);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_888);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_896 = lean_ctor_get(x_893, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_897 = x_893;
} else {
 lean_dec_ref(x_893);
 x_897 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_898 = lean_alloc_ctor(0, 2, 0);
} else {
 x_898 = x_897;
}
lean_ctor_set(x_898, 0, x_810);
lean_ctor_set(x_898, 1, x_896);
return x_898;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_899 = lean_ctor_get(x_893, 1);
lean_inc(x_899);
lean_dec(x_893);
x_900 = lean_box(0);
x_901 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_888, x_900, x_3, x_4, x_5, x_6, x_899);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_904 = x_901;
} else {
 lean_dec_ref(x_901);
 x_904 = lean_box(0);
}
if (lean_is_scalar(x_904)) {
 x_905 = lean_alloc_ctor(0, 2, 0);
} else {
 x_905 = x_904;
}
lean_ctor_set(x_905, 0, x_902);
lean_ctor_set(x_905, 1, x_903);
return x_905;
}
}
else
{
lean_object* x_906; lean_object* x_907; 
lean_dec(x_888);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_906 = lean_ctor_get(x_893, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_893, 1);
lean_inc(x_907);
lean_dec(x_893);
x_8 = x_906;
x_9 = x_907;
goto block_16;
}
}
else
{
lean_object* x_908; lean_object* x_909; 
lean_dec(x_888);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_908 = lean_ctor_get(x_890, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_890, 1);
lean_inc(x_909);
lean_dec(x_890);
x_8 = x_908;
x_9 = x_909;
goto block_16;
}
}
else
{
lean_object* x_910; lean_object* x_911; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_910 = lean_ctor_get(x_887, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_887, 1);
lean_inc(x_911);
lean_dec(x_887);
x_8 = x_910;
x_9 = x_911;
goto block_16;
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_873);
lean_dec(x_850);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_912 = lean_ctor_get(x_872, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_913 = x_872;
} else {
 lean_dec_ref(x_872);
 x_913 = lean_box(0);
}
if (lean_is_scalar(x_913)) {
 x_914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_914 = x_913;
}
lean_ctor_set(x_914, 0, x_810);
lean_ctor_set(x_914, 1, x_912);
return x_914;
}
}
else
{
lean_object* x_915; lean_object* x_916; 
lean_dec(x_850);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_915 = lean_ctor_get(x_872, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_872, 1);
lean_inc(x_916);
lean_dec(x_872);
x_8 = x_915;
x_9 = x_916;
goto block_16;
}
}
else
{
lean_object* x_917; lean_object* x_918; 
lean_dec(x_854);
lean_dec(x_852);
lean_dec(x_850);
lean_dec(x_839);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_917 = lean_ctor_get(x_855, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_855, 1);
lean_inc(x_918);
lean_dec(x_855);
x_8 = x_917;
x_9 = x_918;
goto block_16;
}
}
else
{
lean_object* x_919; lean_object* x_920; 
lean_dec(x_850);
lean_dec(x_839);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_919 = lean_ctor_get(x_851, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_851, 1);
lean_inc(x_920);
lean_dec(x_851);
x_8 = x_919;
x_9 = x_920;
goto block_16;
}
}
}
else
{
lean_object* x_921; lean_object* x_922; 
lean_dec(x_839);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_921 = lean_ctor_get(x_844, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_844, 1);
lean_inc(x_922);
lean_dec(x_844);
x_8 = x_921;
x_9 = x_922;
goto block_16;
}
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_839);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_923 = lean_ctor_get(x_840, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 lean_ctor_release(x_840, 1);
 x_924 = x_840;
} else {
 lean_dec_ref(x_840);
 x_924 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_835);
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(0, 2, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_57);
lean_ctor_set(x_925, 1, x_923);
return x_925;
}
}
else
{
lean_object* x_926; lean_object* x_927; 
lean_dec(x_839);
lean_dec(x_835);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_926 = lean_ctor_get(x_840, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_840, 1);
lean_inc(x_927);
lean_dec(x_840);
x_8 = x_926;
x_9 = x_927;
goto block_16;
}
}
else
{
lean_object* x_928; lean_object* x_929; 
lean_dec(x_835);
lean_dec(x_51);
lean_dec(x_829);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_928 = lean_ctor_get(x_836, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_836, 1);
lean_inc(x_929);
lean_dec(x_836);
x_8 = x_928;
x_9 = x_929;
goto block_16;
}
}
else
{
lean_object* x_930; lean_object* x_931; 
lean_dec(x_822);
lean_dec(x_820);
lean_dec(x_818);
lean_dec(x_816);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_930 = lean_ctor_get(x_823, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_823, 1);
lean_inc(x_931);
lean_dec(x_823);
x_8 = x_930;
x_9 = x_931;
goto block_16;
}
}
else
{
lean_object* x_932; lean_object* x_933; 
lean_dec(x_818);
lean_dec(x_816);
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_932 = lean_ctor_get(x_819, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_819, 1);
lean_inc(x_933);
lean_dec(x_819);
x_8 = x_932;
x_9 = x_933;
goto block_16;
}
}
else
{
lean_object* x_934; lean_object* x_935; 
lean_dec(x_814);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_934 = lean_ctor_get(x_815, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_815, 1);
lean_inc(x_935);
lean_dec(x_815);
x_8 = x_934;
x_9 = x_935;
goto block_16;
}
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_812);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_936 = lean_ctor_get(x_811, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_937 = x_811;
} else {
 lean_dec_ref(x_811);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_810);
lean_ctor_set(x_938, 1, x_936);
return x_938;
}
}
else
{
lean_object* x_939; lean_object* x_940; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_939 = lean_ctor_get(x_811, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_811, 1);
lean_inc(x_940);
lean_dec(x_811);
x_8 = x_939;
x_9 = x_940;
goto block_16;
}
}
}
else
{
lean_object* x_941; lean_object* x_942; 
lean_free_object(x_119);
lean_dec(x_121);
lean_free_object(x_104);
lean_free_object(x_100);
lean_dec(x_102);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_941 = lean_ctor_get(x_123, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_123, 1);
lean_inc(x_942);
lean_dec(x_123);
x_8 = x_941;
x_9 = x_942;
goto block_16;
}
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_943 = lean_ctor_get(x_119, 0);
x_944 = lean_ctor_get(x_119, 1);
lean_inc(x_944);
lean_inc(x_943);
lean_dec(x_119);
x_945 = l_Lean_Meta_decLevel(x_99, x_3, x_4, x_5, x_6, x_944);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_948 = x_945;
} else {
 lean_dec_ref(x_945);
 x_948 = lean_box(0);
}
x_949 = lean_box(0);
if (lean_is_scalar(x_948)) {
 x_950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_950 = x_948;
 lean_ctor_set_tag(x_950, 1);
}
lean_ctor_set(x_950, 0, x_946);
lean_ctor_set(x_950, 1, x_949);
x_951 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_951, 0, x_943);
lean_ctor_set(x_951, 1, x_950);
lean_ctor_set_tag(x_104, 1);
lean_ctor_set(x_104, 1, x_951);
lean_ctor_set(x_104, 0, x_102);
x_952 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_953 = l_Lean_Expr_const___override(x_952, x_104);
lean_inc(x_54);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_949);
lean_ctor_set(x_100, 0, x_54);
lean_inc(x_68);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 1, x_100);
x_954 = lean_array_mk(x_65);
x_955 = l_Lean_mkAppN(x_953, x_954);
lean_dec(x_954);
x_956 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_957 = l_Lean_Meta_trySynthInstance(x_955, x_956, x_3, x_4, x_5, x_6, x_947);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; 
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
if (lean_obj_tag(x_958) == 1)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_959 = lean_ctor_get(x_957, 1);
lean_inc(x_959);
lean_dec(x_957);
x_960 = lean_ctor_get(x_958, 0);
lean_inc(x_960);
lean_dec(x_958);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_961 = l_Lean_Meta_getDecLevel(x_69, x_3, x_4, x_5, x_6, x_959);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_964 = x_961;
} else {
 lean_dec_ref(x_961);
 x_964 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_965 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_963);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 x_968 = x_965;
} else {
 lean_dec_ref(x_965);
 x_968 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_969 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_967);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_972 = x_969;
} else {
 lean_dec_ref(x_969);
 x_972 = lean_box(0);
}
if (lean_is_scalar(x_972)) {
 x_973 = lean_alloc_ctor(1, 2, 0);
} else {
 x_973 = x_972;
 lean_ctor_set_tag(x_973, 1);
}
lean_ctor_set(x_973, 0, x_970);
lean_ctor_set(x_973, 1, x_949);
if (lean_is_scalar(x_968)) {
 x_974 = lean_alloc_ctor(1, 2, 0);
} else {
 x_974 = x_968;
 lean_ctor_set_tag(x_974, 1);
}
lean_ctor_set(x_974, 0, x_966);
lean_ctor_set(x_974, 1, x_973);
if (lean_is_scalar(x_964)) {
 x_975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_975 = x_964;
 lean_ctor_set_tag(x_975, 1);
}
lean_ctor_set(x_975, 0, x_962);
lean_ctor_set(x_975, 1, x_974);
x_976 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_975);
x_977 = l_Lean_Expr_const___override(x_976, x_975);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_949);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_960);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_960);
lean_inc(x_54);
x_978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_978, 0, x_54);
lean_ctor_set(x_978, 1, x_31);
lean_inc(x_68);
x_979 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_979, 0, x_68);
lean_ctor_set(x_979, 1, x_978);
x_980 = lean_array_mk(x_979);
x_981 = l_Lean_mkAppN(x_977, x_980);
lean_dec(x_980);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_981);
x_982 = lean_infer_type(x_981, x_3, x_4, x_5, x_6, x_971);
if (lean_obj_tag(x_982) == 0)
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_985 = x_982;
} else {
 lean_dec_ref(x_982);
 x_985 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_986 = l_Lean_Meta_isExprDefEq(x_33, x_983, x_3, x_4, x_5, x_6, x_984);
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_987; uint8_t x_988; 
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
x_988 = lean_unbox(x_987);
lean_dec(x_987);
if (x_988 == 0)
{
lean_object* x_989; lean_object* x_990; 
lean_dec(x_981);
lean_free_object(x_57);
x_989 = lean_ctor_get(x_986, 1);
lean_inc(x_989);
lean_dec(x_986);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_990 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_989);
if (lean_obj_tag(x_990) == 0)
{
lean_object* x_991; 
x_991 = lean_ctor_get(x_990, 0);
lean_inc(x_991);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_985);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_992 = lean_ctor_get(x_990, 1);
lean_inc(x_992);
if (lean_is_exclusive(x_990)) {
 lean_ctor_release(x_990, 0);
 lean_ctor_release(x_990, 1);
 x_993 = x_990;
} else {
 lean_dec_ref(x_990);
 x_993 = lean_box(0);
}
if (lean_is_scalar(x_993)) {
 x_994 = lean_alloc_ctor(0, 2, 0);
} else {
 x_994 = x_993;
}
lean_ctor_set(x_994, 0, x_956);
lean_ctor_set(x_994, 1, x_992);
return x_994;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_995 = lean_ctor_get(x_990, 1);
lean_inc(x_995);
lean_dec(x_990);
x_996 = lean_ctor_get(x_991, 0);
lean_inc(x_996);
lean_dec(x_991);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_997 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_995);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1001 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_999);
if (lean_obj_tag(x_1001) == 0)
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; uint8_t x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_1001, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_1001)) {
 lean_ctor_release(x_1001, 0);
 lean_ctor_release(x_1001, 1);
 x_1004 = x_1001;
} else {
 lean_dec_ref(x_1001);
 x_1004 = lean_box(0);
}
if (lean_is_scalar(x_1004)) {
 x_1005 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1005 = x_1004;
 lean_ctor_set_tag(x_1005, 1);
}
lean_ctor_set(x_1005, 0, x_1002);
lean_ctor_set(x_1005, 1, x_949);
if (lean_is_scalar(x_1000)) {
 x_1006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1006 = x_1000;
 lean_ctor_set_tag(x_1006, 1);
}
lean_ctor_set(x_1006, 0, x_998);
lean_ctor_set(x_1006, 1, x_1005);
x_1007 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1008 = l_Lean_Expr_const___override(x_1007, x_1006);
lean_inc(x_55);
if (lean_is_scalar(x_985)) {
 x_1009 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1009 = x_985;
 lean_ctor_set_tag(x_1009, 1);
}
lean_ctor_set(x_1009, 0, x_55);
lean_ctor_set(x_1009, 1, x_949);
x_1010 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1011, 0, x_1010);
lean_ctor_set(x_1011, 1, x_1009);
lean_inc(x_69);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_69);
lean_ctor_set(x_1012, 1, x_1011);
x_1013 = lean_array_mk(x_1012);
x_1014 = l_Lean_mkAppN(x_1008, x_1013);
lean_dec(x_1013);
x_1015 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1016 = 0;
lean_inc(x_69);
x_1017 = l_Lean_Expr_forallE___override(x_1015, x_69, x_1014, x_1016);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1018 = l_Lean_Meta_trySynthInstance(x_1017, x_956, x_3, x_4, x_5, x_6, x_1003);
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1019; 
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
if (lean_obj_tag(x_1019) == 1)
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1020 = lean_ctor_get(x_1018, 1);
lean_inc(x_1020);
lean_dec(x_1018);
x_1021 = lean_ctor_get(x_1019, 0);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1023 = l_Lean_Expr_const___override(x_1022, x_975);
x_1024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1024, 0, x_996);
lean_ctor_set(x_1024, 1, x_51);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1021);
lean_ctor_set(x_1025, 1, x_1024);
x_1026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1026, 0, x_960);
lean_ctor_set(x_1026, 1, x_1025);
x_1027 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1027, 0, x_55);
lean_ctor_set(x_1027, 1, x_1026);
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_69);
lean_ctor_set(x_1028, 1, x_1027);
x_1029 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1029, 0, x_54);
lean_ctor_set(x_1029, 1, x_1028);
x_1030 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1030, 0, x_68);
lean_ctor_set(x_1030, 1, x_1029);
x_1031 = lean_array_mk(x_1030);
x_1032 = l_Lean_mkAppN(x_1023, x_1031);
lean_dec(x_1031);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1033 = l_Lean_Meta_expandCoe(x_1032, x_3, x_4, x_5, x_6, x_1020);
if (lean_obj_tag(x_1033) == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
x_1034 = lean_ctor_get(x_1033, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1033, 1);
lean_inc(x_1035);
lean_dec(x_1033);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1034);
x_1036 = lean_infer_type(x_1034, x_3, x_4, x_5, x_6, x_1035);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
lean_dec(x_1036);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1039 = l_Lean_Meta_isExprDefEq(x_33, x_1037, x_3, x_4, x_5, x_6, x_1038);
if (lean_obj_tag(x_1039) == 0)
{
lean_object* x_1040; uint8_t x_1041; 
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_unbox(x_1040);
lean_dec(x_1040);
if (x_1041 == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_1034);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1042 = lean_ctor_get(x_1039, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_1039)) {
 lean_ctor_release(x_1039, 0);
 lean_ctor_release(x_1039, 1);
 x_1043 = x_1039;
} else {
 lean_dec_ref(x_1039);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1043)) {
 x_1044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1044 = x_1043;
}
lean_ctor_set(x_1044, 0, x_956);
lean_ctor_set(x_1044, 1, x_1042);
return x_1044;
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1045 = lean_ctor_get(x_1039, 1);
lean_inc(x_1045);
lean_dec(x_1039);
x_1046 = lean_box(0);
x_1047 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1034, x_1046, x_3, x_4, x_5, x_6, x_1045);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1050 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1048);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
else
{
lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_1034);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1052 = lean_ctor_get(x_1039, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1039, 1);
lean_inc(x_1053);
lean_dec(x_1039);
x_8 = x_1052;
x_9 = x_1053;
goto block_16;
}
}
else
{
lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1034);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1054 = lean_ctor_get(x_1036, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1036, 1);
lean_inc(x_1055);
lean_dec(x_1036);
x_8 = x_1054;
x_9 = x_1055;
goto block_16;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1056 = lean_ctor_get(x_1033, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1033, 1);
lean_inc(x_1057);
lean_dec(x_1033);
x_8 = x_1056;
x_9 = x_1057;
goto block_16;
}
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_1019);
lean_dec(x_996);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1058 = lean_ctor_get(x_1018, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 x_1059 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_956);
lean_ctor_set(x_1060, 1, x_1058);
return x_1060;
}
}
else
{
lean_object* x_1061; lean_object* x_1062; 
lean_dec(x_996);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1061 = lean_ctor_get(x_1018, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1018, 1);
lean_inc(x_1062);
lean_dec(x_1018);
x_8 = x_1061;
x_9 = x_1062;
goto block_16;
}
}
else
{
lean_object* x_1063; lean_object* x_1064; 
lean_dec(x_1000);
lean_dec(x_998);
lean_dec(x_996);
lean_dec(x_985);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1063 = lean_ctor_get(x_1001, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1001, 1);
lean_inc(x_1064);
lean_dec(x_1001);
x_8 = x_1063;
x_9 = x_1064;
goto block_16;
}
}
else
{
lean_object* x_1065; lean_object* x_1066; 
lean_dec(x_996);
lean_dec(x_985);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1065 = lean_ctor_get(x_997, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_997, 1);
lean_inc(x_1066);
lean_dec(x_997);
x_8 = x_1065;
x_9 = x_1066;
goto block_16;
}
}
}
else
{
lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_985);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1067 = lean_ctor_get(x_990, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_990, 1);
lean_inc(x_1068);
lean_dec(x_990);
x_8 = x_1067;
x_9 = x_1068;
goto block_16;
}
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_985);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1069 = lean_ctor_get(x_986, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 x_1070 = x_986;
} else {
 lean_dec_ref(x_986);
 x_1070 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_981);
if (lean_is_scalar(x_1070)) {
 x_1071 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1071 = x_1070;
}
lean_ctor_set(x_1071, 0, x_57);
lean_ctor_set(x_1071, 1, x_1069);
return x_1071;
}
}
else
{
lean_object* x_1072; lean_object* x_1073; 
lean_dec(x_985);
lean_dec(x_981);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1072 = lean_ctor_get(x_986, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_986, 1);
lean_inc(x_1073);
lean_dec(x_986);
x_8 = x_1072;
x_9 = x_1073;
goto block_16;
}
}
else
{
lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_981);
lean_dec(x_51);
lean_dec(x_975);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1074 = lean_ctor_get(x_982, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_982, 1);
lean_inc(x_1075);
lean_dec(x_982);
x_8 = x_1074;
x_9 = x_1075;
goto block_16;
}
}
else
{
lean_object* x_1076; lean_object* x_1077; 
lean_dec(x_968);
lean_dec(x_966);
lean_dec(x_964);
lean_dec(x_962);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1076 = lean_ctor_get(x_969, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_969, 1);
lean_inc(x_1077);
lean_dec(x_969);
x_8 = x_1076;
x_9 = x_1077;
goto block_16;
}
}
else
{
lean_object* x_1078; lean_object* x_1079; 
lean_dec(x_964);
lean_dec(x_962);
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1078 = lean_ctor_get(x_965, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_965, 1);
lean_inc(x_1079);
lean_dec(x_965);
x_8 = x_1078;
x_9 = x_1079;
goto block_16;
}
}
else
{
lean_object* x_1080; lean_object* x_1081; 
lean_dec(x_960);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1080 = lean_ctor_get(x_961, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_961, 1);
lean_inc(x_1081);
lean_dec(x_961);
x_8 = x_1080;
x_9 = x_1081;
goto block_16;
}
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_958);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1082 = lean_ctor_get(x_957, 1);
lean_inc(x_1082);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_1083 = x_957;
} else {
 lean_dec_ref(x_957);
 x_1083 = lean_box(0);
}
if (lean_is_scalar(x_1083)) {
 x_1084 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1084 = x_1083;
}
lean_ctor_set(x_1084, 0, x_956);
lean_ctor_set(x_1084, 1, x_1082);
return x_1084;
}
}
else
{
lean_object* x_1085; lean_object* x_1086; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1085 = lean_ctor_get(x_957, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_957, 1);
lean_inc(x_1086);
lean_dec(x_957);
x_8 = x_1085;
x_9 = x_1086;
goto block_16;
}
}
else
{
lean_object* x_1087; lean_object* x_1088; 
lean_dec(x_943);
lean_free_object(x_104);
lean_free_object(x_100);
lean_dec(x_102);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1087 = lean_ctor_get(x_945, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_945, 1);
lean_inc(x_1088);
lean_dec(x_945);
x_8 = x_1087;
x_9 = x_1088;
goto block_16;
}
}
}
else
{
lean_object* x_1089; lean_object* x_1090; 
lean_free_object(x_104);
lean_free_object(x_100);
lean_dec(x_102);
lean_dec(x_99);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1089 = lean_ctor_get(x_119, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_119, 1);
lean_inc(x_1090);
lean_dec(x_119);
x_8 = x_1089;
x_9 = x_1090;
goto block_16;
}
}
}
else
{
lean_object* x_1091; lean_object* x_1092; 
lean_free_object(x_104);
lean_free_object(x_100);
lean_dec(x_102);
lean_dec(x_99);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1091 = lean_ctor_get(x_109, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_109, 1);
lean_inc(x_1092);
lean_dec(x_109);
x_8 = x_1091;
x_9 = x_1092;
goto block_16;
}
}
else
{
lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; lean_object* x_1096; 
x_1093 = lean_ctor_get(x_104, 0);
x_1094 = lean_ctor_get(x_104, 1);
lean_inc(x_1094);
lean_inc(x_1093);
lean_dec(x_104);
x_1095 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_102);
x_1096 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_102, x_1093, x_1095, x_3, x_4, x_5, x_6, x_1094);
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1097; uint8_t x_1098; 
x_1097 = lean_ctor_get(x_1096, 0);
lean_inc(x_1097);
x_1098 = lean_unbox(x_1097);
lean_dec(x_1097);
if (x_1098 == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
lean_free_object(x_100);
lean_dec(x_102);
lean_dec(x_99);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1099 = lean_ctor_get(x_1096, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1100 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1100 = lean_box(0);
}
x_1101 = lean_box(0);
if (lean_is_scalar(x_1100)) {
 x_1102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1102 = x_1100;
}
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_1099);
return x_1102;
}
else
{
lean_object* x_1103; lean_object* x_1104; 
x_1103 = lean_ctor_get(x_1096, 1);
lean_inc(x_1103);
lean_dec(x_1096);
x_1104 = l_Lean_Meta_decLevel(x_89, x_3, x_4, x_5, x_6, x_1103);
if (lean_obj_tag(x_1104) == 0)
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1104, 1);
lean_inc(x_1106);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1107 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1107 = lean_box(0);
}
x_1108 = l_Lean_Meta_decLevel(x_99, x_3, x_4, x_5, x_6, x_1106);
if (lean_obj_tag(x_1108) == 0)
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
if (lean_is_exclusive(x_1108)) {
 lean_ctor_release(x_1108, 0);
 lean_ctor_release(x_1108, 1);
 x_1111 = x_1108;
} else {
 lean_dec_ref(x_1108);
 x_1111 = lean_box(0);
}
x_1112 = lean_box(0);
if (lean_is_scalar(x_1111)) {
 x_1113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1113 = x_1111;
 lean_ctor_set_tag(x_1113, 1);
}
lean_ctor_set(x_1113, 0, x_1109);
lean_ctor_set(x_1113, 1, x_1112);
if (lean_is_scalar(x_1107)) {
 x_1114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1114 = x_1107;
 lean_ctor_set_tag(x_1114, 1);
}
lean_ctor_set(x_1114, 0, x_1105);
lean_ctor_set(x_1114, 1, x_1113);
x_1115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1115, 0, x_102);
lean_ctor_set(x_1115, 1, x_1114);
x_1116 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1117 = l_Lean_Expr_const___override(x_1116, x_1115);
lean_inc(x_54);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_1112);
lean_ctor_set(x_100, 0, x_54);
lean_inc(x_68);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 1, x_100);
x_1118 = lean_array_mk(x_65);
x_1119 = l_Lean_mkAppN(x_1117, x_1118);
lean_dec(x_1118);
x_1120 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1121 = l_Lean_Meta_trySynthInstance(x_1119, x_1120, x_3, x_4, x_5, x_6, x_1110);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
if (lean_obj_tag(x_1122) == 1)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1123 = lean_ctor_get(x_1121, 1);
lean_inc(x_1123);
lean_dec(x_1121);
x_1124 = lean_ctor_get(x_1122, 0);
lean_inc(x_1124);
lean_dec(x_1122);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_1125 = l_Lean_Meta_getDecLevel(x_69, x_3, x_4, x_5, x_6, x_1123);
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
x_1127 = lean_ctor_get(x_1125, 1);
lean_inc(x_1127);
if (lean_is_exclusive(x_1125)) {
 lean_ctor_release(x_1125, 0);
 lean_ctor_release(x_1125, 1);
 x_1128 = x_1125;
} else {
 lean_dec_ref(x_1125);
 x_1128 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1129 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_1127);
if (lean_obj_tag(x_1129) == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1130 = lean_ctor_get(x_1129, 0);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1129, 1);
lean_inc(x_1131);
if (lean_is_exclusive(x_1129)) {
 lean_ctor_release(x_1129, 0);
 lean_ctor_release(x_1129, 1);
 x_1132 = x_1129;
} else {
 lean_dec_ref(x_1129);
 x_1132 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_1133 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_1131);
if (lean_obj_tag(x_1133) == 0)
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1133, 1);
lean_inc(x_1135);
if (lean_is_exclusive(x_1133)) {
 lean_ctor_release(x_1133, 0);
 lean_ctor_release(x_1133, 1);
 x_1136 = x_1133;
} else {
 lean_dec_ref(x_1133);
 x_1136 = lean_box(0);
}
if (lean_is_scalar(x_1136)) {
 x_1137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1137 = x_1136;
 lean_ctor_set_tag(x_1137, 1);
}
lean_ctor_set(x_1137, 0, x_1134);
lean_ctor_set(x_1137, 1, x_1112);
if (lean_is_scalar(x_1132)) {
 x_1138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1138 = x_1132;
 lean_ctor_set_tag(x_1138, 1);
}
lean_ctor_set(x_1138, 0, x_1130);
lean_ctor_set(x_1138, 1, x_1137);
if (lean_is_scalar(x_1128)) {
 x_1139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1139 = x_1128;
 lean_ctor_set_tag(x_1139, 1);
}
lean_ctor_set(x_1139, 0, x_1126);
lean_ctor_set(x_1139, 1, x_1138);
x_1140 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_1139);
x_1141 = l_Lean_Expr_const___override(x_1140, x_1139);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_1112);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_1124);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_1124);
lean_inc(x_54);
x_1142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1142, 0, x_54);
lean_ctor_set(x_1142, 1, x_31);
lean_inc(x_68);
x_1143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1143, 0, x_68);
lean_ctor_set(x_1143, 1, x_1142);
x_1144 = lean_array_mk(x_1143);
x_1145 = l_Lean_mkAppN(x_1141, x_1144);
lean_dec(x_1144);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1145);
x_1146 = lean_infer_type(x_1145, x_3, x_4, x_5, x_6, x_1135);
if (lean_obj_tag(x_1146) == 0)
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1147 = lean_ctor_get(x_1146, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1146, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1146)) {
 lean_ctor_release(x_1146, 0);
 lean_ctor_release(x_1146, 1);
 x_1149 = x_1146;
} else {
 lean_dec_ref(x_1146);
 x_1149 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_1150 = l_Lean_Meta_isExprDefEq(x_33, x_1147, x_3, x_4, x_5, x_6, x_1148);
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; uint8_t x_1152; 
x_1151 = lean_ctor_get(x_1150, 0);
lean_inc(x_1151);
x_1152 = lean_unbox(x_1151);
lean_dec(x_1151);
if (x_1152 == 0)
{
lean_object* x_1153; lean_object* x_1154; 
lean_dec(x_1145);
lean_free_object(x_57);
x_1153 = lean_ctor_get(x_1150, 1);
lean_inc(x_1153);
lean_dec(x_1150);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_1154 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_1153);
if (lean_obj_tag(x_1154) == 0)
{
lean_object* x_1155; 
x_1155 = lean_ctor_get(x_1154, 0);
lean_inc(x_1155);
if (lean_obj_tag(x_1155) == 0)
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_1149);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1156 = lean_ctor_get(x_1154, 1);
lean_inc(x_1156);
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 lean_ctor_release(x_1154, 1);
 x_1157 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1157 = lean_box(0);
}
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_1120);
lean_ctor_set(x_1158, 1, x_1156);
return x_1158;
}
else
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1159 = lean_ctor_get(x_1154, 1);
lean_inc(x_1159);
lean_dec(x_1154);
x_1160 = lean_ctor_get(x_1155, 0);
lean_inc(x_1160);
lean_dec(x_1155);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_1161 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_1159);
if (lean_obj_tag(x_1161) == 0)
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1161, 1);
lean_inc(x_1163);
if (lean_is_exclusive(x_1161)) {
 lean_ctor_release(x_1161, 0);
 lean_ctor_release(x_1161, 1);
 x_1164 = x_1161;
} else {
 lean_dec_ref(x_1161);
 x_1164 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1165 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_1163);
if (lean_obj_tag(x_1165) == 0)
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; uint8_t x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
if (lean_is_exclusive(x_1165)) {
 lean_ctor_release(x_1165, 0);
 lean_ctor_release(x_1165, 1);
 x_1168 = x_1165;
} else {
 lean_dec_ref(x_1165);
 x_1168 = lean_box(0);
}
if (lean_is_scalar(x_1168)) {
 x_1169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1169 = x_1168;
 lean_ctor_set_tag(x_1169, 1);
}
lean_ctor_set(x_1169, 0, x_1166);
lean_ctor_set(x_1169, 1, x_1112);
if (lean_is_scalar(x_1164)) {
 x_1170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1170 = x_1164;
 lean_ctor_set_tag(x_1170, 1);
}
lean_ctor_set(x_1170, 0, x_1162);
lean_ctor_set(x_1170, 1, x_1169);
x_1171 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1172 = l_Lean_Expr_const___override(x_1171, x_1170);
lean_inc(x_55);
if (lean_is_scalar(x_1149)) {
 x_1173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1173 = x_1149;
 lean_ctor_set_tag(x_1173, 1);
}
lean_ctor_set(x_1173, 0, x_55);
lean_ctor_set(x_1173, 1, x_1112);
x_1174 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1175, 0, x_1174);
lean_ctor_set(x_1175, 1, x_1173);
lean_inc(x_69);
x_1176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1176, 0, x_69);
lean_ctor_set(x_1176, 1, x_1175);
x_1177 = lean_array_mk(x_1176);
x_1178 = l_Lean_mkAppN(x_1172, x_1177);
lean_dec(x_1177);
x_1179 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1180 = 0;
lean_inc(x_69);
x_1181 = l_Lean_Expr_forallE___override(x_1179, x_69, x_1178, x_1180);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1182 = l_Lean_Meta_trySynthInstance(x_1181, x_1120, x_3, x_4, x_5, x_6, x_1167);
if (lean_obj_tag(x_1182) == 0)
{
lean_object* x_1183; 
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
if (lean_obj_tag(x_1183) == 1)
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; 
x_1184 = lean_ctor_get(x_1182, 1);
lean_inc(x_1184);
lean_dec(x_1182);
x_1185 = lean_ctor_get(x_1183, 0);
lean_inc(x_1185);
lean_dec(x_1183);
x_1186 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1187 = l_Lean_Expr_const___override(x_1186, x_1139);
x_1188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1188, 0, x_1160);
lean_ctor_set(x_1188, 1, x_51);
x_1189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1189, 0, x_1185);
lean_ctor_set(x_1189, 1, x_1188);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1124);
lean_ctor_set(x_1190, 1, x_1189);
x_1191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1191, 0, x_55);
lean_ctor_set(x_1191, 1, x_1190);
x_1192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1192, 0, x_69);
lean_ctor_set(x_1192, 1, x_1191);
x_1193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1193, 0, x_54);
lean_ctor_set(x_1193, 1, x_1192);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_68);
lean_ctor_set(x_1194, 1, x_1193);
x_1195 = lean_array_mk(x_1194);
x_1196 = l_Lean_mkAppN(x_1187, x_1195);
lean_dec(x_1195);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1197 = l_Lean_Meta_expandCoe(x_1196, x_3, x_4, x_5, x_6, x_1184);
if (lean_obj_tag(x_1197) == 0)
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
x_1198 = lean_ctor_get(x_1197, 0);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_1197, 1);
lean_inc(x_1199);
lean_dec(x_1197);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1198);
x_1200 = lean_infer_type(x_1198, x_3, x_4, x_5, x_6, x_1199);
if (lean_obj_tag(x_1200) == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
lean_dec(x_1200);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1203 = l_Lean_Meta_isExprDefEq(x_33, x_1201, x_3, x_4, x_5, x_6, x_1202);
if (lean_obj_tag(x_1203) == 0)
{
lean_object* x_1204; uint8_t x_1205; 
x_1204 = lean_ctor_get(x_1203, 0);
lean_inc(x_1204);
x_1205 = lean_unbox(x_1204);
lean_dec(x_1204);
if (x_1205 == 0)
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_dec(x_1198);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1206 = lean_ctor_get(x_1203, 1);
lean_inc(x_1206);
if (lean_is_exclusive(x_1203)) {
 lean_ctor_release(x_1203, 0);
 lean_ctor_release(x_1203, 1);
 x_1207 = x_1203;
} else {
 lean_dec_ref(x_1203);
 x_1207 = lean_box(0);
}
if (lean_is_scalar(x_1207)) {
 x_1208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1208 = x_1207;
}
lean_ctor_set(x_1208, 0, x_1120);
lean_ctor_set(x_1208, 1, x_1206);
return x_1208;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1209 = lean_ctor_get(x_1203, 1);
lean_inc(x_1209);
lean_dec(x_1203);
x_1210 = lean_box(0);
x_1211 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1198, x_1210, x_3, x_4, x_5, x_6, x_1209);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1212 = lean_ctor_get(x_1211, 0);
lean_inc(x_1212);
x_1213 = lean_ctor_get(x_1211, 1);
lean_inc(x_1213);
if (lean_is_exclusive(x_1211)) {
 lean_ctor_release(x_1211, 0);
 lean_ctor_release(x_1211, 1);
 x_1214 = x_1211;
} else {
 lean_dec_ref(x_1211);
 x_1214 = lean_box(0);
}
if (lean_is_scalar(x_1214)) {
 x_1215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1215 = x_1214;
}
lean_ctor_set(x_1215, 0, x_1212);
lean_ctor_set(x_1215, 1, x_1213);
return x_1215;
}
}
else
{
lean_object* x_1216; lean_object* x_1217; 
lean_dec(x_1198);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1216 = lean_ctor_get(x_1203, 0);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_1203, 1);
lean_inc(x_1217);
lean_dec(x_1203);
x_8 = x_1216;
x_9 = x_1217;
goto block_16;
}
}
else
{
lean_object* x_1218; lean_object* x_1219; 
lean_dec(x_1198);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1218 = lean_ctor_get(x_1200, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1200, 1);
lean_inc(x_1219);
lean_dec(x_1200);
x_8 = x_1218;
x_9 = x_1219;
goto block_16;
}
}
else
{
lean_object* x_1220; lean_object* x_1221; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1220 = lean_ctor_get(x_1197, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1197, 1);
lean_inc(x_1221);
lean_dec(x_1197);
x_8 = x_1220;
x_9 = x_1221;
goto block_16;
}
}
else
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
lean_dec(x_1183);
lean_dec(x_1160);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1222 = lean_ctor_get(x_1182, 1);
lean_inc(x_1222);
if (lean_is_exclusive(x_1182)) {
 lean_ctor_release(x_1182, 0);
 lean_ctor_release(x_1182, 1);
 x_1223 = x_1182;
} else {
 lean_dec_ref(x_1182);
 x_1223 = lean_box(0);
}
if (lean_is_scalar(x_1223)) {
 x_1224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1224 = x_1223;
}
lean_ctor_set(x_1224, 0, x_1120);
lean_ctor_set(x_1224, 1, x_1222);
return x_1224;
}
}
else
{
lean_object* x_1225; lean_object* x_1226; 
lean_dec(x_1160);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1225 = lean_ctor_get(x_1182, 0);
lean_inc(x_1225);
x_1226 = lean_ctor_get(x_1182, 1);
lean_inc(x_1226);
lean_dec(x_1182);
x_8 = x_1225;
x_9 = x_1226;
goto block_16;
}
}
else
{
lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1164);
lean_dec(x_1162);
lean_dec(x_1160);
lean_dec(x_1149);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1227 = lean_ctor_get(x_1165, 0);
lean_inc(x_1227);
x_1228 = lean_ctor_get(x_1165, 1);
lean_inc(x_1228);
lean_dec(x_1165);
x_8 = x_1227;
x_9 = x_1228;
goto block_16;
}
}
else
{
lean_object* x_1229; lean_object* x_1230; 
lean_dec(x_1160);
lean_dec(x_1149);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1229 = lean_ctor_get(x_1161, 0);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_1161, 1);
lean_inc(x_1230);
lean_dec(x_1161);
x_8 = x_1229;
x_9 = x_1230;
goto block_16;
}
}
}
else
{
lean_object* x_1231; lean_object* x_1232; 
lean_dec(x_1149);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1231 = lean_ctor_get(x_1154, 0);
lean_inc(x_1231);
x_1232 = lean_ctor_get(x_1154, 1);
lean_inc(x_1232);
lean_dec(x_1154);
x_8 = x_1231;
x_9 = x_1232;
goto block_16;
}
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1149);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1233 = lean_ctor_get(x_1150, 1);
lean_inc(x_1233);
if (lean_is_exclusive(x_1150)) {
 lean_ctor_release(x_1150, 0);
 lean_ctor_release(x_1150, 1);
 x_1234 = x_1150;
} else {
 lean_dec_ref(x_1150);
 x_1234 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_1145);
if (lean_is_scalar(x_1234)) {
 x_1235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1235 = x_1234;
}
lean_ctor_set(x_1235, 0, x_57);
lean_ctor_set(x_1235, 1, x_1233);
return x_1235;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; 
lean_dec(x_1149);
lean_dec(x_1145);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1236 = lean_ctor_get(x_1150, 0);
lean_inc(x_1236);
x_1237 = lean_ctor_get(x_1150, 1);
lean_inc(x_1237);
lean_dec(x_1150);
x_8 = x_1236;
x_9 = x_1237;
goto block_16;
}
}
else
{
lean_object* x_1238; lean_object* x_1239; 
lean_dec(x_1145);
lean_dec(x_51);
lean_dec(x_1139);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1238 = lean_ctor_get(x_1146, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1146, 1);
lean_inc(x_1239);
lean_dec(x_1146);
x_8 = x_1238;
x_9 = x_1239;
goto block_16;
}
}
else
{
lean_object* x_1240; lean_object* x_1241; 
lean_dec(x_1132);
lean_dec(x_1130);
lean_dec(x_1128);
lean_dec(x_1126);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1240 = lean_ctor_get(x_1133, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1133, 1);
lean_inc(x_1241);
lean_dec(x_1133);
x_8 = x_1240;
x_9 = x_1241;
goto block_16;
}
}
else
{
lean_object* x_1242; lean_object* x_1243; 
lean_dec(x_1128);
lean_dec(x_1126);
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1242 = lean_ctor_get(x_1129, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1129, 1);
lean_inc(x_1243);
lean_dec(x_1129);
x_8 = x_1242;
x_9 = x_1243;
goto block_16;
}
}
else
{
lean_object* x_1244; lean_object* x_1245; 
lean_dec(x_1124);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1244 = lean_ctor_get(x_1125, 0);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1125, 1);
lean_inc(x_1245);
lean_dec(x_1125);
x_8 = x_1244;
x_9 = x_1245;
goto block_16;
}
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_1122);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1246 = lean_ctor_get(x_1121, 1);
lean_inc(x_1246);
if (lean_is_exclusive(x_1121)) {
 lean_ctor_release(x_1121, 0);
 lean_ctor_release(x_1121, 1);
 x_1247 = x_1121;
} else {
 lean_dec_ref(x_1121);
 x_1247 = lean_box(0);
}
if (lean_is_scalar(x_1247)) {
 x_1248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1248 = x_1247;
}
lean_ctor_set(x_1248, 0, x_1120);
lean_ctor_set(x_1248, 1, x_1246);
return x_1248;
}
}
else
{
lean_object* x_1249; lean_object* x_1250; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1249 = lean_ctor_get(x_1121, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1121, 1);
lean_inc(x_1250);
lean_dec(x_1121);
x_8 = x_1249;
x_9 = x_1250;
goto block_16;
}
}
else
{
lean_object* x_1251; lean_object* x_1252; 
lean_dec(x_1107);
lean_dec(x_1105);
lean_free_object(x_100);
lean_dec(x_102);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1251 = lean_ctor_get(x_1108, 0);
lean_inc(x_1251);
x_1252 = lean_ctor_get(x_1108, 1);
lean_inc(x_1252);
lean_dec(x_1108);
x_8 = x_1251;
x_9 = x_1252;
goto block_16;
}
}
else
{
lean_object* x_1253; lean_object* x_1254; 
lean_free_object(x_100);
lean_dec(x_102);
lean_dec(x_99);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1253 = lean_ctor_get(x_1104, 0);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_1104, 1);
lean_inc(x_1254);
lean_dec(x_1104);
x_8 = x_1253;
x_9 = x_1254;
goto block_16;
}
}
}
else
{
lean_object* x_1255; lean_object* x_1256; 
lean_free_object(x_100);
lean_dec(x_102);
lean_dec(x_99);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1255 = lean_ctor_get(x_1096, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1096, 1);
lean_inc(x_1256);
lean_dec(x_1096);
x_8 = x_1255;
x_9 = x_1256;
goto block_16;
}
}
}
else
{
lean_object* x_1257; lean_object* x_1258; 
lean_free_object(x_100);
lean_dec(x_102);
lean_dec(x_99);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1257 = lean_ctor_get(x_104, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_104, 1);
lean_inc(x_1258);
lean_dec(x_104);
x_8 = x_1257;
x_9 = x_1258;
goto block_16;
}
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1259 = lean_ctor_get(x_100, 0);
x_1260 = lean_ctor_get(x_100, 1);
lean_inc(x_1260);
lean_inc(x_1259);
lean_dec(x_100);
x_1261 = l_Lean_Meta_decLevel(x_98, x_3, x_4, x_5, x_6, x_1260);
if (lean_obj_tag(x_1261) == 0)
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; uint8_t x_1265; lean_object* x_1266; 
x_1262 = lean_ctor_get(x_1261, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1261, 1);
lean_inc(x_1263);
if (lean_is_exclusive(x_1261)) {
 lean_ctor_release(x_1261, 0);
 lean_ctor_release(x_1261, 1);
 x_1264 = x_1261;
} else {
 lean_dec_ref(x_1261);
 x_1264 = lean_box(0);
}
x_1265 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1259);
x_1266 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1259, x_1262, x_1265, x_3, x_4, x_5, x_6, x_1263);
if (lean_obj_tag(x_1266) == 0)
{
lean_object* x_1267; uint8_t x_1268; 
x_1267 = lean_ctor_get(x_1266, 0);
lean_inc(x_1267);
x_1268 = lean_unbox(x_1267);
lean_dec(x_1267);
if (x_1268 == 0)
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
lean_dec(x_1264);
lean_dec(x_1259);
lean_dec(x_99);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1269 = lean_ctor_get(x_1266, 1);
lean_inc(x_1269);
if (lean_is_exclusive(x_1266)) {
 lean_ctor_release(x_1266, 0);
 lean_ctor_release(x_1266, 1);
 x_1270 = x_1266;
} else {
 lean_dec_ref(x_1266);
 x_1270 = lean_box(0);
}
x_1271 = lean_box(0);
if (lean_is_scalar(x_1270)) {
 x_1272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1272 = x_1270;
}
lean_ctor_set(x_1272, 0, x_1271);
lean_ctor_set(x_1272, 1, x_1269);
return x_1272;
}
else
{
lean_object* x_1273; lean_object* x_1274; 
x_1273 = lean_ctor_get(x_1266, 1);
lean_inc(x_1273);
lean_dec(x_1266);
x_1274 = l_Lean_Meta_decLevel(x_89, x_3, x_4, x_5, x_6, x_1273);
if (lean_obj_tag(x_1274) == 0)
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1275 = lean_ctor_get(x_1274, 0);
lean_inc(x_1275);
x_1276 = lean_ctor_get(x_1274, 1);
lean_inc(x_1276);
if (lean_is_exclusive(x_1274)) {
 lean_ctor_release(x_1274, 0);
 lean_ctor_release(x_1274, 1);
 x_1277 = x_1274;
} else {
 lean_dec_ref(x_1274);
 x_1277 = lean_box(0);
}
x_1278 = l_Lean_Meta_decLevel(x_99, x_3, x_4, x_5, x_6, x_1276);
if (lean_obj_tag(x_1278) == 0)
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
x_1279 = lean_ctor_get(x_1278, 0);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_1278, 1);
lean_inc(x_1280);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 lean_ctor_release(x_1278, 1);
 x_1281 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1281 = lean_box(0);
}
x_1282 = lean_box(0);
if (lean_is_scalar(x_1281)) {
 x_1283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1283 = x_1281;
 lean_ctor_set_tag(x_1283, 1);
}
lean_ctor_set(x_1283, 0, x_1279);
lean_ctor_set(x_1283, 1, x_1282);
if (lean_is_scalar(x_1277)) {
 x_1284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1284 = x_1277;
 lean_ctor_set_tag(x_1284, 1);
}
lean_ctor_set(x_1284, 0, x_1275);
lean_ctor_set(x_1284, 1, x_1283);
if (lean_is_scalar(x_1264)) {
 x_1285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1285 = x_1264;
 lean_ctor_set_tag(x_1285, 1);
}
lean_ctor_set(x_1285, 0, x_1259);
lean_ctor_set(x_1285, 1, x_1284);
x_1286 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1287 = l_Lean_Expr_const___override(x_1286, x_1285);
lean_inc(x_54);
x_1288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1288, 0, x_54);
lean_ctor_set(x_1288, 1, x_1282);
lean_inc(x_68);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 1, x_1288);
x_1289 = lean_array_mk(x_65);
x_1290 = l_Lean_mkAppN(x_1287, x_1289);
lean_dec(x_1289);
x_1291 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1292 = l_Lean_Meta_trySynthInstance(x_1290, x_1291, x_3, x_4, x_5, x_6, x_1280);
if (lean_obj_tag(x_1292) == 0)
{
lean_object* x_1293; 
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
if (lean_obj_tag(x_1293) == 1)
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1294 = lean_ctor_get(x_1292, 1);
lean_inc(x_1294);
lean_dec(x_1292);
x_1295 = lean_ctor_get(x_1293, 0);
lean_inc(x_1295);
lean_dec(x_1293);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_1296 = l_Lean_Meta_getDecLevel(x_69, x_3, x_4, x_5, x_6, x_1294);
if (lean_obj_tag(x_1296) == 0)
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1300 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_1298);
if (lean_obj_tag(x_1300) == 0)
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; 
x_1301 = lean_ctor_get(x_1300, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1300, 1);
lean_inc(x_1302);
if (lean_is_exclusive(x_1300)) {
 lean_ctor_release(x_1300, 0);
 lean_ctor_release(x_1300, 1);
 x_1303 = x_1300;
} else {
 lean_dec_ref(x_1300);
 x_1303 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_1304 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_1302);
if (lean_obj_tag(x_1304) == 0)
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
x_1305 = lean_ctor_get(x_1304, 0);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1304, 1);
lean_inc(x_1306);
if (lean_is_exclusive(x_1304)) {
 lean_ctor_release(x_1304, 0);
 lean_ctor_release(x_1304, 1);
 x_1307 = x_1304;
} else {
 lean_dec_ref(x_1304);
 x_1307 = lean_box(0);
}
if (lean_is_scalar(x_1307)) {
 x_1308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1308 = x_1307;
 lean_ctor_set_tag(x_1308, 1);
}
lean_ctor_set(x_1308, 0, x_1305);
lean_ctor_set(x_1308, 1, x_1282);
if (lean_is_scalar(x_1303)) {
 x_1309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1309 = x_1303;
 lean_ctor_set_tag(x_1309, 1);
}
lean_ctor_set(x_1309, 0, x_1301);
lean_ctor_set(x_1309, 1, x_1308);
if (lean_is_scalar(x_1299)) {
 x_1310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1310 = x_1299;
 lean_ctor_set_tag(x_1310, 1);
}
lean_ctor_set(x_1310, 0, x_1297);
lean_ctor_set(x_1310, 1, x_1309);
x_1311 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_1310);
x_1312 = l_Lean_Expr_const___override(x_1311, x_1310);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_1282);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_1295);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_1295);
lean_inc(x_54);
x_1313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1313, 0, x_54);
lean_ctor_set(x_1313, 1, x_31);
lean_inc(x_68);
x_1314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1314, 0, x_68);
lean_ctor_set(x_1314, 1, x_1313);
x_1315 = lean_array_mk(x_1314);
x_1316 = l_Lean_mkAppN(x_1312, x_1315);
lean_dec(x_1315);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1316);
x_1317 = lean_infer_type(x_1316, x_3, x_4, x_5, x_6, x_1306);
if (lean_obj_tag(x_1317) == 0)
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
x_1318 = lean_ctor_get(x_1317, 0);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1317, 1);
lean_inc(x_1319);
if (lean_is_exclusive(x_1317)) {
 lean_ctor_release(x_1317, 0);
 lean_ctor_release(x_1317, 1);
 x_1320 = x_1317;
} else {
 lean_dec_ref(x_1317);
 x_1320 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_1321 = l_Lean_Meta_isExprDefEq(x_33, x_1318, x_3, x_4, x_5, x_6, x_1319);
if (lean_obj_tag(x_1321) == 0)
{
lean_object* x_1322; uint8_t x_1323; 
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
x_1323 = lean_unbox(x_1322);
lean_dec(x_1322);
if (x_1323 == 0)
{
lean_object* x_1324; lean_object* x_1325; 
lean_dec(x_1316);
lean_free_object(x_57);
x_1324 = lean_ctor_get(x_1321, 1);
lean_inc(x_1324);
lean_dec(x_1321);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_1325 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_1324);
if (lean_obj_tag(x_1325) == 0)
{
lean_object* x_1326; 
x_1326 = lean_ctor_get(x_1325, 0);
lean_inc(x_1326);
if (lean_obj_tag(x_1326) == 0)
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
lean_dec(x_1320);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1327 = lean_ctor_get(x_1325, 1);
lean_inc(x_1327);
if (lean_is_exclusive(x_1325)) {
 lean_ctor_release(x_1325, 0);
 lean_ctor_release(x_1325, 1);
 x_1328 = x_1325;
} else {
 lean_dec_ref(x_1325);
 x_1328 = lean_box(0);
}
if (lean_is_scalar(x_1328)) {
 x_1329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1329 = x_1328;
}
lean_ctor_set(x_1329, 0, x_1291);
lean_ctor_set(x_1329, 1, x_1327);
return x_1329;
}
else
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
x_1330 = lean_ctor_get(x_1325, 1);
lean_inc(x_1330);
lean_dec(x_1325);
x_1331 = lean_ctor_get(x_1326, 0);
lean_inc(x_1331);
lean_dec(x_1326);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_1332 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_1330);
if (lean_obj_tag(x_1332) == 0)
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1333 = lean_ctor_get(x_1332, 0);
lean_inc(x_1333);
x_1334 = lean_ctor_get(x_1332, 1);
lean_inc(x_1334);
if (lean_is_exclusive(x_1332)) {
 lean_ctor_release(x_1332, 0);
 lean_ctor_release(x_1332, 1);
 x_1335 = x_1332;
} else {
 lean_dec_ref(x_1332);
 x_1335 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1336 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_1334);
if (lean_obj_tag(x_1336) == 0)
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; uint8_t x_1351; lean_object* x_1352; lean_object* x_1353; 
x_1337 = lean_ctor_get(x_1336, 0);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1336, 1);
lean_inc(x_1338);
if (lean_is_exclusive(x_1336)) {
 lean_ctor_release(x_1336, 0);
 lean_ctor_release(x_1336, 1);
 x_1339 = x_1336;
} else {
 lean_dec_ref(x_1336);
 x_1339 = lean_box(0);
}
if (lean_is_scalar(x_1339)) {
 x_1340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1340 = x_1339;
 lean_ctor_set_tag(x_1340, 1);
}
lean_ctor_set(x_1340, 0, x_1337);
lean_ctor_set(x_1340, 1, x_1282);
if (lean_is_scalar(x_1335)) {
 x_1341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1341 = x_1335;
 lean_ctor_set_tag(x_1341, 1);
}
lean_ctor_set(x_1341, 0, x_1333);
lean_ctor_set(x_1341, 1, x_1340);
x_1342 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1343 = l_Lean_Expr_const___override(x_1342, x_1341);
lean_inc(x_55);
if (lean_is_scalar(x_1320)) {
 x_1344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1344 = x_1320;
 lean_ctor_set_tag(x_1344, 1);
}
lean_ctor_set(x_1344, 0, x_55);
lean_ctor_set(x_1344, 1, x_1282);
x_1345 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1346, 0, x_1345);
lean_ctor_set(x_1346, 1, x_1344);
lean_inc(x_69);
x_1347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1347, 0, x_69);
lean_ctor_set(x_1347, 1, x_1346);
x_1348 = lean_array_mk(x_1347);
x_1349 = l_Lean_mkAppN(x_1343, x_1348);
lean_dec(x_1348);
x_1350 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1351 = 0;
lean_inc(x_69);
x_1352 = l_Lean_Expr_forallE___override(x_1350, x_69, x_1349, x_1351);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1353 = l_Lean_Meta_trySynthInstance(x_1352, x_1291, x_3, x_4, x_5, x_6, x_1338);
if (lean_obj_tag(x_1353) == 0)
{
lean_object* x_1354; 
x_1354 = lean_ctor_get(x_1353, 0);
lean_inc(x_1354);
if (lean_obj_tag(x_1354) == 1)
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; 
x_1355 = lean_ctor_get(x_1353, 1);
lean_inc(x_1355);
lean_dec(x_1353);
x_1356 = lean_ctor_get(x_1354, 0);
lean_inc(x_1356);
lean_dec(x_1354);
x_1357 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1358 = l_Lean_Expr_const___override(x_1357, x_1310);
x_1359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1359, 0, x_1331);
lean_ctor_set(x_1359, 1, x_51);
x_1360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1360, 0, x_1356);
lean_ctor_set(x_1360, 1, x_1359);
x_1361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1361, 0, x_1295);
lean_ctor_set(x_1361, 1, x_1360);
x_1362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1362, 0, x_55);
lean_ctor_set(x_1362, 1, x_1361);
x_1363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1363, 0, x_69);
lean_ctor_set(x_1363, 1, x_1362);
x_1364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1364, 0, x_54);
lean_ctor_set(x_1364, 1, x_1363);
x_1365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1365, 0, x_68);
lean_ctor_set(x_1365, 1, x_1364);
x_1366 = lean_array_mk(x_1365);
x_1367 = l_Lean_mkAppN(x_1358, x_1366);
lean_dec(x_1366);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1368 = l_Lean_Meta_expandCoe(x_1367, x_3, x_4, x_5, x_6, x_1355);
if (lean_obj_tag(x_1368) == 0)
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1369 = lean_ctor_get(x_1368, 0);
lean_inc(x_1369);
x_1370 = lean_ctor_get(x_1368, 1);
lean_inc(x_1370);
lean_dec(x_1368);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1369);
x_1371 = lean_infer_type(x_1369, x_3, x_4, x_5, x_6, x_1370);
if (lean_obj_tag(x_1371) == 0)
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1372 = lean_ctor_get(x_1371, 0);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_1371, 1);
lean_inc(x_1373);
lean_dec(x_1371);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1374 = l_Lean_Meta_isExprDefEq(x_33, x_1372, x_3, x_4, x_5, x_6, x_1373);
if (lean_obj_tag(x_1374) == 0)
{
lean_object* x_1375; uint8_t x_1376; 
x_1375 = lean_ctor_get(x_1374, 0);
lean_inc(x_1375);
x_1376 = lean_unbox(x_1375);
lean_dec(x_1375);
if (x_1376 == 0)
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
lean_dec(x_1369);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1377 = lean_ctor_get(x_1374, 1);
lean_inc(x_1377);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1378 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1378 = lean_box(0);
}
if (lean_is_scalar(x_1378)) {
 x_1379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1379 = x_1378;
}
lean_ctor_set(x_1379, 0, x_1291);
lean_ctor_set(x_1379, 1, x_1377);
return x_1379;
}
else
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1380 = lean_ctor_get(x_1374, 1);
lean_inc(x_1380);
lean_dec(x_1374);
x_1381 = lean_box(0);
x_1382 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1369, x_1381, x_3, x_4, x_5, x_6, x_1380);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
if (lean_is_exclusive(x_1382)) {
 lean_ctor_release(x_1382, 0);
 lean_ctor_release(x_1382, 1);
 x_1385 = x_1382;
} else {
 lean_dec_ref(x_1382);
 x_1385 = lean_box(0);
}
if (lean_is_scalar(x_1385)) {
 x_1386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1386 = x_1385;
}
lean_ctor_set(x_1386, 0, x_1383);
lean_ctor_set(x_1386, 1, x_1384);
return x_1386;
}
}
else
{
lean_object* x_1387; lean_object* x_1388; 
lean_dec(x_1369);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1387 = lean_ctor_get(x_1374, 0);
lean_inc(x_1387);
x_1388 = lean_ctor_get(x_1374, 1);
lean_inc(x_1388);
lean_dec(x_1374);
x_8 = x_1387;
x_9 = x_1388;
goto block_16;
}
}
else
{
lean_object* x_1389; lean_object* x_1390; 
lean_dec(x_1369);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1389 = lean_ctor_get(x_1371, 0);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_1371, 1);
lean_inc(x_1390);
lean_dec(x_1371);
x_8 = x_1389;
x_9 = x_1390;
goto block_16;
}
}
else
{
lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1391 = lean_ctor_get(x_1368, 0);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_1368, 1);
lean_inc(x_1392);
lean_dec(x_1368);
x_8 = x_1391;
x_9 = x_1392;
goto block_16;
}
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; 
lean_dec(x_1354);
lean_dec(x_1331);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1393 = lean_ctor_get(x_1353, 1);
lean_inc(x_1393);
if (lean_is_exclusive(x_1353)) {
 lean_ctor_release(x_1353, 0);
 lean_ctor_release(x_1353, 1);
 x_1394 = x_1353;
} else {
 lean_dec_ref(x_1353);
 x_1394 = lean_box(0);
}
if (lean_is_scalar(x_1394)) {
 x_1395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1395 = x_1394;
}
lean_ctor_set(x_1395, 0, x_1291);
lean_ctor_set(x_1395, 1, x_1393);
return x_1395;
}
}
else
{
lean_object* x_1396; lean_object* x_1397; 
lean_dec(x_1331);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1396 = lean_ctor_get(x_1353, 0);
lean_inc(x_1396);
x_1397 = lean_ctor_get(x_1353, 1);
lean_inc(x_1397);
lean_dec(x_1353);
x_8 = x_1396;
x_9 = x_1397;
goto block_16;
}
}
else
{
lean_object* x_1398; lean_object* x_1399; 
lean_dec(x_1335);
lean_dec(x_1333);
lean_dec(x_1331);
lean_dec(x_1320);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1398 = lean_ctor_get(x_1336, 0);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1336, 1);
lean_inc(x_1399);
lean_dec(x_1336);
x_8 = x_1398;
x_9 = x_1399;
goto block_16;
}
}
else
{
lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1331);
lean_dec(x_1320);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1400 = lean_ctor_get(x_1332, 0);
lean_inc(x_1400);
x_1401 = lean_ctor_get(x_1332, 1);
lean_inc(x_1401);
lean_dec(x_1332);
x_8 = x_1400;
x_9 = x_1401;
goto block_16;
}
}
}
else
{
lean_object* x_1402; lean_object* x_1403; 
lean_dec(x_1320);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1402 = lean_ctor_get(x_1325, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1325, 1);
lean_inc(x_1403);
lean_dec(x_1325);
x_8 = x_1402;
x_9 = x_1403;
goto block_16;
}
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
lean_dec(x_1320);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1404 = lean_ctor_get(x_1321, 1);
lean_inc(x_1404);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 lean_ctor_release(x_1321, 1);
 x_1405 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1405 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_1316);
if (lean_is_scalar(x_1405)) {
 x_1406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1406 = x_1405;
}
lean_ctor_set(x_1406, 0, x_57);
lean_ctor_set(x_1406, 1, x_1404);
return x_1406;
}
}
else
{
lean_object* x_1407; lean_object* x_1408; 
lean_dec(x_1320);
lean_dec(x_1316);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1407 = lean_ctor_get(x_1321, 0);
lean_inc(x_1407);
x_1408 = lean_ctor_get(x_1321, 1);
lean_inc(x_1408);
lean_dec(x_1321);
x_8 = x_1407;
x_9 = x_1408;
goto block_16;
}
}
else
{
lean_object* x_1409; lean_object* x_1410; 
lean_dec(x_1316);
lean_dec(x_51);
lean_dec(x_1310);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1409 = lean_ctor_get(x_1317, 0);
lean_inc(x_1409);
x_1410 = lean_ctor_get(x_1317, 1);
lean_inc(x_1410);
lean_dec(x_1317);
x_8 = x_1409;
x_9 = x_1410;
goto block_16;
}
}
else
{
lean_object* x_1411; lean_object* x_1412; 
lean_dec(x_1303);
lean_dec(x_1301);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1411 = lean_ctor_get(x_1304, 0);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1304, 1);
lean_inc(x_1412);
lean_dec(x_1304);
x_8 = x_1411;
x_9 = x_1412;
goto block_16;
}
}
else
{
lean_object* x_1413; lean_object* x_1414; 
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1413 = lean_ctor_get(x_1300, 0);
lean_inc(x_1413);
x_1414 = lean_ctor_get(x_1300, 1);
lean_inc(x_1414);
lean_dec(x_1300);
x_8 = x_1413;
x_9 = x_1414;
goto block_16;
}
}
else
{
lean_object* x_1415; lean_object* x_1416; 
lean_dec(x_1295);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1415 = lean_ctor_get(x_1296, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1296, 1);
lean_inc(x_1416);
lean_dec(x_1296);
x_8 = x_1415;
x_9 = x_1416;
goto block_16;
}
}
else
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
lean_dec(x_1293);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1417 = lean_ctor_get(x_1292, 1);
lean_inc(x_1417);
if (lean_is_exclusive(x_1292)) {
 lean_ctor_release(x_1292, 0);
 lean_ctor_release(x_1292, 1);
 x_1418 = x_1292;
} else {
 lean_dec_ref(x_1292);
 x_1418 = lean_box(0);
}
if (lean_is_scalar(x_1418)) {
 x_1419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1419 = x_1418;
}
lean_ctor_set(x_1419, 0, x_1291);
lean_ctor_set(x_1419, 1, x_1417);
return x_1419;
}
}
else
{
lean_object* x_1420; lean_object* x_1421; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1420 = lean_ctor_get(x_1292, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1292, 1);
lean_inc(x_1421);
lean_dec(x_1292);
x_8 = x_1420;
x_9 = x_1421;
goto block_16;
}
}
else
{
lean_object* x_1422; lean_object* x_1423; 
lean_dec(x_1277);
lean_dec(x_1275);
lean_dec(x_1264);
lean_dec(x_1259);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1422 = lean_ctor_get(x_1278, 0);
lean_inc(x_1422);
x_1423 = lean_ctor_get(x_1278, 1);
lean_inc(x_1423);
lean_dec(x_1278);
x_8 = x_1422;
x_9 = x_1423;
goto block_16;
}
}
else
{
lean_object* x_1424; lean_object* x_1425; 
lean_dec(x_1264);
lean_dec(x_1259);
lean_dec(x_99);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1424 = lean_ctor_get(x_1274, 0);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1274, 1);
lean_inc(x_1425);
lean_dec(x_1274);
x_8 = x_1424;
x_9 = x_1425;
goto block_16;
}
}
}
else
{
lean_object* x_1426; lean_object* x_1427; 
lean_dec(x_1264);
lean_dec(x_1259);
lean_dec(x_99);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1426 = lean_ctor_get(x_1266, 0);
lean_inc(x_1426);
x_1427 = lean_ctor_get(x_1266, 1);
lean_inc(x_1427);
lean_dec(x_1266);
x_8 = x_1426;
x_9 = x_1427;
goto block_16;
}
}
else
{
lean_object* x_1428; lean_object* x_1429; 
lean_dec(x_1259);
lean_dec(x_99);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1428 = lean_ctor_get(x_1261, 0);
lean_inc(x_1428);
x_1429 = lean_ctor_get(x_1261, 1);
lean_inc(x_1429);
lean_dec(x_1261);
x_8 = x_1428;
x_9 = x_1429;
goto block_16;
}
}
}
else
{
lean_object* x_1430; lean_object* x_1431; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_89);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1430 = lean_ctor_get(x_100, 0);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_100, 1);
lean_inc(x_1431);
lean_dec(x_100);
x_8 = x_1430;
x_9 = x_1431;
goto block_16;
}
}
else
{
uint8_t x_1432; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1432 = !lean_is_exclusive(x_93);
if (x_1432 == 0)
{
lean_object* x_1433; lean_object* x_1434; 
x_1433 = lean_ctor_get(x_93, 0);
lean_dec(x_1433);
x_1434 = lean_box(0);
lean_ctor_set(x_93, 0, x_1434);
return x_93;
}
else
{
lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; 
x_1435 = lean_ctor_get(x_93, 1);
lean_inc(x_1435);
lean_dec(x_93);
x_1436 = lean_box(0);
x_1437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1437, 0, x_1436);
lean_ctor_set(x_1437, 1, x_1435);
return x_1437;
}
}
}
else
{
uint8_t x_1438; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1438 = !lean_is_exclusive(x_93);
if (x_1438 == 0)
{
lean_object* x_1439; lean_object* x_1440; 
x_1439 = lean_ctor_get(x_93, 0);
lean_dec(x_1439);
x_1440 = lean_box(0);
lean_ctor_set(x_93, 0, x_1440);
return x_93;
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; 
x_1441 = lean_ctor_get(x_93, 1);
lean_inc(x_1441);
lean_dec(x_93);
x_1442 = lean_box(0);
x_1443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1443, 0, x_1442);
lean_ctor_set(x_1443, 1, x_1441);
return x_1443;
}
}
}
else
{
uint8_t x_1444; 
lean_dec(x_94);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1444 = !lean_is_exclusive(x_93);
if (x_1444 == 0)
{
lean_object* x_1445; lean_object* x_1446; 
x_1445 = lean_ctor_get(x_93, 0);
lean_dec(x_1445);
x_1446 = lean_box(0);
lean_ctor_set(x_93, 0, x_1446);
return x_93;
}
else
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; 
x_1447 = lean_ctor_get(x_93, 1);
lean_inc(x_1447);
lean_dec(x_93);
x_1448 = lean_box(0);
x_1449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1449, 0, x_1448);
lean_ctor_set(x_1449, 1, x_1447);
return x_1449;
}
}
}
else
{
uint8_t x_1450; 
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1450 = !lean_is_exclusive(x_93);
if (x_1450 == 0)
{
lean_object* x_1451; uint8_t x_1452; 
x_1451 = lean_ctor_get(x_93, 0);
x_1452 = l_Lean_Exception_isInterrupt(x_1451);
if (x_1452 == 0)
{
uint8_t x_1453; 
x_1453 = l_Lean_Exception_isRuntime(x_1451);
if (x_1453 == 0)
{
lean_object* x_1454; 
lean_dec(x_1451);
x_1454 = lean_box(0);
lean_ctor_set_tag(x_93, 0);
lean_ctor_set(x_93, 0, x_1454);
return x_93;
}
else
{
return x_93;
}
}
else
{
return x_93;
}
}
else
{
lean_object* x_1455; lean_object* x_1456; uint8_t x_1457; 
x_1455 = lean_ctor_get(x_93, 0);
x_1456 = lean_ctor_get(x_93, 1);
lean_inc(x_1456);
lean_inc(x_1455);
lean_dec(x_93);
x_1457 = l_Lean_Exception_isInterrupt(x_1455);
if (x_1457 == 0)
{
uint8_t x_1458; 
x_1458 = l_Lean_Exception_isRuntime(x_1455);
if (x_1458 == 0)
{
lean_object* x_1459; lean_object* x_1460; 
lean_dec(x_1455);
x_1459 = lean_box(0);
x_1460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1460, 0, x_1459);
lean_ctor_set(x_1460, 1, x_1456);
return x_1460;
}
else
{
lean_object* x_1461; 
x_1461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1461, 0, x_1455);
lean_ctor_set(x_1461, 1, x_1456);
return x_1461;
}
}
else
{
lean_object* x_1462; 
x_1462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1462, 0, x_1455);
lean_ctor_set(x_1462, 1, x_1456);
return x_1462;
}
}
}
}
else
{
uint8_t x_1463; 
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1463 = !lean_is_exclusive(x_90);
if (x_1463 == 0)
{
lean_object* x_1464; uint8_t x_1465; 
x_1464 = lean_ctor_get(x_90, 0);
x_1465 = l_Lean_Exception_isInterrupt(x_1464);
if (x_1465 == 0)
{
uint8_t x_1466; 
x_1466 = l_Lean_Exception_isRuntime(x_1464);
if (x_1466 == 0)
{
lean_object* x_1467; 
lean_dec(x_1464);
x_1467 = lean_box(0);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 0, x_1467);
return x_90;
}
else
{
return x_90;
}
}
else
{
return x_90;
}
}
else
{
lean_object* x_1468; lean_object* x_1469; uint8_t x_1470; 
x_1468 = lean_ctor_get(x_90, 0);
x_1469 = lean_ctor_get(x_90, 1);
lean_inc(x_1469);
lean_inc(x_1468);
lean_dec(x_90);
x_1470 = l_Lean_Exception_isInterrupt(x_1468);
if (x_1470 == 0)
{
uint8_t x_1471; 
x_1471 = l_Lean_Exception_isRuntime(x_1468);
if (x_1471 == 0)
{
lean_object* x_1472; lean_object* x_1473; 
lean_dec(x_1468);
x_1472 = lean_box(0);
x_1473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1473, 0, x_1472);
lean_ctor_set(x_1473, 1, x_1469);
return x_1473;
}
else
{
lean_object* x_1474; 
x_1474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1474, 0, x_1468);
lean_ctor_set(x_1474, 1, x_1469);
return x_1474;
}
}
else
{
lean_object* x_1475; 
x_1475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1475, 0, x_1468);
lean_ctor_set(x_1475, 1, x_1469);
return x_1475;
}
}
}
}
else
{
uint8_t x_1476; 
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1476 = !lean_is_exclusive(x_83);
if (x_1476 == 0)
{
lean_object* x_1477; lean_object* x_1478; 
x_1477 = lean_ctor_get(x_83, 0);
lean_dec(x_1477);
x_1478 = lean_box(0);
lean_ctor_set(x_83, 0, x_1478);
return x_83;
}
else
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; 
x_1479 = lean_ctor_get(x_83, 1);
lean_inc(x_1479);
lean_dec(x_83);
x_1480 = lean_box(0);
x_1481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1481, 0, x_1480);
lean_ctor_set(x_1481, 1, x_1479);
return x_1481;
}
}
}
else
{
uint8_t x_1482; 
lean_dec(x_85);
lean_dec(x_84);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1482 = !lean_is_exclusive(x_83);
if (x_1482 == 0)
{
lean_object* x_1483; lean_object* x_1484; 
x_1483 = lean_ctor_get(x_83, 0);
lean_dec(x_1483);
x_1484 = lean_box(0);
lean_ctor_set(x_83, 0, x_1484);
return x_83;
}
else
{
lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; 
x_1485 = lean_ctor_get(x_83, 1);
lean_inc(x_1485);
lean_dec(x_83);
x_1486 = lean_box(0);
x_1487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1487, 0, x_1486);
lean_ctor_set(x_1487, 1, x_1485);
return x_1487;
}
}
}
else
{
uint8_t x_1488; 
lean_dec(x_84);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1488 = !lean_is_exclusive(x_83);
if (x_1488 == 0)
{
lean_object* x_1489; lean_object* x_1490; 
x_1489 = lean_ctor_get(x_83, 0);
lean_dec(x_1489);
x_1490 = lean_box(0);
lean_ctor_set(x_83, 0, x_1490);
return x_83;
}
else
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
x_1491 = lean_ctor_get(x_83, 1);
lean_inc(x_1491);
lean_dec(x_83);
x_1492 = lean_box(0);
x_1493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1493, 0, x_1492);
lean_ctor_set(x_1493, 1, x_1491);
return x_1493;
}
}
}
else
{
uint8_t x_1494; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1494 = !lean_is_exclusive(x_83);
if (x_1494 == 0)
{
lean_object* x_1495; uint8_t x_1496; 
x_1495 = lean_ctor_get(x_83, 0);
x_1496 = l_Lean_Exception_isInterrupt(x_1495);
if (x_1496 == 0)
{
uint8_t x_1497; 
x_1497 = l_Lean_Exception_isRuntime(x_1495);
if (x_1497 == 0)
{
lean_object* x_1498; 
lean_dec(x_1495);
x_1498 = lean_box(0);
lean_ctor_set_tag(x_83, 0);
lean_ctor_set(x_83, 0, x_1498);
return x_83;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
else
{
lean_object* x_1499; lean_object* x_1500; uint8_t x_1501; 
x_1499 = lean_ctor_get(x_83, 0);
x_1500 = lean_ctor_get(x_83, 1);
lean_inc(x_1500);
lean_inc(x_1499);
lean_dec(x_83);
x_1501 = l_Lean_Exception_isInterrupt(x_1499);
if (x_1501 == 0)
{
uint8_t x_1502; 
x_1502 = l_Lean_Exception_isRuntime(x_1499);
if (x_1502 == 0)
{
lean_object* x_1503; lean_object* x_1504; 
lean_dec(x_1499);
x_1503 = lean_box(0);
x_1504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1504, 0, x_1503);
lean_ctor_set(x_1504, 1, x_1500);
return x_1504;
}
else
{
lean_object* x_1505; 
x_1505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1505, 0, x_1499);
lean_ctor_set(x_1505, 1, x_1500);
return x_1505;
}
}
else
{
lean_object* x_1506; 
x_1506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1506, 0, x_1499);
lean_ctor_set(x_1506, 1, x_1500);
return x_1506;
}
}
}
}
else
{
uint8_t x_1507; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1507 = !lean_is_exclusive(x_80);
if (x_1507 == 0)
{
lean_object* x_1508; uint8_t x_1509; 
x_1508 = lean_ctor_get(x_80, 0);
x_1509 = l_Lean_Exception_isInterrupt(x_1508);
if (x_1509 == 0)
{
uint8_t x_1510; 
x_1510 = l_Lean_Exception_isRuntime(x_1508);
if (x_1510 == 0)
{
lean_object* x_1511; 
lean_dec(x_1508);
x_1511 = lean_box(0);
lean_ctor_set_tag(x_80, 0);
lean_ctor_set(x_80, 0, x_1511);
return x_80;
}
else
{
return x_80;
}
}
else
{
return x_80;
}
}
else
{
lean_object* x_1512; lean_object* x_1513; uint8_t x_1514; 
x_1512 = lean_ctor_get(x_80, 0);
x_1513 = lean_ctor_get(x_80, 1);
lean_inc(x_1513);
lean_inc(x_1512);
lean_dec(x_80);
x_1514 = l_Lean_Exception_isInterrupt(x_1512);
if (x_1514 == 0)
{
uint8_t x_1515; 
x_1515 = l_Lean_Exception_isRuntime(x_1512);
if (x_1515 == 0)
{
lean_object* x_1516; lean_object* x_1517; 
lean_dec(x_1512);
x_1516 = lean_box(0);
x_1517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1517, 0, x_1516);
lean_ctor_set(x_1517, 1, x_1513);
return x_1517;
}
else
{
lean_object* x_1518; 
x_1518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1518, 0, x_1512);
lean_ctor_set(x_1518, 1, x_1513);
return x_1518;
}
}
else
{
lean_object* x_1519; 
x_1519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1519, 0, x_1512);
lean_ctor_set(x_1519, 1, x_1513);
return x_1519;
}
}
}
}
}
else
{
lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; uint8_t x_1523; 
x_1520 = lean_ctor_get(x_70, 1);
lean_inc(x_1520);
lean_dec(x_70);
x_1521 = lean_ctor_get(x_5, 2);
lean_inc(x_1521);
x_1522 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1523 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1521, x_1522);
lean_dec(x_1521);
if (x_1523 == 0)
{
lean_object* x_1524; lean_object* x_1525; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1524 = lean_box(0);
x_1525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1525, 0, x_1524);
lean_ctor_set(x_1525, 1, x_1520);
return x_1525;
}
else
{
lean_object* x_1526; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_68);
x_1526 = lean_infer_type(x_68, x_3, x_4, x_5, x_6, x_1520);
if (lean_obj_tag(x_1526) == 0)
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; 
x_1527 = lean_ctor_get(x_1526, 0);
lean_inc(x_1527);
x_1528 = lean_ctor_get(x_1526, 1);
lean_inc(x_1528);
lean_dec(x_1526);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1529 = lean_whnf(x_1527, x_3, x_4, x_5, x_6, x_1528);
if (lean_obj_tag(x_1529) == 0)
{
lean_object* x_1530; 
x_1530 = lean_ctor_get(x_1529, 0);
lean_inc(x_1530);
if (lean_obj_tag(x_1530) == 7)
{
lean_object* x_1531; 
x_1531 = lean_ctor_get(x_1530, 1);
lean_inc(x_1531);
if (lean_obj_tag(x_1531) == 3)
{
lean_object* x_1532; 
x_1532 = lean_ctor_get(x_1530, 2);
lean_inc(x_1532);
lean_dec(x_1530);
if (lean_obj_tag(x_1532) == 3)
{
lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; 
x_1533 = lean_ctor_get(x_1529, 1);
lean_inc(x_1533);
lean_dec(x_1529);
x_1534 = lean_ctor_get(x_1531, 0);
lean_inc(x_1534);
lean_dec(x_1531);
x_1535 = lean_ctor_get(x_1532, 0);
lean_inc(x_1535);
lean_dec(x_1532);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_1536 = lean_infer_type(x_54, x_3, x_4, x_5, x_6, x_1533);
if (lean_obj_tag(x_1536) == 0)
{
lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; 
x_1537 = lean_ctor_get(x_1536, 0);
lean_inc(x_1537);
x_1538 = lean_ctor_get(x_1536, 1);
lean_inc(x_1538);
lean_dec(x_1536);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1539 = lean_whnf(x_1537, x_3, x_4, x_5, x_6, x_1538);
if (lean_obj_tag(x_1539) == 0)
{
lean_object* x_1540; 
x_1540 = lean_ctor_get(x_1539, 0);
lean_inc(x_1540);
if (lean_obj_tag(x_1540) == 7)
{
lean_object* x_1541; 
x_1541 = lean_ctor_get(x_1540, 1);
lean_inc(x_1541);
if (lean_obj_tag(x_1541) == 3)
{
lean_object* x_1542; 
x_1542 = lean_ctor_get(x_1540, 2);
lean_inc(x_1542);
lean_dec(x_1540);
if (lean_obj_tag(x_1542) == 3)
{
lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
x_1543 = lean_ctor_get(x_1539, 1);
lean_inc(x_1543);
lean_dec(x_1539);
x_1544 = lean_ctor_get(x_1541, 0);
lean_inc(x_1544);
lean_dec(x_1541);
x_1545 = lean_ctor_get(x_1542, 0);
lean_inc(x_1545);
lean_dec(x_1542);
x_1546 = l_Lean_Meta_decLevel(x_1534, x_3, x_4, x_5, x_6, x_1543);
if (lean_obj_tag(x_1546) == 0)
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
x_1547 = lean_ctor_get(x_1546, 0);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1546, 1);
lean_inc(x_1548);
if (lean_is_exclusive(x_1546)) {
 lean_ctor_release(x_1546, 0);
 lean_ctor_release(x_1546, 1);
 x_1549 = x_1546;
} else {
 lean_dec_ref(x_1546);
 x_1549 = lean_box(0);
}
x_1550 = l_Lean_Meta_decLevel(x_1544, x_3, x_4, x_5, x_6, x_1548);
if (lean_obj_tag(x_1550) == 0)
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; uint8_t x_1554; lean_object* x_1555; 
x_1551 = lean_ctor_get(x_1550, 0);
lean_inc(x_1551);
x_1552 = lean_ctor_get(x_1550, 1);
lean_inc(x_1552);
if (lean_is_exclusive(x_1550)) {
 lean_ctor_release(x_1550, 0);
 lean_ctor_release(x_1550, 1);
 x_1553 = x_1550;
} else {
 lean_dec_ref(x_1550);
 x_1553 = lean_box(0);
}
x_1554 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1547);
x_1555 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1547, x_1551, x_1554, x_3, x_4, x_5, x_6, x_1552);
if (lean_obj_tag(x_1555) == 0)
{
lean_object* x_1556; uint8_t x_1557; 
x_1556 = lean_ctor_get(x_1555, 0);
lean_inc(x_1556);
x_1557 = lean_unbox(x_1556);
lean_dec(x_1556);
if (x_1557 == 0)
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
lean_dec(x_1553);
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1545);
lean_dec(x_1535);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1558 = lean_ctor_get(x_1555, 1);
lean_inc(x_1558);
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 lean_ctor_release(x_1555, 1);
 x_1559 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1559 = lean_box(0);
}
x_1560 = lean_box(0);
if (lean_is_scalar(x_1559)) {
 x_1561 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1561 = x_1559;
}
lean_ctor_set(x_1561, 0, x_1560);
lean_ctor_set(x_1561, 1, x_1558);
return x_1561;
}
else
{
lean_object* x_1562; lean_object* x_1563; 
x_1562 = lean_ctor_get(x_1555, 1);
lean_inc(x_1562);
lean_dec(x_1555);
x_1563 = l_Lean_Meta_decLevel(x_1535, x_3, x_4, x_5, x_6, x_1562);
if (lean_obj_tag(x_1563) == 0)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; 
x_1564 = lean_ctor_get(x_1563, 0);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1563, 1);
lean_inc(x_1565);
if (lean_is_exclusive(x_1563)) {
 lean_ctor_release(x_1563, 0);
 lean_ctor_release(x_1563, 1);
 x_1566 = x_1563;
} else {
 lean_dec_ref(x_1563);
 x_1566 = lean_box(0);
}
x_1567 = l_Lean_Meta_decLevel(x_1545, x_3, x_4, x_5, x_6, x_1565);
if (lean_obj_tag(x_1567) == 0)
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
x_1568 = lean_ctor_get(x_1567, 0);
lean_inc(x_1568);
x_1569 = lean_ctor_get(x_1567, 1);
lean_inc(x_1569);
if (lean_is_exclusive(x_1567)) {
 lean_ctor_release(x_1567, 0);
 lean_ctor_release(x_1567, 1);
 x_1570 = x_1567;
} else {
 lean_dec_ref(x_1567);
 x_1570 = lean_box(0);
}
x_1571 = lean_box(0);
if (lean_is_scalar(x_1570)) {
 x_1572 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1572 = x_1570;
 lean_ctor_set_tag(x_1572, 1);
}
lean_ctor_set(x_1572, 0, x_1568);
lean_ctor_set(x_1572, 1, x_1571);
if (lean_is_scalar(x_1566)) {
 x_1573 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1573 = x_1566;
 lean_ctor_set_tag(x_1573, 1);
}
lean_ctor_set(x_1573, 0, x_1564);
lean_ctor_set(x_1573, 1, x_1572);
if (lean_is_scalar(x_1553)) {
 x_1574 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1574 = x_1553;
 lean_ctor_set_tag(x_1574, 1);
}
lean_ctor_set(x_1574, 0, x_1547);
lean_ctor_set(x_1574, 1, x_1573);
x_1575 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1576 = l_Lean_Expr_const___override(x_1575, x_1574);
lean_inc(x_54);
if (lean_is_scalar(x_1549)) {
 x_1577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1577 = x_1549;
 lean_ctor_set_tag(x_1577, 1);
}
lean_ctor_set(x_1577, 0, x_54);
lean_ctor_set(x_1577, 1, x_1571);
lean_inc(x_68);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 1, x_1577);
x_1578 = lean_array_mk(x_65);
x_1579 = l_Lean_mkAppN(x_1576, x_1578);
lean_dec(x_1578);
x_1580 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1581 = l_Lean_Meta_trySynthInstance(x_1579, x_1580, x_3, x_4, x_5, x_6, x_1569);
if (lean_obj_tag(x_1581) == 0)
{
lean_object* x_1582; 
x_1582 = lean_ctor_get(x_1581, 0);
lean_inc(x_1582);
if (lean_obj_tag(x_1582) == 1)
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; 
x_1583 = lean_ctor_get(x_1581, 1);
lean_inc(x_1583);
lean_dec(x_1581);
x_1584 = lean_ctor_get(x_1582, 0);
lean_inc(x_1584);
lean_dec(x_1582);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_1585 = l_Lean_Meta_getDecLevel(x_69, x_3, x_4, x_5, x_6, x_1583);
if (lean_obj_tag(x_1585) == 0)
{
lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; 
x_1586 = lean_ctor_get(x_1585, 0);
lean_inc(x_1586);
x_1587 = lean_ctor_get(x_1585, 1);
lean_inc(x_1587);
if (lean_is_exclusive(x_1585)) {
 lean_ctor_release(x_1585, 0);
 lean_ctor_release(x_1585, 1);
 x_1588 = x_1585;
} else {
 lean_dec_ref(x_1585);
 x_1588 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1589 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_1587);
if (lean_obj_tag(x_1589) == 0)
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; 
x_1590 = lean_ctor_get(x_1589, 0);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1589, 1);
lean_inc(x_1591);
if (lean_is_exclusive(x_1589)) {
 lean_ctor_release(x_1589, 0);
 lean_ctor_release(x_1589, 1);
 x_1592 = x_1589;
} else {
 lean_dec_ref(x_1589);
 x_1592 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_1593 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_1591);
if (lean_obj_tag(x_1593) == 0)
{
lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
x_1594 = lean_ctor_get(x_1593, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1593, 1);
lean_inc(x_1595);
if (lean_is_exclusive(x_1593)) {
 lean_ctor_release(x_1593, 0);
 lean_ctor_release(x_1593, 1);
 x_1596 = x_1593;
} else {
 lean_dec_ref(x_1593);
 x_1596 = lean_box(0);
}
if (lean_is_scalar(x_1596)) {
 x_1597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1597 = x_1596;
 lean_ctor_set_tag(x_1597, 1);
}
lean_ctor_set(x_1597, 0, x_1594);
lean_ctor_set(x_1597, 1, x_1571);
if (lean_is_scalar(x_1592)) {
 x_1598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1598 = x_1592;
 lean_ctor_set_tag(x_1598, 1);
}
lean_ctor_set(x_1598, 0, x_1590);
lean_ctor_set(x_1598, 1, x_1597);
if (lean_is_scalar(x_1588)) {
 x_1599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1599 = x_1588;
 lean_ctor_set_tag(x_1599, 1);
}
lean_ctor_set(x_1599, 0, x_1586);
lean_ctor_set(x_1599, 1, x_1598);
x_1600 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_1599);
x_1601 = l_Lean_Expr_const___override(x_1600, x_1599);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_1571);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_69);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_69);
lean_inc(x_1584);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_1584);
lean_inc(x_54);
x_1602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1602, 0, x_54);
lean_ctor_set(x_1602, 1, x_31);
lean_inc(x_68);
x_1603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1603, 0, x_68);
lean_ctor_set(x_1603, 1, x_1602);
x_1604 = lean_array_mk(x_1603);
x_1605 = l_Lean_mkAppN(x_1601, x_1604);
lean_dec(x_1604);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1605);
x_1606 = lean_infer_type(x_1605, x_3, x_4, x_5, x_6, x_1595);
if (lean_obj_tag(x_1606) == 0)
{
lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; 
x_1607 = lean_ctor_get(x_1606, 0);
lean_inc(x_1607);
x_1608 = lean_ctor_get(x_1606, 1);
lean_inc(x_1608);
if (lean_is_exclusive(x_1606)) {
 lean_ctor_release(x_1606, 0);
 lean_ctor_release(x_1606, 1);
 x_1609 = x_1606;
} else {
 lean_dec_ref(x_1606);
 x_1609 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_1610 = l_Lean_Meta_isExprDefEq(x_33, x_1607, x_3, x_4, x_5, x_6, x_1608);
if (lean_obj_tag(x_1610) == 0)
{
lean_object* x_1611; uint8_t x_1612; 
x_1611 = lean_ctor_get(x_1610, 0);
lean_inc(x_1611);
x_1612 = lean_unbox(x_1611);
lean_dec(x_1611);
if (x_1612 == 0)
{
lean_object* x_1613; lean_object* x_1614; 
lean_dec(x_1605);
lean_free_object(x_57);
x_1613 = lean_ctor_get(x_1610, 1);
lean_inc(x_1613);
lean_dec(x_1610);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_1614 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_1613);
if (lean_obj_tag(x_1614) == 0)
{
lean_object* x_1615; 
x_1615 = lean_ctor_get(x_1614, 0);
lean_inc(x_1615);
if (lean_obj_tag(x_1615) == 0)
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; 
lean_dec(x_1609);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1616 = lean_ctor_get(x_1614, 1);
lean_inc(x_1616);
if (lean_is_exclusive(x_1614)) {
 lean_ctor_release(x_1614, 0);
 lean_ctor_release(x_1614, 1);
 x_1617 = x_1614;
} else {
 lean_dec_ref(x_1614);
 x_1617 = lean_box(0);
}
if (lean_is_scalar(x_1617)) {
 x_1618 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1618 = x_1617;
}
lean_ctor_set(x_1618, 0, x_1580);
lean_ctor_set(x_1618, 1, x_1616);
return x_1618;
}
else
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1619 = lean_ctor_get(x_1614, 1);
lean_inc(x_1619);
lean_dec(x_1614);
x_1620 = lean_ctor_get(x_1615, 0);
lean_inc(x_1620);
lean_dec(x_1615);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_69);
x_1621 = l_Lean_Meta_getLevel(x_69, x_3, x_4, x_5, x_6, x_1619);
if (lean_obj_tag(x_1621) == 0)
{
lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; 
x_1622 = lean_ctor_get(x_1621, 0);
lean_inc(x_1622);
x_1623 = lean_ctor_get(x_1621, 1);
lean_inc(x_1623);
if (lean_is_exclusive(x_1621)) {
 lean_ctor_release(x_1621, 0);
 lean_ctor_release(x_1621, 1);
 x_1624 = x_1621;
} else {
 lean_dec_ref(x_1621);
 x_1624 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1625 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_1623);
if (lean_obj_tag(x_1625) == 0)
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; uint8_t x_1640; lean_object* x_1641; lean_object* x_1642; 
x_1626 = lean_ctor_get(x_1625, 0);
lean_inc(x_1626);
x_1627 = lean_ctor_get(x_1625, 1);
lean_inc(x_1627);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1628 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1628 = lean_box(0);
}
if (lean_is_scalar(x_1628)) {
 x_1629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1629 = x_1628;
 lean_ctor_set_tag(x_1629, 1);
}
lean_ctor_set(x_1629, 0, x_1626);
lean_ctor_set(x_1629, 1, x_1571);
if (lean_is_scalar(x_1624)) {
 x_1630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1630 = x_1624;
 lean_ctor_set_tag(x_1630, 1);
}
lean_ctor_set(x_1630, 0, x_1622);
lean_ctor_set(x_1630, 1, x_1629);
x_1631 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1632 = l_Lean_Expr_const___override(x_1631, x_1630);
lean_inc(x_55);
if (lean_is_scalar(x_1609)) {
 x_1633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1633 = x_1609;
 lean_ctor_set_tag(x_1633, 1);
}
lean_ctor_set(x_1633, 0, x_55);
lean_ctor_set(x_1633, 1, x_1571);
x_1634 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1635, 0, x_1634);
lean_ctor_set(x_1635, 1, x_1633);
lean_inc(x_69);
x_1636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1636, 0, x_69);
lean_ctor_set(x_1636, 1, x_1635);
x_1637 = lean_array_mk(x_1636);
x_1638 = l_Lean_mkAppN(x_1632, x_1637);
lean_dec(x_1637);
x_1639 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1640 = 0;
lean_inc(x_69);
x_1641 = l_Lean_Expr_forallE___override(x_1639, x_69, x_1638, x_1640);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1642 = l_Lean_Meta_trySynthInstance(x_1641, x_1580, x_3, x_4, x_5, x_6, x_1627);
if (lean_obj_tag(x_1642) == 0)
{
lean_object* x_1643; 
x_1643 = lean_ctor_get(x_1642, 0);
lean_inc(x_1643);
if (lean_obj_tag(x_1643) == 1)
{
lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
x_1644 = lean_ctor_get(x_1642, 1);
lean_inc(x_1644);
lean_dec(x_1642);
x_1645 = lean_ctor_get(x_1643, 0);
lean_inc(x_1645);
lean_dec(x_1643);
x_1646 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1647 = l_Lean_Expr_const___override(x_1646, x_1599);
x_1648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1648, 0, x_1620);
lean_ctor_set(x_1648, 1, x_51);
x_1649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1649, 0, x_1645);
lean_ctor_set(x_1649, 1, x_1648);
x_1650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1650, 0, x_1584);
lean_ctor_set(x_1650, 1, x_1649);
x_1651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1651, 0, x_55);
lean_ctor_set(x_1651, 1, x_1650);
x_1652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1652, 0, x_69);
lean_ctor_set(x_1652, 1, x_1651);
x_1653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1653, 0, x_54);
lean_ctor_set(x_1653, 1, x_1652);
x_1654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1654, 0, x_68);
lean_ctor_set(x_1654, 1, x_1653);
x_1655 = lean_array_mk(x_1654);
x_1656 = l_Lean_mkAppN(x_1647, x_1655);
lean_dec(x_1655);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1657 = l_Lean_Meta_expandCoe(x_1656, x_3, x_4, x_5, x_6, x_1644);
if (lean_obj_tag(x_1657) == 0)
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; 
x_1658 = lean_ctor_get(x_1657, 0);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1657, 1);
lean_inc(x_1659);
lean_dec(x_1657);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1658);
x_1660 = lean_infer_type(x_1658, x_3, x_4, x_5, x_6, x_1659);
if (lean_obj_tag(x_1660) == 0)
{
lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; 
x_1661 = lean_ctor_get(x_1660, 0);
lean_inc(x_1661);
x_1662 = lean_ctor_get(x_1660, 1);
lean_inc(x_1662);
lean_dec(x_1660);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1663 = l_Lean_Meta_isExprDefEq(x_33, x_1661, x_3, x_4, x_5, x_6, x_1662);
if (lean_obj_tag(x_1663) == 0)
{
lean_object* x_1664; uint8_t x_1665; 
x_1664 = lean_ctor_get(x_1663, 0);
lean_inc(x_1664);
x_1665 = lean_unbox(x_1664);
lean_dec(x_1664);
if (x_1665 == 0)
{
lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; 
lean_dec(x_1658);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1666 = lean_ctor_get(x_1663, 1);
lean_inc(x_1666);
if (lean_is_exclusive(x_1663)) {
 lean_ctor_release(x_1663, 0);
 lean_ctor_release(x_1663, 1);
 x_1667 = x_1663;
} else {
 lean_dec_ref(x_1663);
 x_1667 = lean_box(0);
}
if (lean_is_scalar(x_1667)) {
 x_1668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1668 = x_1667;
}
lean_ctor_set(x_1668, 0, x_1580);
lean_ctor_set(x_1668, 1, x_1666);
return x_1668;
}
else
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; 
x_1669 = lean_ctor_get(x_1663, 1);
lean_inc(x_1669);
lean_dec(x_1663);
x_1670 = lean_box(0);
x_1671 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1658, x_1670, x_3, x_4, x_5, x_6, x_1669);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1672 = lean_ctor_get(x_1671, 0);
lean_inc(x_1672);
x_1673 = lean_ctor_get(x_1671, 1);
lean_inc(x_1673);
if (lean_is_exclusive(x_1671)) {
 lean_ctor_release(x_1671, 0);
 lean_ctor_release(x_1671, 1);
 x_1674 = x_1671;
} else {
 lean_dec_ref(x_1671);
 x_1674 = lean_box(0);
}
if (lean_is_scalar(x_1674)) {
 x_1675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1675 = x_1674;
}
lean_ctor_set(x_1675, 0, x_1672);
lean_ctor_set(x_1675, 1, x_1673);
return x_1675;
}
}
else
{
lean_object* x_1676; lean_object* x_1677; 
lean_dec(x_1658);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1676 = lean_ctor_get(x_1663, 0);
lean_inc(x_1676);
x_1677 = lean_ctor_get(x_1663, 1);
lean_inc(x_1677);
lean_dec(x_1663);
x_8 = x_1676;
x_9 = x_1677;
goto block_16;
}
}
else
{
lean_object* x_1678; lean_object* x_1679; 
lean_dec(x_1658);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1678 = lean_ctor_get(x_1660, 0);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_1660, 1);
lean_inc(x_1679);
lean_dec(x_1660);
x_8 = x_1678;
x_9 = x_1679;
goto block_16;
}
}
else
{
lean_object* x_1680; lean_object* x_1681; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1680 = lean_ctor_get(x_1657, 0);
lean_inc(x_1680);
x_1681 = lean_ctor_get(x_1657, 1);
lean_inc(x_1681);
lean_dec(x_1657);
x_8 = x_1680;
x_9 = x_1681;
goto block_16;
}
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; 
lean_dec(x_1643);
lean_dec(x_1620);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1682 = lean_ctor_get(x_1642, 1);
lean_inc(x_1682);
if (lean_is_exclusive(x_1642)) {
 lean_ctor_release(x_1642, 0);
 lean_ctor_release(x_1642, 1);
 x_1683 = x_1642;
} else {
 lean_dec_ref(x_1642);
 x_1683 = lean_box(0);
}
if (lean_is_scalar(x_1683)) {
 x_1684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1684 = x_1683;
}
lean_ctor_set(x_1684, 0, x_1580);
lean_ctor_set(x_1684, 1, x_1682);
return x_1684;
}
}
else
{
lean_object* x_1685; lean_object* x_1686; 
lean_dec(x_1620);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1685 = lean_ctor_get(x_1642, 0);
lean_inc(x_1685);
x_1686 = lean_ctor_get(x_1642, 1);
lean_inc(x_1686);
lean_dec(x_1642);
x_8 = x_1685;
x_9 = x_1686;
goto block_16;
}
}
else
{
lean_object* x_1687; lean_object* x_1688; 
lean_dec(x_1624);
lean_dec(x_1622);
lean_dec(x_1620);
lean_dec(x_1609);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1687 = lean_ctor_get(x_1625, 0);
lean_inc(x_1687);
x_1688 = lean_ctor_get(x_1625, 1);
lean_inc(x_1688);
lean_dec(x_1625);
x_8 = x_1687;
x_9 = x_1688;
goto block_16;
}
}
else
{
lean_object* x_1689; lean_object* x_1690; 
lean_dec(x_1620);
lean_dec(x_1609);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1689 = lean_ctor_get(x_1621, 0);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1621, 1);
lean_inc(x_1690);
lean_dec(x_1621);
x_8 = x_1689;
x_9 = x_1690;
goto block_16;
}
}
}
else
{
lean_object* x_1691; lean_object* x_1692; 
lean_dec(x_1609);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1691 = lean_ctor_get(x_1614, 0);
lean_inc(x_1691);
x_1692 = lean_ctor_get(x_1614, 1);
lean_inc(x_1692);
lean_dec(x_1614);
x_8 = x_1691;
x_9 = x_1692;
goto block_16;
}
}
else
{
lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; 
lean_dec(x_1609);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1693 = lean_ctor_get(x_1610, 1);
lean_inc(x_1693);
if (lean_is_exclusive(x_1610)) {
 lean_ctor_release(x_1610, 0);
 lean_ctor_release(x_1610, 1);
 x_1694 = x_1610;
} else {
 lean_dec_ref(x_1610);
 x_1694 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_1605);
if (lean_is_scalar(x_1694)) {
 x_1695 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1695 = x_1694;
}
lean_ctor_set(x_1695, 0, x_57);
lean_ctor_set(x_1695, 1, x_1693);
return x_1695;
}
}
else
{
lean_object* x_1696; lean_object* x_1697; 
lean_dec(x_1609);
lean_dec(x_1605);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1696 = lean_ctor_get(x_1610, 0);
lean_inc(x_1696);
x_1697 = lean_ctor_get(x_1610, 1);
lean_inc(x_1697);
lean_dec(x_1610);
x_8 = x_1696;
x_9 = x_1697;
goto block_16;
}
}
else
{
lean_object* x_1698; lean_object* x_1699; 
lean_dec(x_1605);
lean_dec(x_51);
lean_dec(x_1599);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1698 = lean_ctor_get(x_1606, 0);
lean_inc(x_1698);
x_1699 = lean_ctor_get(x_1606, 1);
lean_inc(x_1699);
lean_dec(x_1606);
x_8 = x_1698;
x_9 = x_1699;
goto block_16;
}
}
else
{
lean_object* x_1700; lean_object* x_1701; 
lean_dec(x_1592);
lean_dec(x_1590);
lean_dec(x_1588);
lean_dec(x_1586);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1700 = lean_ctor_get(x_1593, 0);
lean_inc(x_1700);
x_1701 = lean_ctor_get(x_1593, 1);
lean_inc(x_1701);
lean_dec(x_1593);
x_8 = x_1700;
x_9 = x_1701;
goto block_16;
}
}
else
{
lean_object* x_1702; lean_object* x_1703; 
lean_dec(x_1588);
lean_dec(x_1586);
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1702 = lean_ctor_get(x_1589, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1589, 1);
lean_inc(x_1703);
lean_dec(x_1589);
x_8 = x_1702;
x_9 = x_1703;
goto block_16;
}
}
else
{
lean_object* x_1704; lean_object* x_1705; 
lean_dec(x_1584);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1704 = lean_ctor_get(x_1585, 0);
lean_inc(x_1704);
x_1705 = lean_ctor_get(x_1585, 1);
lean_inc(x_1705);
lean_dec(x_1585);
x_8 = x_1704;
x_9 = x_1705;
goto block_16;
}
}
else
{
lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; 
lean_dec(x_1582);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1706 = lean_ctor_get(x_1581, 1);
lean_inc(x_1706);
if (lean_is_exclusive(x_1581)) {
 lean_ctor_release(x_1581, 0);
 lean_ctor_release(x_1581, 1);
 x_1707 = x_1581;
} else {
 lean_dec_ref(x_1581);
 x_1707 = lean_box(0);
}
if (lean_is_scalar(x_1707)) {
 x_1708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1708 = x_1707;
}
lean_ctor_set(x_1708, 0, x_1580);
lean_ctor_set(x_1708, 1, x_1706);
return x_1708;
}
}
else
{
lean_object* x_1709; lean_object* x_1710; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1709 = lean_ctor_get(x_1581, 0);
lean_inc(x_1709);
x_1710 = lean_ctor_get(x_1581, 1);
lean_inc(x_1710);
lean_dec(x_1581);
x_8 = x_1709;
x_9 = x_1710;
goto block_16;
}
}
else
{
lean_object* x_1711; lean_object* x_1712; 
lean_dec(x_1566);
lean_dec(x_1564);
lean_dec(x_1553);
lean_dec(x_1549);
lean_dec(x_1547);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1711 = lean_ctor_get(x_1567, 0);
lean_inc(x_1711);
x_1712 = lean_ctor_get(x_1567, 1);
lean_inc(x_1712);
lean_dec(x_1567);
x_8 = x_1711;
x_9 = x_1712;
goto block_16;
}
}
else
{
lean_object* x_1713; lean_object* x_1714; 
lean_dec(x_1553);
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1545);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1713 = lean_ctor_get(x_1563, 0);
lean_inc(x_1713);
x_1714 = lean_ctor_get(x_1563, 1);
lean_inc(x_1714);
lean_dec(x_1563);
x_8 = x_1713;
x_9 = x_1714;
goto block_16;
}
}
}
else
{
lean_object* x_1715; lean_object* x_1716; 
lean_dec(x_1553);
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1545);
lean_dec(x_1535);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1715 = lean_ctor_get(x_1555, 0);
lean_inc(x_1715);
x_1716 = lean_ctor_get(x_1555, 1);
lean_inc(x_1716);
lean_dec(x_1555);
x_8 = x_1715;
x_9 = x_1716;
goto block_16;
}
}
else
{
lean_object* x_1717; lean_object* x_1718; 
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1545);
lean_dec(x_1535);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1717 = lean_ctor_get(x_1550, 0);
lean_inc(x_1717);
x_1718 = lean_ctor_get(x_1550, 1);
lean_inc(x_1718);
lean_dec(x_1550);
x_8 = x_1717;
x_9 = x_1718;
goto block_16;
}
}
else
{
lean_object* x_1719; lean_object* x_1720; 
lean_dec(x_1545);
lean_dec(x_1544);
lean_dec(x_1535);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1719 = lean_ctor_get(x_1546, 0);
lean_inc(x_1719);
x_1720 = lean_ctor_get(x_1546, 1);
lean_inc(x_1720);
lean_dec(x_1546);
x_8 = x_1719;
x_9 = x_1720;
goto block_16;
}
}
else
{
lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; 
lean_dec(x_1542);
lean_dec(x_1541);
lean_dec(x_1535);
lean_dec(x_1534);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1721 = lean_ctor_get(x_1539, 1);
lean_inc(x_1721);
if (lean_is_exclusive(x_1539)) {
 lean_ctor_release(x_1539, 0);
 lean_ctor_release(x_1539, 1);
 x_1722 = x_1539;
} else {
 lean_dec_ref(x_1539);
 x_1722 = lean_box(0);
}
x_1723 = lean_box(0);
if (lean_is_scalar(x_1722)) {
 x_1724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1724 = x_1722;
}
lean_ctor_set(x_1724, 0, x_1723);
lean_ctor_set(x_1724, 1, x_1721);
return x_1724;
}
}
else
{
lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; 
lean_dec(x_1541);
lean_dec(x_1540);
lean_dec(x_1535);
lean_dec(x_1534);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1725 = lean_ctor_get(x_1539, 1);
lean_inc(x_1725);
if (lean_is_exclusive(x_1539)) {
 lean_ctor_release(x_1539, 0);
 lean_ctor_release(x_1539, 1);
 x_1726 = x_1539;
} else {
 lean_dec_ref(x_1539);
 x_1726 = lean_box(0);
}
x_1727 = lean_box(0);
if (lean_is_scalar(x_1726)) {
 x_1728 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1728 = x_1726;
}
lean_ctor_set(x_1728, 0, x_1727);
lean_ctor_set(x_1728, 1, x_1725);
return x_1728;
}
}
else
{
lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; 
lean_dec(x_1540);
lean_dec(x_1535);
lean_dec(x_1534);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1729 = lean_ctor_get(x_1539, 1);
lean_inc(x_1729);
if (lean_is_exclusive(x_1539)) {
 lean_ctor_release(x_1539, 0);
 lean_ctor_release(x_1539, 1);
 x_1730 = x_1539;
} else {
 lean_dec_ref(x_1539);
 x_1730 = lean_box(0);
}
x_1731 = lean_box(0);
if (lean_is_scalar(x_1730)) {
 x_1732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1732 = x_1730;
}
lean_ctor_set(x_1732, 0, x_1731);
lean_ctor_set(x_1732, 1, x_1729);
return x_1732;
}
}
else
{
lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; uint8_t x_1736; 
lean_dec(x_1535);
lean_dec(x_1534);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1733 = lean_ctor_get(x_1539, 0);
lean_inc(x_1733);
x_1734 = lean_ctor_get(x_1539, 1);
lean_inc(x_1734);
if (lean_is_exclusive(x_1539)) {
 lean_ctor_release(x_1539, 0);
 lean_ctor_release(x_1539, 1);
 x_1735 = x_1539;
} else {
 lean_dec_ref(x_1539);
 x_1735 = lean_box(0);
}
x_1736 = l_Lean_Exception_isInterrupt(x_1733);
if (x_1736 == 0)
{
uint8_t x_1737; 
x_1737 = l_Lean_Exception_isRuntime(x_1733);
if (x_1737 == 0)
{
lean_object* x_1738; lean_object* x_1739; 
lean_dec(x_1733);
x_1738 = lean_box(0);
if (lean_is_scalar(x_1735)) {
 x_1739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1739 = x_1735;
 lean_ctor_set_tag(x_1739, 0);
}
lean_ctor_set(x_1739, 0, x_1738);
lean_ctor_set(x_1739, 1, x_1734);
return x_1739;
}
else
{
lean_object* x_1740; 
if (lean_is_scalar(x_1735)) {
 x_1740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1740 = x_1735;
}
lean_ctor_set(x_1740, 0, x_1733);
lean_ctor_set(x_1740, 1, x_1734);
return x_1740;
}
}
else
{
lean_object* x_1741; 
if (lean_is_scalar(x_1735)) {
 x_1741 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1741 = x_1735;
}
lean_ctor_set(x_1741, 0, x_1733);
lean_ctor_set(x_1741, 1, x_1734);
return x_1741;
}
}
}
else
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; uint8_t x_1745; 
lean_dec(x_1535);
lean_dec(x_1534);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1742 = lean_ctor_get(x_1536, 0);
lean_inc(x_1742);
x_1743 = lean_ctor_get(x_1536, 1);
lean_inc(x_1743);
if (lean_is_exclusive(x_1536)) {
 lean_ctor_release(x_1536, 0);
 lean_ctor_release(x_1536, 1);
 x_1744 = x_1536;
} else {
 lean_dec_ref(x_1536);
 x_1744 = lean_box(0);
}
x_1745 = l_Lean_Exception_isInterrupt(x_1742);
if (x_1745 == 0)
{
uint8_t x_1746; 
x_1746 = l_Lean_Exception_isRuntime(x_1742);
if (x_1746 == 0)
{
lean_object* x_1747; lean_object* x_1748; 
lean_dec(x_1742);
x_1747 = lean_box(0);
if (lean_is_scalar(x_1744)) {
 x_1748 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1748 = x_1744;
 lean_ctor_set_tag(x_1748, 0);
}
lean_ctor_set(x_1748, 0, x_1747);
lean_ctor_set(x_1748, 1, x_1743);
return x_1748;
}
else
{
lean_object* x_1749; 
if (lean_is_scalar(x_1744)) {
 x_1749 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1749 = x_1744;
}
lean_ctor_set(x_1749, 0, x_1742);
lean_ctor_set(x_1749, 1, x_1743);
return x_1749;
}
}
else
{
lean_object* x_1750; 
if (lean_is_scalar(x_1744)) {
 x_1750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1750 = x_1744;
}
lean_ctor_set(x_1750, 0, x_1742);
lean_ctor_set(x_1750, 1, x_1743);
return x_1750;
}
}
}
else
{
lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; 
lean_dec(x_1532);
lean_dec(x_1531);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1751 = lean_ctor_get(x_1529, 1);
lean_inc(x_1751);
if (lean_is_exclusive(x_1529)) {
 lean_ctor_release(x_1529, 0);
 lean_ctor_release(x_1529, 1);
 x_1752 = x_1529;
} else {
 lean_dec_ref(x_1529);
 x_1752 = lean_box(0);
}
x_1753 = lean_box(0);
if (lean_is_scalar(x_1752)) {
 x_1754 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1754 = x_1752;
}
lean_ctor_set(x_1754, 0, x_1753);
lean_ctor_set(x_1754, 1, x_1751);
return x_1754;
}
}
else
{
lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; 
lean_dec(x_1531);
lean_dec(x_1530);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1755 = lean_ctor_get(x_1529, 1);
lean_inc(x_1755);
if (lean_is_exclusive(x_1529)) {
 lean_ctor_release(x_1529, 0);
 lean_ctor_release(x_1529, 1);
 x_1756 = x_1529;
} else {
 lean_dec_ref(x_1529);
 x_1756 = lean_box(0);
}
x_1757 = lean_box(0);
if (lean_is_scalar(x_1756)) {
 x_1758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1758 = x_1756;
}
lean_ctor_set(x_1758, 0, x_1757);
lean_ctor_set(x_1758, 1, x_1755);
return x_1758;
}
}
else
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; 
lean_dec(x_1530);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1759 = lean_ctor_get(x_1529, 1);
lean_inc(x_1759);
if (lean_is_exclusive(x_1529)) {
 lean_ctor_release(x_1529, 0);
 lean_ctor_release(x_1529, 1);
 x_1760 = x_1529;
} else {
 lean_dec_ref(x_1529);
 x_1760 = lean_box(0);
}
x_1761 = lean_box(0);
if (lean_is_scalar(x_1760)) {
 x_1762 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1762 = x_1760;
}
lean_ctor_set(x_1762, 0, x_1761);
lean_ctor_set(x_1762, 1, x_1759);
return x_1762;
}
}
else
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; uint8_t x_1766; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1763 = lean_ctor_get(x_1529, 0);
lean_inc(x_1763);
x_1764 = lean_ctor_get(x_1529, 1);
lean_inc(x_1764);
if (lean_is_exclusive(x_1529)) {
 lean_ctor_release(x_1529, 0);
 lean_ctor_release(x_1529, 1);
 x_1765 = x_1529;
} else {
 lean_dec_ref(x_1529);
 x_1765 = lean_box(0);
}
x_1766 = l_Lean_Exception_isInterrupt(x_1763);
if (x_1766 == 0)
{
uint8_t x_1767; 
x_1767 = l_Lean_Exception_isRuntime(x_1763);
if (x_1767 == 0)
{
lean_object* x_1768; lean_object* x_1769; 
lean_dec(x_1763);
x_1768 = lean_box(0);
if (lean_is_scalar(x_1765)) {
 x_1769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1769 = x_1765;
 lean_ctor_set_tag(x_1769, 0);
}
lean_ctor_set(x_1769, 0, x_1768);
lean_ctor_set(x_1769, 1, x_1764);
return x_1769;
}
else
{
lean_object* x_1770; 
if (lean_is_scalar(x_1765)) {
 x_1770 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1770 = x_1765;
}
lean_ctor_set(x_1770, 0, x_1763);
lean_ctor_set(x_1770, 1, x_1764);
return x_1770;
}
}
else
{
lean_object* x_1771; 
if (lean_is_scalar(x_1765)) {
 x_1771 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1771 = x_1765;
}
lean_ctor_set(x_1771, 0, x_1763);
lean_ctor_set(x_1771, 1, x_1764);
return x_1771;
}
}
}
else
{
lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; uint8_t x_1775; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1772 = lean_ctor_get(x_1526, 0);
lean_inc(x_1772);
x_1773 = lean_ctor_get(x_1526, 1);
lean_inc(x_1773);
if (lean_is_exclusive(x_1526)) {
 lean_ctor_release(x_1526, 0);
 lean_ctor_release(x_1526, 1);
 x_1774 = x_1526;
} else {
 lean_dec_ref(x_1526);
 x_1774 = lean_box(0);
}
x_1775 = l_Lean_Exception_isInterrupt(x_1772);
if (x_1775 == 0)
{
uint8_t x_1776; 
x_1776 = l_Lean_Exception_isRuntime(x_1772);
if (x_1776 == 0)
{
lean_object* x_1777; lean_object* x_1778; 
lean_dec(x_1772);
x_1777 = lean_box(0);
if (lean_is_scalar(x_1774)) {
 x_1778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1778 = x_1774;
 lean_ctor_set_tag(x_1778, 0);
}
lean_ctor_set(x_1778, 0, x_1777);
lean_ctor_set(x_1778, 1, x_1773);
return x_1778;
}
else
{
lean_object* x_1779; 
if (lean_is_scalar(x_1774)) {
 x_1779 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1779 = x_1774;
}
lean_ctor_set(x_1779, 0, x_1772);
lean_ctor_set(x_1779, 1, x_1773);
return x_1779;
}
}
else
{
lean_object* x_1780; 
if (lean_is_scalar(x_1774)) {
 x_1780 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1780 = x_1774;
}
lean_ctor_set(x_1780, 0, x_1772);
lean_ctor_set(x_1780, 1, x_1773);
return x_1780;
}
}
}
}
}
else
{
lean_object* x_1781; lean_object* x_1782; 
lean_dec(x_40);
lean_dec(x_33);
x_1781 = lean_ctor_get(x_70, 1);
lean_inc(x_1781);
lean_dec(x_70);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1782 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_1781);
if (lean_obj_tag(x_1782) == 0)
{
lean_object* x_1783; 
x_1783 = lean_ctor_get(x_1782, 0);
lean_inc(x_1783);
if (lean_obj_tag(x_1783) == 0)
{
uint8_t x_1784; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_free_object(x_43);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1784 = !lean_is_exclusive(x_1782);
if (x_1784 == 0)
{
lean_object* x_1785; lean_object* x_1786; 
x_1785 = lean_ctor_get(x_1782, 0);
lean_dec(x_1785);
x_1786 = lean_box(0);
lean_ctor_set(x_1782, 0, x_1786);
return x_1782;
}
else
{
lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; 
x_1787 = lean_ctor_get(x_1782, 1);
lean_inc(x_1787);
lean_dec(x_1782);
x_1788 = lean_box(0);
x_1789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1789, 0, x_1788);
lean_ctor_set(x_1789, 1, x_1787);
return x_1789;
}
}
else
{
lean_object* x_1790; uint8_t x_1791; 
x_1790 = lean_ctor_get(x_1782, 1);
lean_inc(x_1790);
lean_dec(x_1782);
x_1791 = !lean_is_exclusive(x_1783);
if (x_1791 == 0)
{
lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; 
x_1792 = lean_ctor_get(x_1783, 0);
lean_ctor_set(x_1783, 0, x_68);
lean_ctor_set(x_57, 0, x_69);
lean_ctor_set(x_43, 0, x_55);
x_1793 = lean_box(0);
x_1794 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1794, 0, x_1792);
x_1795 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1795, 0, x_1);
x_1796 = lean_box(0);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 1, x_1796);
lean_ctor_set(x_65, 0, x_1795);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_65);
lean_ctor_set(x_51, 0, x_1794);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_1793);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_43);
x_1797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1797, 0, x_57);
lean_ctor_set(x_1797, 1, x_31);
x_1798 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1798, 0, x_1783);
lean_ctor_set(x_1798, 1, x_1797);
x_1799 = lean_array_mk(x_1798);
x_1800 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1801 = l_Lean_Meta_mkAppOptM(x_1800, x_1799, x_3, x_4, x_5, x_6, x_1790);
if (lean_obj_tag(x_1801) == 0)
{
lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; 
x_1802 = lean_ctor_get(x_1801, 0);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1801, 1);
lean_inc(x_1803);
lean_dec(x_1801);
x_1804 = l_Lean_Meta_expandCoe(x_1802, x_3, x_4, x_5, x_6, x_1803);
if (lean_obj_tag(x_1804) == 0)
{
lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; 
x_1805 = lean_ctor_get(x_1804, 0);
lean_inc(x_1805);
x_1806 = lean_ctor_get(x_1804, 1);
lean_inc(x_1806);
lean_dec(x_1804);
x_1807 = lean_box(0);
x_1808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1808, 0, x_1805);
lean_ctor_set(x_1808, 1, x_1807);
x_17 = x_1808;
x_18 = x_1806;
goto block_30;
}
else
{
uint8_t x_1809; 
x_1809 = !lean_is_exclusive(x_1804);
if (x_1809 == 0)
{
lean_object* x_1810; lean_object* x_1811; uint8_t x_1812; 
x_1810 = lean_ctor_get(x_1804, 0);
x_1811 = lean_ctor_get(x_1804, 1);
x_1812 = l_Lean_Exception_isInterrupt(x_1810);
if (x_1812 == 0)
{
uint8_t x_1813; 
x_1813 = l_Lean_Exception_isRuntime(x_1810);
if (x_1813 == 0)
{
lean_object* x_1814; 
lean_free_object(x_1804);
lean_dec(x_1810);
x_1814 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_1814;
x_18 = x_1811;
goto block_30;
}
else
{
return x_1804;
}
}
else
{
return x_1804;
}
}
else
{
lean_object* x_1815; lean_object* x_1816; uint8_t x_1817; 
x_1815 = lean_ctor_get(x_1804, 0);
x_1816 = lean_ctor_get(x_1804, 1);
lean_inc(x_1816);
lean_inc(x_1815);
lean_dec(x_1804);
x_1817 = l_Lean_Exception_isInterrupt(x_1815);
if (x_1817 == 0)
{
uint8_t x_1818; 
x_1818 = l_Lean_Exception_isRuntime(x_1815);
if (x_1818 == 0)
{
lean_object* x_1819; 
lean_dec(x_1815);
x_1819 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_1819;
x_18 = x_1816;
goto block_30;
}
else
{
lean_object* x_1820; 
x_1820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1820, 0, x_1815);
lean_ctor_set(x_1820, 1, x_1816);
return x_1820;
}
}
else
{
lean_object* x_1821; 
x_1821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1821, 0, x_1815);
lean_ctor_set(x_1821, 1, x_1816);
return x_1821;
}
}
}
}
else
{
uint8_t x_1822; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1822 = !lean_is_exclusive(x_1801);
if (x_1822 == 0)
{
lean_object* x_1823; lean_object* x_1824; uint8_t x_1825; 
x_1823 = lean_ctor_get(x_1801, 0);
x_1824 = lean_ctor_get(x_1801, 1);
x_1825 = l_Lean_Exception_isInterrupt(x_1823);
if (x_1825 == 0)
{
uint8_t x_1826; 
x_1826 = l_Lean_Exception_isRuntime(x_1823);
if (x_1826 == 0)
{
lean_object* x_1827; 
lean_free_object(x_1801);
lean_dec(x_1823);
x_1827 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_1827;
x_18 = x_1824;
goto block_30;
}
else
{
return x_1801;
}
}
else
{
return x_1801;
}
}
else
{
lean_object* x_1828; lean_object* x_1829; uint8_t x_1830; 
x_1828 = lean_ctor_get(x_1801, 0);
x_1829 = lean_ctor_get(x_1801, 1);
lean_inc(x_1829);
lean_inc(x_1828);
lean_dec(x_1801);
x_1830 = l_Lean_Exception_isInterrupt(x_1828);
if (x_1830 == 0)
{
uint8_t x_1831; 
x_1831 = l_Lean_Exception_isRuntime(x_1828);
if (x_1831 == 0)
{
lean_object* x_1832; 
lean_dec(x_1828);
x_1832 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_1832;
x_18 = x_1829;
goto block_30;
}
else
{
lean_object* x_1833; 
x_1833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1833, 0, x_1828);
lean_ctor_set(x_1833, 1, x_1829);
return x_1833;
}
}
else
{
lean_object* x_1834; 
x_1834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1834, 0, x_1828);
lean_ctor_set(x_1834, 1, x_1829);
return x_1834;
}
}
}
}
else
{
lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; 
x_1835 = lean_ctor_get(x_1783, 0);
lean_inc(x_1835);
lean_dec(x_1783);
x_1836 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1836, 0, x_68);
lean_ctor_set(x_57, 0, x_69);
lean_ctor_set(x_43, 0, x_55);
x_1837 = lean_box(0);
x_1838 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1838, 0, x_1835);
x_1839 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1839, 0, x_1);
x_1840 = lean_box(0);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 1, x_1840);
lean_ctor_set(x_65, 0, x_1839);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_65);
lean_ctor_set(x_51, 0, x_1838);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_1837);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_43);
x_1841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1841, 0, x_57);
lean_ctor_set(x_1841, 1, x_31);
x_1842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1842, 0, x_1836);
lean_ctor_set(x_1842, 1, x_1841);
x_1843 = lean_array_mk(x_1842);
x_1844 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1845 = l_Lean_Meta_mkAppOptM(x_1844, x_1843, x_3, x_4, x_5, x_6, x_1790);
if (lean_obj_tag(x_1845) == 0)
{
lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; 
x_1846 = lean_ctor_get(x_1845, 0);
lean_inc(x_1846);
x_1847 = lean_ctor_get(x_1845, 1);
lean_inc(x_1847);
lean_dec(x_1845);
x_1848 = l_Lean_Meta_expandCoe(x_1846, x_3, x_4, x_5, x_6, x_1847);
if (lean_obj_tag(x_1848) == 0)
{
lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; 
x_1849 = lean_ctor_get(x_1848, 0);
lean_inc(x_1849);
x_1850 = lean_ctor_get(x_1848, 1);
lean_inc(x_1850);
lean_dec(x_1848);
x_1851 = lean_box(0);
x_1852 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1852, 0, x_1849);
lean_ctor_set(x_1852, 1, x_1851);
x_17 = x_1852;
x_18 = x_1850;
goto block_30;
}
else
{
lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; uint8_t x_1856; 
x_1853 = lean_ctor_get(x_1848, 0);
lean_inc(x_1853);
x_1854 = lean_ctor_get(x_1848, 1);
lean_inc(x_1854);
if (lean_is_exclusive(x_1848)) {
 lean_ctor_release(x_1848, 0);
 lean_ctor_release(x_1848, 1);
 x_1855 = x_1848;
} else {
 lean_dec_ref(x_1848);
 x_1855 = lean_box(0);
}
x_1856 = l_Lean_Exception_isInterrupt(x_1853);
if (x_1856 == 0)
{
uint8_t x_1857; 
x_1857 = l_Lean_Exception_isRuntime(x_1853);
if (x_1857 == 0)
{
lean_object* x_1858; 
lean_dec(x_1855);
lean_dec(x_1853);
x_1858 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_1858;
x_18 = x_1854;
goto block_30;
}
else
{
lean_object* x_1859; 
if (lean_is_scalar(x_1855)) {
 x_1859 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1859 = x_1855;
}
lean_ctor_set(x_1859, 0, x_1853);
lean_ctor_set(x_1859, 1, x_1854);
return x_1859;
}
}
else
{
lean_object* x_1860; 
if (lean_is_scalar(x_1855)) {
 x_1860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1860 = x_1855;
}
lean_ctor_set(x_1860, 0, x_1853);
lean_ctor_set(x_1860, 1, x_1854);
return x_1860;
}
}
}
else
{
lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; uint8_t x_1864; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1861 = lean_ctor_get(x_1845, 0);
lean_inc(x_1861);
x_1862 = lean_ctor_get(x_1845, 1);
lean_inc(x_1862);
if (lean_is_exclusive(x_1845)) {
 lean_ctor_release(x_1845, 0);
 lean_ctor_release(x_1845, 1);
 x_1863 = x_1845;
} else {
 lean_dec_ref(x_1845);
 x_1863 = lean_box(0);
}
x_1864 = l_Lean_Exception_isInterrupt(x_1861);
if (x_1864 == 0)
{
uint8_t x_1865; 
x_1865 = l_Lean_Exception_isRuntime(x_1861);
if (x_1865 == 0)
{
lean_object* x_1866; 
lean_dec(x_1863);
lean_dec(x_1861);
x_1866 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_1866;
x_18 = x_1862;
goto block_30;
}
else
{
lean_object* x_1867; 
if (lean_is_scalar(x_1863)) {
 x_1867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1867 = x_1863;
}
lean_ctor_set(x_1867, 0, x_1861);
lean_ctor_set(x_1867, 1, x_1862);
return x_1867;
}
}
else
{
lean_object* x_1868; 
if (lean_is_scalar(x_1863)) {
 x_1868 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1868 = x_1863;
}
lean_ctor_set(x_1868, 0, x_1861);
lean_ctor_set(x_1868, 1, x_1862);
return x_1868;
}
}
}
}
}
else
{
uint8_t x_1869; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_free_object(x_43);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1869 = !lean_is_exclusive(x_1782);
if (x_1869 == 0)
{
return x_1782;
}
else
{
lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; 
x_1870 = lean_ctor_get(x_1782, 0);
x_1871 = lean_ctor_get(x_1782, 1);
lean_inc(x_1871);
lean_inc(x_1870);
lean_dec(x_1782);
x_1872 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1872, 0, x_1870);
lean_ctor_set(x_1872, 1, x_1871);
return x_1872;
}
}
}
}
else
{
uint8_t x_1873; 
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1873 = !lean_is_exclusive(x_70);
if (x_1873 == 0)
{
return x_70;
}
else
{
lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; 
x_1874 = lean_ctor_get(x_70, 0);
x_1875 = lean_ctor_get(x_70, 1);
lean_inc(x_1875);
lean_inc(x_1874);
lean_dec(x_70);
x_1876 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1876, 0, x_1874);
lean_ctor_set(x_1876, 1, x_1875);
return x_1876;
}
}
}
else
{
lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; 
x_1877 = lean_ctor_get(x_65, 0);
x_1878 = lean_ctor_get(x_65, 1);
lean_inc(x_1878);
lean_inc(x_1877);
lean_dec(x_65);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
lean_inc(x_1877);
x_1879 = l_Lean_Meta_isExprDefEq(x_1877, x_54, x_3, x_4, x_5, x_6, x_66);
if (lean_obj_tag(x_1879) == 0)
{
lean_object* x_1880; uint8_t x_1881; 
x_1880 = lean_ctor_get(x_1879, 0);
lean_inc(x_1880);
x_1881 = lean_unbox(x_1880);
lean_dec(x_1880);
if (x_1881 == 0)
{
lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; uint8_t x_1886; 
lean_free_object(x_43);
x_1882 = lean_ctor_get(x_1879, 1);
lean_inc(x_1882);
if (lean_is_exclusive(x_1879)) {
 lean_ctor_release(x_1879, 0);
 lean_ctor_release(x_1879, 1);
 x_1883 = x_1879;
} else {
 lean_dec_ref(x_1879);
 x_1883 = lean_box(0);
}
x_1884 = lean_ctor_get(x_5, 2);
lean_inc(x_1884);
x_1885 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1886 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1884, x_1885);
lean_dec(x_1884);
if (x_1886 == 0)
{
lean_object* x_1887; lean_object* x_1888; 
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1887 = lean_box(0);
if (lean_is_scalar(x_1883)) {
 x_1888 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1888 = x_1883;
}
lean_ctor_set(x_1888, 0, x_1887);
lean_ctor_set(x_1888, 1, x_1882);
return x_1888;
}
else
{
lean_object* x_1889; 
lean_dec(x_1883);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1877);
x_1889 = lean_infer_type(x_1877, x_3, x_4, x_5, x_6, x_1882);
if (lean_obj_tag(x_1889) == 0)
{
lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; 
x_1890 = lean_ctor_get(x_1889, 0);
lean_inc(x_1890);
x_1891 = lean_ctor_get(x_1889, 1);
lean_inc(x_1891);
lean_dec(x_1889);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1892 = lean_whnf(x_1890, x_3, x_4, x_5, x_6, x_1891);
if (lean_obj_tag(x_1892) == 0)
{
lean_object* x_1893; 
x_1893 = lean_ctor_get(x_1892, 0);
lean_inc(x_1893);
if (lean_obj_tag(x_1893) == 7)
{
lean_object* x_1894; 
x_1894 = lean_ctor_get(x_1893, 1);
lean_inc(x_1894);
if (lean_obj_tag(x_1894) == 3)
{
lean_object* x_1895; 
x_1895 = lean_ctor_get(x_1893, 2);
lean_inc(x_1895);
lean_dec(x_1893);
if (lean_obj_tag(x_1895) == 3)
{
lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; 
x_1896 = lean_ctor_get(x_1892, 1);
lean_inc(x_1896);
lean_dec(x_1892);
x_1897 = lean_ctor_get(x_1894, 0);
lean_inc(x_1897);
lean_dec(x_1894);
x_1898 = lean_ctor_get(x_1895, 0);
lean_inc(x_1898);
lean_dec(x_1895);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_1899 = lean_infer_type(x_54, x_3, x_4, x_5, x_6, x_1896);
if (lean_obj_tag(x_1899) == 0)
{
lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; 
x_1900 = lean_ctor_get(x_1899, 0);
lean_inc(x_1900);
x_1901 = lean_ctor_get(x_1899, 1);
lean_inc(x_1901);
lean_dec(x_1899);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1902 = lean_whnf(x_1900, x_3, x_4, x_5, x_6, x_1901);
if (lean_obj_tag(x_1902) == 0)
{
lean_object* x_1903; 
x_1903 = lean_ctor_get(x_1902, 0);
lean_inc(x_1903);
if (lean_obj_tag(x_1903) == 7)
{
lean_object* x_1904; 
x_1904 = lean_ctor_get(x_1903, 1);
lean_inc(x_1904);
if (lean_obj_tag(x_1904) == 3)
{
lean_object* x_1905; 
x_1905 = lean_ctor_get(x_1903, 2);
lean_inc(x_1905);
lean_dec(x_1903);
if (lean_obj_tag(x_1905) == 3)
{
lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; 
x_1906 = lean_ctor_get(x_1902, 1);
lean_inc(x_1906);
lean_dec(x_1902);
x_1907 = lean_ctor_get(x_1904, 0);
lean_inc(x_1907);
lean_dec(x_1904);
x_1908 = lean_ctor_get(x_1905, 0);
lean_inc(x_1908);
lean_dec(x_1905);
x_1909 = l_Lean_Meta_decLevel(x_1897, x_3, x_4, x_5, x_6, x_1906);
if (lean_obj_tag(x_1909) == 0)
{
lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; 
x_1910 = lean_ctor_get(x_1909, 0);
lean_inc(x_1910);
x_1911 = lean_ctor_get(x_1909, 1);
lean_inc(x_1911);
if (lean_is_exclusive(x_1909)) {
 lean_ctor_release(x_1909, 0);
 lean_ctor_release(x_1909, 1);
 x_1912 = x_1909;
} else {
 lean_dec_ref(x_1909);
 x_1912 = lean_box(0);
}
x_1913 = l_Lean_Meta_decLevel(x_1907, x_3, x_4, x_5, x_6, x_1911);
if (lean_obj_tag(x_1913) == 0)
{
lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; uint8_t x_1917; lean_object* x_1918; 
x_1914 = lean_ctor_get(x_1913, 0);
lean_inc(x_1914);
x_1915 = lean_ctor_get(x_1913, 1);
lean_inc(x_1915);
if (lean_is_exclusive(x_1913)) {
 lean_ctor_release(x_1913, 0);
 lean_ctor_release(x_1913, 1);
 x_1916 = x_1913;
} else {
 lean_dec_ref(x_1913);
 x_1916 = lean_box(0);
}
x_1917 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1910);
x_1918 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1910, x_1914, x_1917, x_3, x_4, x_5, x_6, x_1915);
if (lean_obj_tag(x_1918) == 0)
{
lean_object* x_1919; uint8_t x_1920; 
x_1919 = lean_ctor_get(x_1918, 0);
lean_inc(x_1919);
x_1920 = lean_unbox(x_1919);
lean_dec(x_1919);
if (x_1920 == 0)
{
lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; 
lean_dec(x_1916);
lean_dec(x_1912);
lean_dec(x_1910);
lean_dec(x_1908);
lean_dec(x_1898);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1921 = lean_ctor_get(x_1918, 1);
lean_inc(x_1921);
if (lean_is_exclusive(x_1918)) {
 lean_ctor_release(x_1918, 0);
 lean_ctor_release(x_1918, 1);
 x_1922 = x_1918;
} else {
 lean_dec_ref(x_1918);
 x_1922 = lean_box(0);
}
x_1923 = lean_box(0);
if (lean_is_scalar(x_1922)) {
 x_1924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1924 = x_1922;
}
lean_ctor_set(x_1924, 0, x_1923);
lean_ctor_set(x_1924, 1, x_1921);
return x_1924;
}
else
{
lean_object* x_1925; lean_object* x_1926; 
x_1925 = lean_ctor_get(x_1918, 1);
lean_inc(x_1925);
lean_dec(x_1918);
x_1926 = l_Lean_Meta_decLevel(x_1898, x_3, x_4, x_5, x_6, x_1925);
if (lean_obj_tag(x_1926) == 0)
{
lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; 
x_1927 = lean_ctor_get(x_1926, 0);
lean_inc(x_1927);
x_1928 = lean_ctor_get(x_1926, 1);
lean_inc(x_1928);
if (lean_is_exclusive(x_1926)) {
 lean_ctor_release(x_1926, 0);
 lean_ctor_release(x_1926, 1);
 x_1929 = x_1926;
} else {
 lean_dec_ref(x_1926);
 x_1929 = lean_box(0);
}
x_1930 = l_Lean_Meta_decLevel(x_1908, x_3, x_4, x_5, x_6, x_1928);
if (lean_obj_tag(x_1930) == 0)
{
lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; 
x_1931 = lean_ctor_get(x_1930, 0);
lean_inc(x_1931);
x_1932 = lean_ctor_get(x_1930, 1);
lean_inc(x_1932);
if (lean_is_exclusive(x_1930)) {
 lean_ctor_release(x_1930, 0);
 lean_ctor_release(x_1930, 1);
 x_1933 = x_1930;
} else {
 lean_dec_ref(x_1930);
 x_1933 = lean_box(0);
}
x_1934 = lean_box(0);
if (lean_is_scalar(x_1933)) {
 x_1935 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1935 = x_1933;
 lean_ctor_set_tag(x_1935, 1);
}
lean_ctor_set(x_1935, 0, x_1931);
lean_ctor_set(x_1935, 1, x_1934);
if (lean_is_scalar(x_1929)) {
 x_1936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1936 = x_1929;
 lean_ctor_set_tag(x_1936, 1);
}
lean_ctor_set(x_1936, 0, x_1927);
lean_ctor_set(x_1936, 1, x_1935);
if (lean_is_scalar(x_1916)) {
 x_1937 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1937 = x_1916;
 lean_ctor_set_tag(x_1937, 1);
}
lean_ctor_set(x_1937, 0, x_1910);
lean_ctor_set(x_1937, 1, x_1936);
x_1938 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1939 = l_Lean_Expr_const___override(x_1938, x_1937);
lean_inc(x_54);
if (lean_is_scalar(x_1912)) {
 x_1940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1940 = x_1912;
 lean_ctor_set_tag(x_1940, 1);
}
lean_ctor_set(x_1940, 0, x_54);
lean_ctor_set(x_1940, 1, x_1934);
lean_inc(x_1877);
x_1941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1941, 0, x_1877);
lean_ctor_set(x_1941, 1, x_1940);
x_1942 = lean_array_mk(x_1941);
x_1943 = l_Lean_mkAppN(x_1939, x_1942);
lean_dec(x_1942);
x_1944 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1945 = l_Lean_Meta_trySynthInstance(x_1943, x_1944, x_3, x_4, x_5, x_6, x_1932);
if (lean_obj_tag(x_1945) == 0)
{
lean_object* x_1946; 
x_1946 = lean_ctor_get(x_1945, 0);
lean_inc(x_1946);
if (lean_obj_tag(x_1946) == 1)
{
lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; 
x_1947 = lean_ctor_get(x_1945, 1);
lean_inc(x_1947);
lean_dec(x_1945);
x_1948 = lean_ctor_get(x_1946, 0);
lean_inc(x_1948);
lean_dec(x_1946);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1878);
x_1949 = l_Lean_Meta_getDecLevel(x_1878, x_3, x_4, x_5, x_6, x_1947);
if (lean_obj_tag(x_1949) == 0)
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; 
x_1950 = lean_ctor_get(x_1949, 0);
lean_inc(x_1950);
x_1951 = lean_ctor_get(x_1949, 1);
lean_inc(x_1951);
if (lean_is_exclusive(x_1949)) {
 lean_ctor_release(x_1949, 0);
 lean_ctor_release(x_1949, 1);
 x_1952 = x_1949;
} else {
 lean_dec_ref(x_1949);
 x_1952 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1953 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_1951);
if (lean_obj_tag(x_1953) == 0)
{
lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; 
x_1954 = lean_ctor_get(x_1953, 0);
lean_inc(x_1954);
x_1955 = lean_ctor_get(x_1953, 1);
lean_inc(x_1955);
if (lean_is_exclusive(x_1953)) {
 lean_ctor_release(x_1953, 0);
 lean_ctor_release(x_1953, 1);
 x_1956 = x_1953;
} else {
 lean_dec_ref(x_1953);
 x_1956 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_1957 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_1955);
if (lean_obj_tag(x_1957) == 0)
{
lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; 
x_1958 = lean_ctor_get(x_1957, 0);
lean_inc(x_1958);
x_1959 = lean_ctor_get(x_1957, 1);
lean_inc(x_1959);
if (lean_is_exclusive(x_1957)) {
 lean_ctor_release(x_1957, 0);
 lean_ctor_release(x_1957, 1);
 x_1960 = x_1957;
} else {
 lean_dec_ref(x_1957);
 x_1960 = lean_box(0);
}
if (lean_is_scalar(x_1960)) {
 x_1961 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1961 = x_1960;
 lean_ctor_set_tag(x_1961, 1);
}
lean_ctor_set(x_1961, 0, x_1958);
lean_ctor_set(x_1961, 1, x_1934);
if (lean_is_scalar(x_1956)) {
 x_1962 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1962 = x_1956;
 lean_ctor_set_tag(x_1962, 1);
}
lean_ctor_set(x_1962, 0, x_1954);
lean_ctor_set(x_1962, 1, x_1961);
if (lean_is_scalar(x_1952)) {
 x_1963 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1963 = x_1952;
 lean_ctor_set_tag(x_1963, 1);
}
lean_ctor_set(x_1963, 0, x_1950);
lean_ctor_set(x_1963, 1, x_1962);
x_1964 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_1963);
x_1965 = l_Lean_Expr_const___override(x_1964, x_1963);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_1934);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_1878);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_1878);
lean_inc(x_1948);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_1948);
lean_inc(x_54);
x_1966 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1966, 0, x_54);
lean_ctor_set(x_1966, 1, x_31);
lean_inc(x_1877);
x_1967 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1967, 0, x_1877);
lean_ctor_set(x_1967, 1, x_1966);
x_1968 = lean_array_mk(x_1967);
x_1969 = l_Lean_mkAppN(x_1965, x_1968);
lean_dec(x_1968);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1969);
x_1970 = lean_infer_type(x_1969, x_3, x_4, x_5, x_6, x_1959);
if (lean_obj_tag(x_1970) == 0)
{
lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; 
x_1971 = lean_ctor_get(x_1970, 0);
lean_inc(x_1971);
x_1972 = lean_ctor_get(x_1970, 1);
lean_inc(x_1972);
if (lean_is_exclusive(x_1970)) {
 lean_ctor_release(x_1970, 0);
 lean_ctor_release(x_1970, 1);
 x_1973 = x_1970;
} else {
 lean_dec_ref(x_1970);
 x_1973 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_1974 = l_Lean_Meta_isExprDefEq(x_33, x_1971, x_3, x_4, x_5, x_6, x_1972);
if (lean_obj_tag(x_1974) == 0)
{
lean_object* x_1975; uint8_t x_1976; 
x_1975 = lean_ctor_get(x_1974, 0);
lean_inc(x_1975);
x_1976 = lean_unbox(x_1975);
lean_dec(x_1975);
if (x_1976 == 0)
{
lean_object* x_1977; lean_object* x_1978; 
lean_dec(x_1969);
lean_free_object(x_57);
x_1977 = lean_ctor_get(x_1974, 1);
lean_inc(x_1977);
lean_dec(x_1974);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_1978 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_1977);
if (lean_obj_tag(x_1978) == 0)
{
lean_object* x_1979; 
x_1979 = lean_ctor_get(x_1978, 0);
lean_inc(x_1979);
if (lean_obj_tag(x_1979) == 0)
{
lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; 
lean_dec(x_1973);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1980 = lean_ctor_get(x_1978, 1);
lean_inc(x_1980);
if (lean_is_exclusive(x_1978)) {
 lean_ctor_release(x_1978, 0);
 lean_ctor_release(x_1978, 1);
 x_1981 = x_1978;
} else {
 lean_dec_ref(x_1978);
 x_1981 = lean_box(0);
}
if (lean_is_scalar(x_1981)) {
 x_1982 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1982 = x_1981;
}
lean_ctor_set(x_1982, 0, x_1944);
lean_ctor_set(x_1982, 1, x_1980);
return x_1982;
}
else
{
lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; 
x_1983 = lean_ctor_get(x_1978, 1);
lean_inc(x_1983);
lean_dec(x_1978);
x_1984 = lean_ctor_get(x_1979, 0);
lean_inc(x_1984);
lean_dec(x_1979);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1878);
x_1985 = l_Lean_Meta_getLevel(x_1878, x_3, x_4, x_5, x_6, x_1983);
if (lean_obj_tag(x_1985) == 0)
{
lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; 
x_1986 = lean_ctor_get(x_1985, 0);
lean_inc(x_1986);
x_1987 = lean_ctor_get(x_1985, 1);
lean_inc(x_1987);
if (lean_is_exclusive(x_1985)) {
 lean_ctor_release(x_1985, 0);
 lean_ctor_release(x_1985, 1);
 x_1988 = x_1985;
} else {
 lean_dec_ref(x_1985);
 x_1988 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1989 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_1987);
if (lean_obj_tag(x_1989) == 0)
{
lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; uint8_t x_2004; lean_object* x_2005; lean_object* x_2006; 
x_1990 = lean_ctor_get(x_1989, 0);
lean_inc(x_1990);
x_1991 = lean_ctor_get(x_1989, 1);
lean_inc(x_1991);
if (lean_is_exclusive(x_1989)) {
 lean_ctor_release(x_1989, 0);
 lean_ctor_release(x_1989, 1);
 x_1992 = x_1989;
} else {
 lean_dec_ref(x_1989);
 x_1992 = lean_box(0);
}
if (lean_is_scalar(x_1992)) {
 x_1993 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1993 = x_1992;
 lean_ctor_set_tag(x_1993, 1);
}
lean_ctor_set(x_1993, 0, x_1990);
lean_ctor_set(x_1993, 1, x_1934);
if (lean_is_scalar(x_1988)) {
 x_1994 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1994 = x_1988;
 lean_ctor_set_tag(x_1994, 1);
}
lean_ctor_set(x_1994, 0, x_1986);
lean_ctor_set(x_1994, 1, x_1993);
x_1995 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1996 = l_Lean_Expr_const___override(x_1995, x_1994);
lean_inc(x_55);
if (lean_is_scalar(x_1973)) {
 x_1997 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1997 = x_1973;
 lean_ctor_set_tag(x_1997, 1);
}
lean_ctor_set(x_1997, 0, x_55);
lean_ctor_set(x_1997, 1, x_1934);
x_1998 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1999 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1999, 0, x_1998);
lean_ctor_set(x_1999, 1, x_1997);
lean_inc(x_1878);
x_2000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2000, 0, x_1878);
lean_ctor_set(x_2000, 1, x_1999);
x_2001 = lean_array_mk(x_2000);
x_2002 = l_Lean_mkAppN(x_1996, x_2001);
lean_dec(x_2001);
x_2003 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_2004 = 0;
lean_inc(x_1878);
x_2005 = l_Lean_Expr_forallE___override(x_2003, x_1878, x_2002, x_2004);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2006 = l_Lean_Meta_trySynthInstance(x_2005, x_1944, x_3, x_4, x_5, x_6, x_1991);
if (lean_obj_tag(x_2006) == 0)
{
lean_object* x_2007; 
x_2007 = lean_ctor_get(x_2006, 0);
lean_inc(x_2007);
if (lean_obj_tag(x_2007) == 1)
{
lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; 
x_2008 = lean_ctor_get(x_2006, 1);
lean_inc(x_2008);
lean_dec(x_2006);
x_2009 = lean_ctor_get(x_2007, 0);
lean_inc(x_2009);
lean_dec(x_2007);
x_2010 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_2011 = l_Lean_Expr_const___override(x_2010, x_1963);
x_2012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2012, 0, x_1984);
lean_ctor_set(x_2012, 1, x_51);
x_2013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2013, 0, x_2009);
lean_ctor_set(x_2013, 1, x_2012);
x_2014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2014, 0, x_1948);
lean_ctor_set(x_2014, 1, x_2013);
x_2015 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2015, 0, x_55);
lean_ctor_set(x_2015, 1, x_2014);
x_2016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2016, 0, x_1878);
lean_ctor_set(x_2016, 1, x_2015);
x_2017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2017, 0, x_54);
lean_ctor_set(x_2017, 1, x_2016);
x_2018 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2018, 0, x_1877);
lean_ctor_set(x_2018, 1, x_2017);
x_2019 = lean_array_mk(x_2018);
x_2020 = l_Lean_mkAppN(x_2011, x_2019);
lean_dec(x_2019);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2021 = l_Lean_Meta_expandCoe(x_2020, x_3, x_4, x_5, x_6, x_2008);
if (lean_obj_tag(x_2021) == 0)
{
lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; 
x_2022 = lean_ctor_get(x_2021, 0);
lean_inc(x_2022);
x_2023 = lean_ctor_get(x_2021, 1);
lean_inc(x_2023);
lean_dec(x_2021);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2022);
x_2024 = lean_infer_type(x_2022, x_3, x_4, x_5, x_6, x_2023);
if (lean_obj_tag(x_2024) == 0)
{
lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; 
x_2025 = lean_ctor_get(x_2024, 0);
lean_inc(x_2025);
x_2026 = lean_ctor_get(x_2024, 1);
lean_inc(x_2026);
lean_dec(x_2024);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2027 = l_Lean_Meta_isExprDefEq(x_33, x_2025, x_3, x_4, x_5, x_6, x_2026);
if (lean_obj_tag(x_2027) == 0)
{
lean_object* x_2028; uint8_t x_2029; 
x_2028 = lean_ctor_get(x_2027, 0);
lean_inc(x_2028);
x_2029 = lean_unbox(x_2028);
lean_dec(x_2028);
if (x_2029 == 0)
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; 
lean_dec(x_2022);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2030 = lean_ctor_get(x_2027, 1);
lean_inc(x_2030);
if (lean_is_exclusive(x_2027)) {
 lean_ctor_release(x_2027, 0);
 lean_ctor_release(x_2027, 1);
 x_2031 = x_2027;
} else {
 lean_dec_ref(x_2027);
 x_2031 = lean_box(0);
}
if (lean_is_scalar(x_2031)) {
 x_2032 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2032 = x_2031;
}
lean_ctor_set(x_2032, 0, x_1944);
lean_ctor_set(x_2032, 1, x_2030);
return x_2032;
}
else
{
lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; 
x_2033 = lean_ctor_get(x_2027, 1);
lean_inc(x_2033);
lean_dec(x_2027);
x_2034 = lean_box(0);
x_2035 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2022, x_2034, x_3, x_4, x_5, x_6, x_2033);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2036 = lean_ctor_get(x_2035, 0);
lean_inc(x_2036);
x_2037 = lean_ctor_get(x_2035, 1);
lean_inc(x_2037);
if (lean_is_exclusive(x_2035)) {
 lean_ctor_release(x_2035, 0);
 lean_ctor_release(x_2035, 1);
 x_2038 = x_2035;
} else {
 lean_dec_ref(x_2035);
 x_2038 = lean_box(0);
}
if (lean_is_scalar(x_2038)) {
 x_2039 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2039 = x_2038;
}
lean_ctor_set(x_2039, 0, x_2036);
lean_ctor_set(x_2039, 1, x_2037);
return x_2039;
}
}
else
{
lean_object* x_2040; lean_object* x_2041; 
lean_dec(x_2022);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2040 = lean_ctor_get(x_2027, 0);
lean_inc(x_2040);
x_2041 = lean_ctor_get(x_2027, 1);
lean_inc(x_2041);
lean_dec(x_2027);
x_8 = x_2040;
x_9 = x_2041;
goto block_16;
}
}
else
{
lean_object* x_2042; lean_object* x_2043; 
lean_dec(x_2022);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2042 = lean_ctor_get(x_2024, 0);
lean_inc(x_2042);
x_2043 = lean_ctor_get(x_2024, 1);
lean_inc(x_2043);
lean_dec(x_2024);
x_8 = x_2042;
x_9 = x_2043;
goto block_16;
}
}
else
{
lean_object* x_2044; lean_object* x_2045; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2044 = lean_ctor_get(x_2021, 0);
lean_inc(x_2044);
x_2045 = lean_ctor_get(x_2021, 1);
lean_inc(x_2045);
lean_dec(x_2021);
x_8 = x_2044;
x_9 = x_2045;
goto block_16;
}
}
else
{
lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; 
lean_dec(x_2007);
lean_dec(x_1984);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2046 = lean_ctor_get(x_2006, 1);
lean_inc(x_2046);
if (lean_is_exclusive(x_2006)) {
 lean_ctor_release(x_2006, 0);
 lean_ctor_release(x_2006, 1);
 x_2047 = x_2006;
} else {
 lean_dec_ref(x_2006);
 x_2047 = lean_box(0);
}
if (lean_is_scalar(x_2047)) {
 x_2048 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2048 = x_2047;
}
lean_ctor_set(x_2048, 0, x_1944);
lean_ctor_set(x_2048, 1, x_2046);
return x_2048;
}
}
else
{
lean_object* x_2049; lean_object* x_2050; 
lean_dec(x_1984);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2049 = lean_ctor_get(x_2006, 0);
lean_inc(x_2049);
x_2050 = lean_ctor_get(x_2006, 1);
lean_inc(x_2050);
lean_dec(x_2006);
x_8 = x_2049;
x_9 = x_2050;
goto block_16;
}
}
else
{
lean_object* x_2051; lean_object* x_2052; 
lean_dec(x_1988);
lean_dec(x_1986);
lean_dec(x_1984);
lean_dec(x_1973);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2051 = lean_ctor_get(x_1989, 0);
lean_inc(x_2051);
x_2052 = lean_ctor_get(x_1989, 1);
lean_inc(x_2052);
lean_dec(x_1989);
x_8 = x_2051;
x_9 = x_2052;
goto block_16;
}
}
else
{
lean_object* x_2053; lean_object* x_2054; 
lean_dec(x_1984);
lean_dec(x_1973);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2053 = lean_ctor_get(x_1985, 0);
lean_inc(x_2053);
x_2054 = lean_ctor_get(x_1985, 1);
lean_inc(x_2054);
lean_dec(x_1985);
x_8 = x_2053;
x_9 = x_2054;
goto block_16;
}
}
}
else
{
lean_object* x_2055; lean_object* x_2056; 
lean_dec(x_1973);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2055 = lean_ctor_get(x_1978, 0);
lean_inc(x_2055);
x_2056 = lean_ctor_get(x_1978, 1);
lean_inc(x_2056);
lean_dec(x_1978);
x_8 = x_2055;
x_9 = x_2056;
goto block_16;
}
}
else
{
lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; 
lean_dec(x_1973);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2057 = lean_ctor_get(x_1974, 1);
lean_inc(x_2057);
if (lean_is_exclusive(x_1974)) {
 lean_ctor_release(x_1974, 0);
 lean_ctor_release(x_1974, 1);
 x_2058 = x_1974;
} else {
 lean_dec_ref(x_1974);
 x_2058 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_1969);
if (lean_is_scalar(x_2058)) {
 x_2059 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2059 = x_2058;
}
lean_ctor_set(x_2059, 0, x_57);
lean_ctor_set(x_2059, 1, x_2057);
return x_2059;
}
}
else
{
lean_object* x_2060; lean_object* x_2061; 
lean_dec(x_1973);
lean_dec(x_1969);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2060 = lean_ctor_get(x_1974, 0);
lean_inc(x_2060);
x_2061 = lean_ctor_get(x_1974, 1);
lean_inc(x_2061);
lean_dec(x_1974);
x_8 = x_2060;
x_9 = x_2061;
goto block_16;
}
}
else
{
lean_object* x_2062; lean_object* x_2063; 
lean_dec(x_1969);
lean_dec(x_51);
lean_dec(x_1963);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2062 = lean_ctor_get(x_1970, 0);
lean_inc(x_2062);
x_2063 = lean_ctor_get(x_1970, 1);
lean_inc(x_2063);
lean_dec(x_1970);
x_8 = x_2062;
x_9 = x_2063;
goto block_16;
}
}
else
{
lean_object* x_2064; lean_object* x_2065; 
lean_dec(x_1956);
lean_dec(x_1954);
lean_dec(x_1952);
lean_dec(x_1950);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2064 = lean_ctor_get(x_1957, 0);
lean_inc(x_2064);
x_2065 = lean_ctor_get(x_1957, 1);
lean_inc(x_2065);
lean_dec(x_1957);
x_8 = x_2064;
x_9 = x_2065;
goto block_16;
}
}
else
{
lean_object* x_2066; lean_object* x_2067; 
lean_dec(x_1952);
lean_dec(x_1950);
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2066 = lean_ctor_get(x_1953, 0);
lean_inc(x_2066);
x_2067 = lean_ctor_get(x_1953, 1);
lean_inc(x_2067);
lean_dec(x_1953);
x_8 = x_2066;
x_9 = x_2067;
goto block_16;
}
}
else
{
lean_object* x_2068; lean_object* x_2069; 
lean_dec(x_1948);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2068 = lean_ctor_get(x_1949, 0);
lean_inc(x_2068);
x_2069 = lean_ctor_get(x_1949, 1);
lean_inc(x_2069);
lean_dec(x_1949);
x_8 = x_2068;
x_9 = x_2069;
goto block_16;
}
}
else
{
lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; 
lean_dec(x_1946);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2070 = lean_ctor_get(x_1945, 1);
lean_inc(x_2070);
if (lean_is_exclusive(x_1945)) {
 lean_ctor_release(x_1945, 0);
 lean_ctor_release(x_1945, 1);
 x_2071 = x_1945;
} else {
 lean_dec_ref(x_1945);
 x_2071 = lean_box(0);
}
if (lean_is_scalar(x_2071)) {
 x_2072 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2072 = x_2071;
}
lean_ctor_set(x_2072, 0, x_1944);
lean_ctor_set(x_2072, 1, x_2070);
return x_2072;
}
}
else
{
lean_object* x_2073; lean_object* x_2074; 
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2073 = lean_ctor_get(x_1945, 0);
lean_inc(x_2073);
x_2074 = lean_ctor_get(x_1945, 1);
lean_inc(x_2074);
lean_dec(x_1945);
x_8 = x_2073;
x_9 = x_2074;
goto block_16;
}
}
else
{
lean_object* x_2075; lean_object* x_2076; 
lean_dec(x_1929);
lean_dec(x_1927);
lean_dec(x_1916);
lean_dec(x_1912);
lean_dec(x_1910);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2075 = lean_ctor_get(x_1930, 0);
lean_inc(x_2075);
x_2076 = lean_ctor_get(x_1930, 1);
lean_inc(x_2076);
lean_dec(x_1930);
x_8 = x_2075;
x_9 = x_2076;
goto block_16;
}
}
else
{
lean_object* x_2077; lean_object* x_2078; 
lean_dec(x_1916);
lean_dec(x_1912);
lean_dec(x_1910);
lean_dec(x_1908);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2077 = lean_ctor_get(x_1926, 0);
lean_inc(x_2077);
x_2078 = lean_ctor_get(x_1926, 1);
lean_inc(x_2078);
lean_dec(x_1926);
x_8 = x_2077;
x_9 = x_2078;
goto block_16;
}
}
}
else
{
lean_object* x_2079; lean_object* x_2080; 
lean_dec(x_1916);
lean_dec(x_1912);
lean_dec(x_1910);
lean_dec(x_1908);
lean_dec(x_1898);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2079 = lean_ctor_get(x_1918, 0);
lean_inc(x_2079);
x_2080 = lean_ctor_get(x_1918, 1);
lean_inc(x_2080);
lean_dec(x_1918);
x_8 = x_2079;
x_9 = x_2080;
goto block_16;
}
}
else
{
lean_object* x_2081; lean_object* x_2082; 
lean_dec(x_1912);
lean_dec(x_1910);
lean_dec(x_1908);
lean_dec(x_1898);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2081 = lean_ctor_get(x_1913, 0);
lean_inc(x_2081);
x_2082 = lean_ctor_get(x_1913, 1);
lean_inc(x_2082);
lean_dec(x_1913);
x_8 = x_2081;
x_9 = x_2082;
goto block_16;
}
}
else
{
lean_object* x_2083; lean_object* x_2084; 
lean_dec(x_1908);
lean_dec(x_1907);
lean_dec(x_1898);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2083 = lean_ctor_get(x_1909, 0);
lean_inc(x_2083);
x_2084 = lean_ctor_get(x_1909, 1);
lean_inc(x_2084);
lean_dec(x_1909);
x_8 = x_2083;
x_9 = x_2084;
goto block_16;
}
}
else
{
lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; 
lean_dec(x_1905);
lean_dec(x_1904);
lean_dec(x_1898);
lean_dec(x_1897);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2085 = lean_ctor_get(x_1902, 1);
lean_inc(x_2085);
if (lean_is_exclusive(x_1902)) {
 lean_ctor_release(x_1902, 0);
 lean_ctor_release(x_1902, 1);
 x_2086 = x_1902;
} else {
 lean_dec_ref(x_1902);
 x_2086 = lean_box(0);
}
x_2087 = lean_box(0);
if (lean_is_scalar(x_2086)) {
 x_2088 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2088 = x_2086;
}
lean_ctor_set(x_2088, 0, x_2087);
lean_ctor_set(x_2088, 1, x_2085);
return x_2088;
}
}
else
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; 
lean_dec(x_1904);
lean_dec(x_1903);
lean_dec(x_1898);
lean_dec(x_1897);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2089 = lean_ctor_get(x_1902, 1);
lean_inc(x_2089);
if (lean_is_exclusive(x_1902)) {
 lean_ctor_release(x_1902, 0);
 lean_ctor_release(x_1902, 1);
 x_2090 = x_1902;
} else {
 lean_dec_ref(x_1902);
 x_2090 = lean_box(0);
}
x_2091 = lean_box(0);
if (lean_is_scalar(x_2090)) {
 x_2092 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2092 = x_2090;
}
lean_ctor_set(x_2092, 0, x_2091);
lean_ctor_set(x_2092, 1, x_2089);
return x_2092;
}
}
else
{
lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; 
lean_dec(x_1903);
lean_dec(x_1898);
lean_dec(x_1897);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2093 = lean_ctor_get(x_1902, 1);
lean_inc(x_2093);
if (lean_is_exclusive(x_1902)) {
 lean_ctor_release(x_1902, 0);
 lean_ctor_release(x_1902, 1);
 x_2094 = x_1902;
} else {
 lean_dec_ref(x_1902);
 x_2094 = lean_box(0);
}
x_2095 = lean_box(0);
if (lean_is_scalar(x_2094)) {
 x_2096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2096 = x_2094;
}
lean_ctor_set(x_2096, 0, x_2095);
lean_ctor_set(x_2096, 1, x_2093);
return x_2096;
}
}
else
{
lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; uint8_t x_2100; 
lean_dec(x_1898);
lean_dec(x_1897);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2097 = lean_ctor_get(x_1902, 0);
lean_inc(x_2097);
x_2098 = lean_ctor_get(x_1902, 1);
lean_inc(x_2098);
if (lean_is_exclusive(x_1902)) {
 lean_ctor_release(x_1902, 0);
 lean_ctor_release(x_1902, 1);
 x_2099 = x_1902;
} else {
 lean_dec_ref(x_1902);
 x_2099 = lean_box(0);
}
x_2100 = l_Lean_Exception_isInterrupt(x_2097);
if (x_2100 == 0)
{
uint8_t x_2101; 
x_2101 = l_Lean_Exception_isRuntime(x_2097);
if (x_2101 == 0)
{
lean_object* x_2102; lean_object* x_2103; 
lean_dec(x_2097);
x_2102 = lean_box(0);
if (lean_is_scalar(x_2099)) {
 x_2103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2103 = x_2099;
 lean_ctor_set_tag(x_2103, 0);
}
lean_ctor_set(x_2103, 0, x_2102);
lean_ctor_set(x_2103, 1, x_2098);
return x_2103;
}
else
{
lean_object* x_2104; 
if (lean_is_scalar(x_2099)) {
 x_2104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2104 = x_2099;
}
lean_ctor_set(x_2104, 0, x_2097);
lean_ctor_set(x_2104, 1, x_2098);
return x_2104;
}
}
else
{
lean_object* x_2105; 
if (lean_is_scalar(x_2099)) {
 x_2105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2105 = x_2099;
}
lean_ctor_set(x_2105, 0, x_2097);
lean_ctor_set(x_2105, 1, x_2098);
return x_2105;
}
}
}
else
{
lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; uint8_t x_2109; 
lean_dec(x_1898);
lean_dec(x_1897);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2106 = lean_ctor_get(x_1899, 0);
lean_inc(x_2106);
x_2107 = lean_ctor_get(x_1899, 1);
lean_inc(x_2107);
if (lean_is_exclusive(x_1899)) {
 lean_ctor_release(x_1899, 0);
 lean_ctor_release(x_1899, 1);
 x_2108 = x_1899;
} else {
 lean_dec_ref(x_1899);
 x_2108 = lean_box(0);
}
x_2109 = l_Lean_Exception_isInterrupt(x_2106);
if (x_2109 == 0)
{
uint8_t x_2110; 
x_2110 = l_Lean_Exception_isRuntime(x_2106);
if (x_2110 == 0)
{
lean_object* x_2111; lean_object* x_2112; 
lean_dec(x_2106);
x_2111 = lean_box(0);
if (lean_is_scalar(x_2108)) {
 x_2112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2112 = x_2108;
 lean_ctor_set_tag(x_2112, 0);
}
lean_ctor_set(x_2112, 0, x_2111);
lean_ctor_set(x_2112, 1, x_2107);
return x_2112;
}
else
{
lean_object* x_2113; 
if (lean_is_scalar(x_2108)) {
 x_2113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2113 = x_2108;
}
lean_ctor_set(x_2113, 0, x_2106);
lean_ctor_set(x_2113, 1, x_2107);
return x_2113;
}
}
else
{
lean_object* x_2114; 
if (lean_is_scalar(x_2108)) {
 x_2114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2114 = x_2108;
}
lean_ctor_set(x_2114, 0, x_2106);
lean_ctor_set(x_2114, 1, x_2107);
return x_2114;
}
}
}
else
{
lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; 
lean_dec(x_1895);
lean_dec(x_1894);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2115 = lean_ctor_get(x_1892, 1);
lean_inc(x_2115);
if (lean_is_exclusive(x_1892)) {
 lean_ctor_release(x_1892, 0);
 lean_ctor_release(x_1892, 1);
 x_2116 = x_1892;
} else {
 lean_dec_ref(x_1892);
 x_2116 = lean_box(0);
}
x_2117 = lean_box(0);
if (lean_is_scalar(x_2116)) {
 x_2118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2118 = x_2116;
}
lean_ctor_set(x_2118, 0, x_2117);
lean_ctor_set(x_2118, 1, x_2115);
return x_2118;
}
}
else
{
lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; 
lean_dec(x_1894);
lean_dec(x_1893);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2119 = lean_ctor_get(x_1892, 1);
lean_inc(x_2119);
if (lean_is_exclusive(x_1892)) {
 lean_ctor_release(x_1892, 0);
 lean_ctor_release(x_1892, 1);
 x_2120 = x_1892;
} else {
 lean_dec_ref(x_1892);
 x_2120 = lean_box(0);
}
x_2121 = lean_box(0);
if (lean_is_scalar(x_2120)) {
 x_2122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2122 = x_2120;
}
lean_ctor_set(x_2122, 0, x_2121);
lean_ctor_set(x_2122, 1, x_2119);
return x_2122;
}
}
else
{
lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; 
lean_dec(x_1893);
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2123 = lean_ctor_get(x_1892, 1);
lean_inc(x_2123);
if (lean_is_exclusive(x_1892)) {
 lean_ctor_release(x_1892, 0);
 lean_ctor_release(x_1892, 1);
 x_2124 = x_1892;
} else {
 lean_dec_ref(x_1892);
 x_2124 = lean_box(0);
}
x_2125 = lean_box(0);
if (lean_is_scalar(x_2124)) {
 x_2126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2126 = x_2124;
}
lean_ctor_set(x_2126, 0, x_2125);
lean_ctor_set(x_2126, 1, x_2123);
return x_2126;
}
}
else
{
lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; uint8_t x_2130; 
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2127 = lean_ctor_get(x_1892, 0);
lean_inc(x_2127);
x_2128 = lean_ctor_get(x_1892, 1);
lean_inc(x_2128);
if (lean_is_exclusive(x_1892)) {
 lean_ctor_release(x_1892, 0);
 lean_ctor_release(x_1892, 1);
 x_2129 = x_1892;
} else {
 lean_dec_ref(x_1892);
 x_2129 = lean_box(0);
}
x_2130 = l_Lean_Exception_isInterrupt(x_2127);
if (x_2130 == 0)
{
uint8_t x_2131; 
x_2131 = l_Lean_Exception_isRuntime(x_2127);
if (x_2131 == 0)
{
lean_object* x_2132; lean_object* x_2133; 
lean_dec(x_2127);
x_2132 = lean_box(0);
if (lean_is_scalar(x_2129)) {
 x_2133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2133 = x_2129;
 lean_ctor_set_tag(x_2133, 0);
}
lean_ctor_set(x_2133, 0, x_2132);
lean_ctor_set(x_2133, 1, x_2128);
return x_2133;
}
else
{
lean_object* x_2134; 
if (lean_is_scalar(x_2129)) {
 x_2134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2134 = x_2129;
}
lean_ctor_set(x_2134, 0, x_2127);
lean_ctor_set(x_2134, 1, x_2128);
return x_2134;
}
}
else
{
lean_object* x_2135; 
if (lean_is_scalar(x_2129)) {
 x_2135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2135 = x_2129;
}
lean_ctor_set(x_2135, 0, x_2127);
lean_ctor_set(x_2135, 1, x_2128);
return x_2135;
}
}
}
else
{
lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; uint8_t x_2139; 
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2136 = lean_ctor_get(x_1889, 0);
lean_inc(x_2136);
x_2137 = lean_ctor_get(x_1889, 1);
lean_inc(x_2137);
if (lean_is_exclusive(x_1889)) {
 lean_ctor_release(x_1889, 0);
 lean_ctor_release(x_1889, 1);
 x_2138 = x_1889;
} else {
 lean_dec_ref(x_1889);
 x_2138 = lean_box(0);
}
x_2139 = l_Lean_Exception_isInterrupt(x_2136);
if (x_2139 == 0)
{
uint8_t x_2140; 
x_2140 = l_Lean_Exception_isRuntime(x_2136);
if (x_2140 == 0)
{
lean_object* x_2141; lean_object* x_2142; 
lean_dec(x_2136);
x_2141 = lean_box(0);
if (lean_is_scalar(x_2138)) {
 x_2142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2142 = x_2138;
 lean_ctor_set_tag(x_2142, 0);
}
lean_ctor_set(x_2142, 0, x_2141);
lean_ctor_set(x_2142, 1, x_2137);
return x_2142;
}
else
{
lean_object* x_2143; 
if (lean_is_scalar(x_2138)) {
 x_2143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2143 = x_2138;
}
lean_ctor_set(x_2143, 0, x_2136);
lean_ctor_set(x_2143, 1, x_2137);
return x_2143;
}
}
else
{
lean_object* x_2144; 
if (lean_is_scalar(x_2138)) {
 x_2144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2144 = x_2138;
}
lean_ctor_set(x_2144, 0, x_2136);
lean_ctor_set(x_2144, 1, x_2137);
return x_2144;
}
}
}
}
else
{
lean_object* x_2145; lean_object* x_2146; 
lean_dec(x_40);
lean_dec(x_33);
x_2145 = lean_ctor_get(x_1879, 1);
lean_inc(x_2145);
lean_dec(x_1879);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2146 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_2145);
if (lean_obj_tag(x_2146) == 0)
{
lean_object* x_2147; 
x_2147 = lean_ctor_get(x_2146, 0);
lean_inc(x_2147);
if (lean_obj_tag(x_2147) == 0)
{
lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; 
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_free_object(x_43);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2148 = lean_ctor_get(x_2146, 1);
lean_inc(x_2148);
if (lean_is_exclusive(x_2146)) {
 lean_ctor_release(x_2146, 0);
 lean_ctor_release(x_2146, 1);
 x_2149 = x_2146;
} else {
 lean_dec_ref(x_2146);
 x_2149 = lean_box(0);
}
x_2150 = lean_box(0);
if (lean_is_scalar(x_2149)) {
 x_2151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2151 = x_2149;
}
lean_ctor_set(x_2151, 0, x_2150);
lean_ctor_set(x_2151, 1, x_2148);
return x_2151;
}
else
{
lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; 
x_2152 = lean_ctor_get(x_2146, 1);
lean_inc(x_2152);
lean_dec(x_2146);
x_2153 = lean_ctor_get(x_2147, 0);
lean_inc(x_2153);
if (lean_is_exclusive(x_2147)) {
 lean_ctor_release(x_2147, 0);
 x_2154 = x_2147;
} else {
 lean_dec_ref(x_2147);
 x_2154 = lean_box(0);
}
if (lean_is_scalar(x_2154)) {
 x_2155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2155 = x_2154;
}
lean_ctor_set(x_2155, 0, x_1877);
lean_ctor_set(x_57, 0, x_1878);
lean_ctor_set(x_43, 0, x_55);
x_2156 = lean_box(0);
x_2157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2157, 0, x_2153);
x_2158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2158, 0, x_1);
x_2159 = lean_box(0);
x_2160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2160, 0, x_2158);
lean_ctor_set(x_2160, 1, x_2159);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_2160);
lean_ctor_set(x_51, 0, x_2157);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_2156);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_43);
x_2161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2161, 0, x_57);
lean_ctor_set(x_2161, 1, x_31);
x_2162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2162, 0, x_2155);
lean_ctor_set(x_2162, 1, x_2161);
x_2163 = lean_array_mk(x_2162);
x_2164 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2165 = l_Lean_Meta_mkAppOptM(x_2164, x_2163, x_3, x_4, x_5, x_6, x_2152);
if (lean_obj_tag(x_2165) == 0)
{
lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; 
x_2166 = lean_ctor_get(x_2165, 0);
lean_inc(x_2166);
x_2167 = lean_ctor_get(x_2165, 1);
lean_inc(x_2167);
lean_dec(x_2165);
x_2168 = l_Lean_Meta_expandCoe(x_2166, x_3, x_4, x_5, x_6, x_2167);
if (lean_obj_tag(x_2168) == 0)
{
lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; 
x_2169 = lean_ctor_get(x_2168, 0);
lean_inc(x_2169);
x_2170 = lean_ctor_get(x_2168, 1);
lean_inc(x_2170);
lean_dec(x_2168);
x_2171 = lean_box(0);
x_2172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2172, 0, x_2169);
lean_ctor_set(x_2172, 1, x_2171);
x_17 = x_2172;
x_18 = x_2170;
goto block_30;
}
else
{
lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; uint8_t x_2176; 
x_2173 = lean_ctor_get(x_2168, 0);
lean_inc(x_2173);
x_2174 = lean_ctor_get(x_2168, 1);
lean_inc(x_2174);
if (lean_is_exclusive(x_2168)) {
 lean_ctor_release(x_2168, 0);
 lean_ctor_release(x_2168, 1);
 x_2175 = x_2168;
} else {
 lean_dec_ref(x_2168);
 x_2175 = lean_box(0);
}
x_2176 = l_Lean_Exception_isInterrupt(x_2173);
if (x_2176 == 0)
{
uint8_t x_2177; 
x_2177 = l_Lean_Exception_isRuntime(x_2173);
if (x_2177 == 0)
{
lean_object* x_2178; 
lean_dec(x_2175);
lean_dec(x_2173);
x_2178 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_2178;
x_18 = x_2174;
goto block_30;
}
else
{
lean_object* x_2179; 
if (lean_is_scalar(x_2175)) {
 x_2179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2179 = x_2175;
}
lean_ctor_set(x_2179, 0, x_2173);
lean_ctor_set(x_2179, 1, x_2174);
return x_2179;
}
}
else
{
lean_object* x_2180; 
if (lean_is_scalar(x_2175)) {
 x_2180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2180 = x_2175;
}
lean_ctor_set(x_2180, 0, x_2173);
lean_ctor_set(x_2180, 1, x_2174);
return x_2180;
}
}
}
else
{
lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; uint8_t x_2184; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2181 = lean_ctor_get(x_2165, 0);
lean_inc(x_2181);
x_2182 = lean_ctor_get(x_2165, 1);
lean_inc(x_2182);
if (lean_is_exclusive(x_2165)) {
 lean_ctor_release(x_2165, 0);
 lean_ctor_release(x_2165, 1);
 x_2183 = x_2165;
} else {
 lean_dec_ref(x_2165);
 x_2183 = lean_box(0);
}
x_2184 = l_Lean_Exception_isInterrupt(x_2181);
if (x_2184 == 0)
{
uint8_t x_2185; 
x_2185 = l_Lean_Exception_isRuntime(x_2181);
if (x_2185 == 0)
{
lean_object* x_2186; 
lean_dec(x_2183);
lean_dec(x_2181);
x_2186 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_2186;
x_18 = x_2182;
goto block_30;
}
else
{
lean_object* x_2187; 
if (lean_is_scalar(x_2183)) {
 x_2187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2187 = x_2183;
}
lean_ctor_set(x_2187, 0, x_2181);
lean_ctor_set(x_2187, 1, x_2182);
return x_2187;
}
}
else
{
lean_object* x_2188; 
if (lean_is_scalar(x_2183)) {
 x_2188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2188 = x_2183;
}
lean_ctor_set(x_2188, 0, x_2181);
lean_ctor_set(x_2188, 1, x_2182);
return x_2188;
}
}
}
}
else
{
lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; 
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_free_object(x_43);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2189 = lean_ctor_get(x_2146, 0);
lean_inc(x_2189);
x_2190 = lean_ctor_get(x_2146, 1);
lean_inc(x_2190);
if (lean_is_exclusive(x_2146)) {
 lean_ctor_release(x_2146, 0);
 lean_ctor_release(x_2146, 1);
 x_2191 = x_2146;
} else {
 lean_dec_ref(x_2146);
 x_2191 = lean_box(0);
}
if (lean_is_scalar(x_2191)) {
 x_2192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2192 = x_2191;
}
lean_ctor_set(x_2192, 0, x_2189);
lean_ctor_set(x_2192, 1, x_2190);
return x_2192;
}
}
}
else
{
lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; 
lean_dec(x_1878);
lean_dec(x_1877);
lean_free_object(x_57);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2193 = lean_ctor_get(x_1879, 0);
lean_inc(x_2193);
x_2194 = lean_ctor_get(x_1879, 1);
lean_inc(x_2194);
if (lean_is_exclusive(x_1879)) {
 lean_ctor_release(x_1879, 0);
 lean_ctor_release(x_1879, 1);
 x_2195 = x_1879;
} else {
 lean_dec_ref(x_1879);
 x_2195 = lean_box(0);
}
if (lean_is_scalar(x_2195)) {
 x_2196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2196 = x_2195;
}
lean_ctor_set(x_2196, 0, x_2193);
lean_ctor_set(x_2196, 1, x_2194);
return x_2196;
}
}
}
else
{
lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; 
x_2197 = lean_ctor_get(x_57, 0);
lean_inc(x_2197);
lean_dec(x_57);
x_2198 = lean_ctor_get(x_56, 1);
lean_inc(x_2198);
lean_dec(x_56);
x_2199 = lean_ctor_get(x_2197, 0);
lean_inc(x_2199);
x_2200 = lean_ctor_get(x_2197, 1);
lean_inc(x_2200);
if (lean_is_exclusive(x_2197)) {
 lean_ctor_release(x_2197, 0);
 lean_ctor_release(x_2197, 1);
 x_2201 = x_2197;
} else {
 lean_dec_ref(x_2197);
 x_2201 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
lean_inc(x_2199);
x_2202 = l_Lean_Meta_isExprDefEq(x_2199, x_54, x_3, x_4, x_5, x_6, x_2198);
if (lean_obj_tag(x_2202) == 0)
{
lean_object* x_2203; uint8_t x_2204; 
x_2203 = lean_ctor_get(x_2202, 0);
lean_inc(x_2203);
x_2204 = lean_unbox(x_2203);
lean_dec(x_2203);
if (x_2204 == 0)
{
lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; uint8_t x_2209; 
lean_free_object(x_43);
x_2205 = lean_ctor_get(x_2202, 1);
lean_inc(x_2205);
if (lean_is_exclusive(x_2202)) {
 lean_ctor_release(x_2202, 0);
 lean_ctor_release(x_2202, 1);
 x_2206 = x_2202;
} else {
 lean_dec_ref(x_2202);
 x_2206 = lean_box(0);
}
x_2207 = lean_ctor_get(x_5, 2);
lean_inc(x_2207);
x_2208 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_2209 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2207, x_2208);
lean_dec(x_2207);
if (x_2209 == 0)
{
lean_object* x_2210; lean_object* x_2211; 
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2210 = lean_box(0);
if (lean_is_scalar(x_2206)) {
 x_2211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2211 = x_2206;
}
lean_ctor_set(x_2211, 0, x_2210);
lean_ctor_set(x_2211, 1, x_2205);
return x_2211;
}
else
{
lean_object* x_2212; 
lean_dec(x_2206);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2199);
x_2212 = lean_infer_type(x_2199, x_3, x_4, x_5, x_6, x_2205);
if (lean_obj_tag(x_2212) == 0)
{
lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; 
x_2213 = lean_ctor_get(x_2212, 0);
lean_inc(x_2213);
x_2214 = lean_ctor_get(x_2212, 1);
lean_inc(x_2214);
lean_dec(x_2212);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2215 = lean_whnf(x_2213, x_3, x_4, x_5, x_6, x_2214);
if (lean_obj_tag(x_2215) == 0)
{
lean_object* x_2216; 
x_2216 = lean_ctor_get(x_2215, 0);
lean_inc(x_2216);
if (lean_obj_tag(x_2216) == 7)
{
lean_object* x_2217; 
x_2217 = lean_ctor_get(x_2216, 1);
lean_inc(x_2217);
if (lean_obj_tag(x_2217) == 3)
{
lean_object* x_2218; 
x_2218 = lean_ctor_get(x_2216, 2);
lean_inc(x_2218);
lean_dec(x_2216);
if (lean_obj_tag(x_2218) == 3)
{
lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; 
x_2219 = lean_ctor_get(x_2215, 1);
lean_inc(x_2219);
lean_dec(x_2215);
x_2220 = lean_ctor_get(x_2217, 0);
lean_inc(x_2220);
lean_dec(x_2217);
x_2221 = lean_ctor_get(x_2218, 0);
lean_inc(x_2221);
lean_dec(x_2218);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_2222 = lean_infer_type(x_54, x_3, x_4, x_5, x_6, x_2219);
if (lean_obj_tag(x_2222) == 0)
{
lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; 
x_2223 = lean_ctor_get(x_2222, 0);
lean_inc(x_2223);
x_2224 = lean_ctor_get(x_2222, 1);
lean_inc(x_2224);
lean_dec(x_2222);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2225 = lean_whnf(x_2223, x_3, x_4, x_5, x_6, x_2224);
if (lean_obj_tag(x_2225) == 0)
{
lean_object* x_2226; 
x_2226 = lean_ctor_get(x_2225, 0);
lean_inc(x_2226);
if (lean_obj_tag(x_2226) == 7)
{
lean_object* x_2227; 
x_2227 = lean_ctor_get(x_2226, 1);
lean_inc(x_2227);
if (lean_obj_tag(x_2227) == 3)
{
lean_object* x_2228; 
x_2228 = lean_ctor_get(x_2226, 2);
lean_inc(x_2228);
lean_dec(x_2226);
if (lean_obj_tag(x_2228) == 3)
{
lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; 
x_2229 = lean_ctor_get(x_2225, 1);
lean_inc(x_2229);
lean_dec(x_2225);
x_2230 = lean_ctor_get(x_2227, 0);
lean_inc(x_2230);
lean_dec(x_2227);
x_2231 = lean_ctor_get(x_2228, 0);
lean_inc(x_2231);
lean_dec(x_2228);
x_2232 = l_Lean_Meta_decLevel(x_2220, x_3, x_4, x_5, x_6, x_2229);
if (lean_obj_tag(x_2232) == 0)
{
lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; 
x_2233 = lean_ctor_get(x_2232, 0);
lean_inc(x_2233);
x_2234 = lean_ctor_get(x_2232, 1);
lean_inc(x_2234);
if (lean_is_exclusive(x_2232)) {
 lean_ctor_release(x_2232, 0);
 lean_ctor_release(x_2232, 1);
 x_2235 = x_2232;
} else {
 lean_dec_ref(x_2232);
 x_2235 = lean_box(0);
}
x_2236 = l_Lean_Meta_decLevel(x_2230, x_3, x_4, x_5, x_6, x_2234);
if (lean_obj_tag(x_2236) == 0)
{
lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; uint8_t x_2240; lean_object* x_2241; 
x_2237 = lean_ctor_get(x_2236, 0);
lean_inc(x_2237);
x_2238 = lean_ctor_get(x_2236, 1);
lean_inc(x_2238);
if (lean_is_exclusive(x_2236)) {
 lean_ctor_release(x_2236, 0);
 lean_ctor_release(x_2236, 1);
 x_2239 = x_2236;
} else {
 lean_dec_ref(x_2236);
 x_2239 = lean_box(0);
}
x_2240 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2233);
x_2241 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_2233, x_2237, x_2240, x_3, x_4, x_5, x_6, x_2238);
if (lean_obj_tag(x_2241) == 0)
{
lean_object* x_2242; uint8_t x_2243; 
x_2242 = lean_ctor_get(x_2241, 0);
lean_inc(x_2242);
x_2243 = lean_unbox(x_2242);
lean_dec(x_2242);
if (x_2243 == 0)
{
lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; 
lean_dec(x_2239);
lean_dec(x_2235);
lean_dec(x_2233);
lean_dec(x_2231);
lean_dec(x_2221);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2244 = lean_ctor_get(x_2241, 1);
lean_inc(x_2244);
if (lean_is_exclusive(x_2241)) {
 lean_ctor_release(x_2241, 0);
 lean_ctor_release(x_2241, 1);
 x_2245 = x_2241;
} else {
 lean_dec_ref(x_2241);
 x_2245 = lean_box(0);
}
x_2246 = lean_box(0);
if (lean_is_scalar(x_2245)) {
 x_2247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2247 = x_2245;
}
lean_ctor_set(x_2247, 0, x_2246);
lean_ctor_set(x_2247, 1, x_2244);
return x_2247;
}
else
{
lean_object* x_2248; lean_object* x_2249; 
x_2248 = lean_ctor_get(x_2241, 1);
lean_inc(x_2248);
lean_dec(x_2241);
x_2249 = l_Lean_Meta_decLevel(x_2221, x_3, x_4, x_5, x_6, x_2248);
if (lean_obj_tag(x_2249) == 0)
{
lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; 
x_2250 = lean_ctor_get(x_2249, 0);
lean_inc(x_2250);
x_2251 = lean_ctor_get(x_2249, 1);
lean_inc(x_2251);
if (lean_is_exclusive(x_2249)) {
 lean_ctor_release(x_2249, 0);
 lean_ctor_release(x_2249, 1);
 x_2252 = x_2249;
} else {
 lean_dec_ref(x_2249);
 x_2252 = lean_box(0);
}
x_2253 = l_Lean_Meta_decLevel(x_2231, x_3, x_4, x_5, x_6, x_2251);
if (lean_obj_tag(x_2253) == 0)
{
lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; 
x_2254 = lean_ctor_get(x_2253, 0);
lean_inc(x_2254);
x_2255 = lean_ctor_get(x_2253, 1);
lean_inc(x_2255);
if (lean_is_exclusive(x_2253)) {
 lean_ctor_release(x_2253, 0);
 lean_ctor_release(x_2253, 1);
 x_2256 = x_2253;
} else {
 lean_dec_ref(x_2253);
 x_2256 = lean_box(0);
}
x_2257 = lean_box(0);
if (lean_is_scalar(x_2256)) {
 x_2258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2258 = x_2256;
 lean_ctor_set_tag(x_2258, 1);
}
lean_ctor_set(x_2258, 0, x_2254);
lean_ctor_set(x_2258, 1, x_2257);
if (lean_is_scalar(x_2252)) {
 x_2259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2259 = x_2252;
 lean_ctor_set_tag(x_2259, 1);
}
lean_ctor_set(x_2259, 0, x_2250);
lean_ctor_set(x_2259, 1, x_2258);
if (lean_is_scalar(x_2239)) {
 x_2260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2260 = x_2239;
 lean_ctor_set_tag(x_2260, 1);
}
lean_ctor_set(x_2260, 0, x_2233);
lean_ctor_set(x_2260, 1, x_2259);
x_2261 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2262 = l_Lean_Expr_const___override(x_2261, x_2260);
lean_inc(x_54);
if (lean_is_scalar(x_2235)) {
 x_2263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2263 = x_2235;
 lean_ctor_set_tag(x_2263, 1);
}
lean_ctor_set(x_2263, 0, x_54);
lean_ctor_set(x_2263, 1, x_2257);
lean_inc(x_2199);
if (lean_is_scalar(x_2201)) {
 x_2264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2264 = x_2201;
 lean_ctor_set_tag(x_2264, 1);
}
lean_ctor_set(x_2264, 0, x_2199);
lean_ctor_set(x_2264, 1, x_2263);
x_2265 = lean_array_mk(x_2264);
x_2266 = l_Lean_mkAppN(x_2262, x_2265);
lean_dec(x_2265);
x_2267 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2268 = l_Lean_Meta_trySynthInstance(x_2266, x_2267, x_3, x_4, x_5, x_6, x_2255);
if (lean_obj_tag(x_2268) == 0)
{
lean_object* x_2269; 
x_2269 = lean_ctor_get(x_2268, 0);
lean_inc(x_2269);
if (lean_obj_tag(x_2269) == 1)
{
lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; 
x_2270 = lean_ctor_get(x_2268, 1);
lean_inc(x_2270);
lean_dec(x_2268);
x_2271 = lean_ctor_get(x_2269, 0);
lean_inc(x_2271);
lean_dec(x_2269);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2200);
x_2272 = l_Lean_Meta_getDecLevel(x_2200, x_3, x_4, x_5, x_6, x_2270);
if (lean_obj_tag(x_2272) == 0)
{
lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; 
x_2273 = lean_ctor_get(x_2272, 0);
lean_inc(x_2273);
x_2274 = lean_ctor_get(x_2272, 1);
lean_inc(x_2274);
if (lean_is_exclusive(x_2272)) {
 lean_ctor_release(x_2272, 0);
 lean_ctor_release(x_2272, 1);
 x_2275 = x_2272;
} else {
 lean_dec_ref(x_2272);
 x_2275 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2276 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_2274);
if (lean_obj_tag(x_2276) == 0)
{
lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; 
x_2277 = lean_ctor_get(x_2276, 0);
lean_inc(x_2277);
x_2278 = lean_ctor_get(x_2276, 1);
lean_inc(x_2278);
if (lean_is_exclusive(x_2276)) {
 lean_ctor_release(x_2276, 0);
 lean_ctor_release(x_2276, 1);
 x_2279 = x_2276;
} else {
 lean_dec_ref(x_2276);
 x_2279 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_2280 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_2278);
if (lean_obj_tag(x_2280) == 0)
{
lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; 
x_2281 = lean_ctor_get(x_2280, 0);
lean_inc(x_2281);
x_2282 = lean_ctor_get(x_2280, 1);
lean_inc(x_2282);
if (lean_is_exclusive(x_2280)) {
 lean_ctor_release(x_2280, 0);
 lean_ctor_release(x_2280, 1);
 x_2283 = x_2280;
} else {
 lean_dec_ref(x_2280);
 x_2283 = lean_box(0);
}
if (lean_is_scalar(x_2283)) {
 x_2284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2284 = x_2283;
 lean_ctor_set_tag(x_2284, 1);
}
lean_ctor_set(x_2284, 0, x_2281);
lean_ctor_set(x_2284, 1, x_2257);
if (lean_is_scalar(x_2279)) {
 x_2285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2285 = x_2279;
 lean_ctor_set_tag(x_2285, 1);
}
lean_ctor_set(x_2285, 0, x_2277);
lean_ctor_set(x_2285, 1, x_2284);
if (lean_is_scalar(x_2275)) {
 x_2286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2286 = x_2275;
 lean_ctor_set_tag(x_2286, 1);
}
lean_ctor_set(x_2286, 0, x_2273);
lean_ctor_set(x_2286, 1, x_2285);
x_2287 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_2286);
x_2288 = l_Lean_Expr_const___override(x_2287, x_2286);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_2257);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_2200);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_2200);
lean_inc(x_2271);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_2271);
lean_inc(x_54);
x_2289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2289, 0, x_54);
lean_ctor_set(x_2289, 1, x_31);
lean_inc(x_2199);
x_2290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2290, 0, x_2199);
lean_ctor_set(x_2290, 1, x_2289);
x_2291 = lean_array_mk(x_2290);
x_2292 = l_Lean_mkAppN(x_2288, x_2291);
lean_dec(x_2291);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2292);
x_2293 = lean_infer_type(x_2292, x_3, x_4, x_5, x_6, x_2282);
if (lean_obj_tag(x_2293) == 0)
{
lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; 
x_2294 = lean_ctor_get(x_2293, 0);
lean_inc(x_2294);
x_2295 = lean_ctor_get(x_2293, 1);
lean_inc(x_2295);
if (lean_is_exclusive(x_2293)) {
 lean_ctor_release(x_2293, 0);
 lean_ctor_release(x_2293, 1);
 x_2296 = x_2293;
} else {
 lean_dec_ref(x_2293);
 x_2296 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_2297 = l_Lean_Meta_isExprDefEq(x_33, x_2294, x_3, x_4, x_5, x_6, x_2295);
if (lean_obj_tag(x_2297) == 0)
{
lean_object* x_2298; uint8_t x_2299; 
x_2298 = lean_ctor_get(x_2297, 0);
lean_inc(x_2298);
x_2299 = lean_unbox(x_2298);
lean_dec(x_2298);
if (x_2299 == 0)
{
lean_object* x_2300; lean_object* x_2301; 
lean_dec(x_2292);
x_2300 = lean_ctor_get(x_2297, 1);
lean_inc(x_2300);
lean_dec(x_2297);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_2301 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_2300);
if (lean_obj_tag(x_2301) == 0)
{
lean_object* x_2302; 
x_2302 = lean_ctor_get(x_2301, 0);
lean_inc(x_2302);
if (lean_obj_tag(x_2302) == 0)
{
lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; 
lean_dec(x_2296);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2303 = lean_ctor_get(x_2301, 1);
lean_inc(x_2303);
if (lean_is_exclusive(x_2301)) {
 lean_ctor_release(x_2301, 0);
 lean_ctor_release(x_2301, 1);
 x_2304 = x_2301;
} else {
 lean_dec_ref(x_2301);
 x_2304 = lean_box(0);
}
if (lean_is_scalar(x_2304)) {
 x_2305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2305 = x_2304;
}
lean_ctor_set(x_2305, 0, x_2267);
lean_ctor_set(x_2305, 1, x_2303);
return x_2305;
}
else
{
lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; 
x_2306 = lean_ctor_get(x_2301, 1);
lean_inc(x_2306);
lean_dec(x_2301);
x_2307 = lean_ctor_get(x_2302, 0);
lean_inc(x_2307);
lean_dec(x_2302);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2200);
x_2308 = l_Lean_Meta_getLevel(x_2200, x_3, x_4, x_5, x_6, x_2306);
if (lean_obj_tag(x_2308) == 0)
{
lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; 
x_2309 = lean_ctor_get(x_2308, 0);
lean_inc(x_2309);
x_2310 = lean_ctor_get(x_2308, 1);
lean_inc(x_2310);
if (lean_is_exclusive(x_2308)) {
 lean_ctor_release(x_2308, 0);
 lean_ctor_release(x_2308, 1);
 x_2311 = x_2308;
} else {
 lean_dec_ref(x_2308);
 x_2311 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_2312 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_2310);
if (lean_obj_tag(x_2312) == 0)
{
lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; uint8_t x_2327; lean_object* x_2328; lean_object* x_2329; 
x_2313 = lean_ctor_get(x_2312, 0);
lean_inc(x_2313);
x_2314 = lean_ctor_get(x_2312, 1);
lean_inc(x_2314);
if (lean_is_exclusive(x_2312)) {
 lean_ctor_release(x_2312, 0);
 lean_ctor_release(x_2312, 1);
 x_2315 = x_2312;
} else {
 lean_dec_ref(x_2312);
 x_2315 = lean_box(0);
}
if (lean_is_scalar(x_2315)) {
 x_2316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2316 = x_2315;
 lean_ctor_set_tag(x_2316, 1);
}
lean_ctor_set(x_2316, 0, x_2313);
lean_ctor_set(x_2316, 1, x_2257);
if (lean_is_scalar(x_2311)) {
 x_2317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2317 = x_2311;
 lean_ctor_set_tag(x_2317, 1);
}
lean_ctor_set(x_2317, 0, x_2309);
lean_ctor_set(x_2317, 1, x_2316);
x_2318 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_2319 = l_Lean_Expr_const___override(x_2318, x_2317);
lean_inc(x_55);
if (lean_is_scalar(x_2296)) {
 x_2320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2320 = x_2296;
 lean_ctor_set_tag(x_2320, 1);
}
lean_ctor_set(x_2320, 0, x_55);
lean_ctor_set(x_2320, 1, x_2257);
x_2321 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_2322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2322, 0, x_2321);
lean_ctor_set(x_2322, 1, x_2320);
lean_inc(x_2200);
x_2323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2323, 0, x_2200);
lean_ctor_set(x_2323, 1, x_2322);
x_2324 = lean_array_mk(x_2323);
x_2325 = l_Lean_mkAppN(x_2319, x_2324);
lean_dec(x_2324);
x_2326 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_2327 = 0;
lean_inc(x_2200);
x_2328 = l_Lean_Expr_forallE___override(x_2326, x_2200, x_2325, x_2327);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2329 = l_Lean_Meta_trySynthInstance(x_2328, x_2267, x_3, x_4, x_5, x_6, x_2314);
if (lean_obj_tag(x_2329) == 0)
{
lean_object* x_2330; 
x_2330 = lean_ctor_get(x_2329, 0);
lean_inc(x_2330);
if (lean_obj_tag(x_2330) == 1)
{
lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; 
x_2331 = lean_ctor_get(x_2329, 1);
lean_inc(x_2331);
lean_dec(x_2329);
x_2332 = lean_ctor_get(x_2330, 0);
lean_inc(x_2332);
lean_dec(x_2330);
x_2333 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_2334 = l_Lean_Expr_const___override(x_2333, x_2286);
x_2335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2335, 0, x_2307);
lean_ctor_set(x_2335, 1, x_51);
x_2336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2336, 0, x_2332);
lean_ctor_set(x_2336, 1, x_2335);
x_2337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2337, 0, x_2271);
lean_ctor_set(x_2337, 1, x_2336);
x_2338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2338, 0, x_55);
lean_ctor_set(x_2338, 1, x_2337);
x_2339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2339, 0, x_2200);
lean_ctor_set(x_2339, 1, x_2338);
x_2340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2340, 0, x_54);
lean_ctor_set(x_2340, 1, x_2339);
x_2341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2341, 0, x_2199);
lean_ctor_set(x_2341, 1, x_2340);
x_2342 = lean_array_mk(x_2341);
x_2343 = l_Lean_mkAppN(x_2334, x_2342);
lean_dec(x_2342);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2344 = l_Lean_Meta_expandCoe(x_2343, x_3, x_4, x_5, x_6, x_2331);
if (lean_obj_tag(x_2344) == 0)
{
lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; 
x_2345 = lean_ctor_get(x_2344, 0);
lean_inc(x_2345);
x_2346 = lean_ctor_get(x_2344, 1);
lean_inc(x_2346);
lean_dec(x_2344);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2345);
x_2347 = lean_infer_type(x_2345, x_3, x_4, x_5, x_6, x_2346);
if (lean_obj_tag(x_2347) == 0)
{
lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; 
x_2348 = lean_ctor_get(x_2347, 0);
lean_inc(x_2348);
x_2349 = lean_ctor_get(x_2347, 1);
lean_inc(x_2349);
lean_dec(x_2347);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2350 = l_Lean_Meta_isExprDefEq(x_33, x_2348, x_3, x_4, x_5, x_6, x_2349);
if (lean_obj_tag(x_2350) == 0)
{
lean_object* x_2351; uint8_t x_2352; 
x_2351 = lean_ctor_get(x_2350, 0);
lean_inc(x_2351);
x_2352 = lean_unbox(x_2351);
lean_dec(x_2351);
if (x_2352 == 0)
{
lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; 
lean_dec(x_2345);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2353 = lean_ctor_get(x_2350, 1);
lean_inc(x_2353);
if (lean_is_exclusive(x_2350)) {
 lean_ctor_release(x_2350, 0);
 lean_ctor_release(x_2350, 1);
 x_2354 = x_2350;
} else {
 lean_dec_ref(x_2350);
 x_2354 = lean_box(0);
}
if (lean_is_scalar(x_2354)) {
 x_2355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2355 = x_2354;
}
lean_ctor_set(x_2355, 0, x_2267);
lean_ctor_set(x_2355, 1, x_2353);
return x_2355;
}
else
{
lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; 
x_2356 = lean_ctor_get(x_2350, 1);
lean_inc(x_2356);
lean_dec(x_2350);
x_2357 = lean_box(0);
x_2358 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2345, x_2357, x_3, x_4, x_5, x_6, x_2356);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2359 = lean_ctor_get(x_2358, 0);
lean_inc(x_2359);
x_2360 = lean_ctor_get(x_2358, 1);
lean_inc(x_2360);
if (lean_is_exclusive(x_2358)) {
 lean_ctor_release(x_2358, 0);
 lean_ctor_release(x_2358, 1);
 x_2361 = x_2358;
} else {
 lean_dec_ref(x_2358);
 x_2361 = lean_box(0);
}
if (lean_is_scalar(x_2361)) {
 x_2362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2362 = x_2361;
}
lean_ctor_set(x_2362, 0, x_2359);
lean_ctor_set(x_2362, 1, x_2360);
return x_2362;
}
}
else
{
lean_object* x_2363; lean_object* x_2364; 
lean_dec(x_2345);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2363 = lean_ctor_get(x_2350, 0);
lean_inc(x_2363);
x_2364 = lean_ctor_get(x_2350, 1);
lean_inc(x_2364);
lean_dec(x_2350);
x_8 = x_2363;
x_9 = x_2364;
goto block_16;
}
}
else
{
lean_object* x_2365; lean_object* x_2366; 
lean_dec(x_2345);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2365 = lean_ctor_get(x_2347, 0);
lean_inc(x_2365);
x_2366 = lean_ctor_get(x_2347, 1);
lean_inc(x_2366);
lean_dec(x_2347);
x_8 = x_2365;
x_9 = x_2366;
goto block_16;
}
}
else
{
lean_object* x_2367; lean_object* x_2368; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2367 = lean_ctor_get(x_2344, 0);
lean_inc(x_2367);
x_2368 = lean_ctor_get(x_2344, 1);
lean_inc(x_2368);
lean_dec(x_2344);
x_8 = x_2367;
x_9 = x_2368;
goto block_16;
}
}
else
{
lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; 
lean_dec(x_2330);
lean_dec(x_2307);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2369 = lean_ctor_get(x_2329, 1);
lean_inc(x_2369);
if (lean_is_exclusive(x_2329)) {
 lean_ctor_release(x_2329, 0);
 lean_ctor_release(x_2329, 1);
 x_2370 = x_2329;
} else {
 lean_dec_ref(x_2329);
 x_2370 = lean_box(0);
}
if (lean_is_scalar(x_2370)) {
 x_2371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2371 = x_2370;
}
lean_ctor_set(x_2371, 0, x_2267);
lean_ctor_set(x_2371, 1, x_2369);
return x_2371;
}
}
else
{
lean_object* x_2372; lean_object* x_2373; 
lean_dec(x_2307);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2372 = lean_ctor_get(x_2329, 0);
lean_inc(x_2372);
x_2373 = lean_ctor_get(x_2329, 1);
lean_inc(x_2373);
lean_dec(x_2329);
x_8 = x_2372;
x_9 = x_2373;
goto block_16;
}
}
else
{
lean_object* x_2374; lean_object* x_2375; 
lean_dec(x_2311);
lean_dec(x_2309);
lean_dec(x_2307);
lean_dec(x_2296);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2374 = lean_ctor_get(x_2312, 0);
lean_inc(x_2374);
x_2375 = lean_ctor_get(x_2312, 1);
lean_inc(x_2375);
lean_dec(x_2312);
x_8 = x_2374;
x_9 = x_2375;
goto block_16;
}
}
else
{
lean_object* x_2376; lean_object* x_2377; 
lean_dec(x_2307);
lean_dec(x_2296);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2376 = lean_ctor_get(x_2308, 0);
lean_inc(x_2376);
x_2377 = lean_ctor_get(x_2308, 1);
lean_inc(x_2377);
lean_dec(x_2308);
x_8 = x_2376;
x_9 = x_2377;
goto block_16;
}
}
}
else
{
lean_object* x_2378; lean_object* x_2379; 
lean_dec(x_2296);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2378 = lean_ctor_get(x_2301, 0);
lean_inc(x_2378);
x_2379 = lean_ctor_get(x_2301, 1);
lean_inc(x_2379);
lean_dec(x_2301);
x_8 = x_2378;
x_9 = x_2379;
goto block_16;
}
}
else
{
lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; 
lean_dec(x_2296);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2380 = lean_ctor_get(x_2297, 1);
lean_inc(x_2380);
if (lean_is_exclusive(x_2297)) {
 lean_ctor_release(x_2297, 0);
 lean_ctor_release(x_2297, 1);
 x_2381 = x_2297;
} else {
 lean_dec_ref(x_2297);
 x_2381 = lean_box(0);
}
x_2382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2382, 0, x_2292);
if (lean_is_scalar(x_2381)) {
 x_2383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2383 = x_2381;
}
lean_ctor_set(x_2383, 0, x_2382);
lean_ctor_set(x_2383, 1, x_2380);
return x_2383;
}
}
else
{
lean_object* x_2384; lean_object* x_2385; 
lean_dec(x_2296);
lean_dec(x_2292);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2384 = lean_ctor_get(x_2297, 0);
lean_inc(x_2384);
x_2385 = lean_ctor_get(x_2297, 1);
lean_inc(x_2385);
lean_dec(x_2297);
x_8 = x_2384;
x_9 = x_2385;
goto block_16;
}
}
else
{
lean_object* x_2386; lean_object* x_2387; 
lean_dec(x_2292);
lean_dec(x_51);
lean_dec(x_2286);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2386 = lean_ctor_get(x_2293, 0);
lean_inc(x_2386);
x_2387 = lean_ctor_get(x_2293, 1);
lean_inc(x_2387);
lean_dec(x_2293);
x_8 = x_2386;
x_9 = x_2387;
goto block_16;
}
}
else
{
lean_object* x_2388; lean_object* x_2389; 
lean_dec(x_2279);
lean_dec(x_2277);
lean_dec(x_2275);
lean_dec(x_2273);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2388 = lean_ctor_get(x_2280, 0);
lean_inc(x_2388);
x_2389 = lean_ctor_get(x_2280, 1);
lean_inc(x_2389);
lean_dec(x_2280);
x_8 = x_2388;
x_9 = x_2389;
goto block_16;
}
}
else
{
lean_object* x_2390; lean_object* x_2391; 
lean_dec(x_2275);
lean_dec(x_2273);
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2390 = lean_ctor_get(x_2276, 0);
lean_inc(x_2390);
x_2391 = lean_ctor_get(x_2276, 1);
lean_inc(x_2391);
lean_dec(x_2276);
x_8 = x_2390;
x_9 = x_2391;
goto block_16;
}
}
else
{
lean_object* x_2392; lean_object* x_2393; 
lean_dec(x_2271);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2392 = lean_ctor_get(x_2272, 0);
lean_inc(x_2392);
x_2393 = lean_ctor_get(x_2272, 1);
lean_inc(x_2393);
lean_dec(x_2272);
x_8 = x_2392;
x_9 = x_2393;
goto block_16;
}
}
else
{
lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; 
lean_dec(x_2269);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2394 = lean_ctor_get(x_2268, 1);
lean_inc(x_2394);
if (lean_is_exclusive(x_2268)) {
 lean_ctor_release(x_2268, 0);
 lean_ctor_release(x_2268, 1);
 x_2395 = x_2268;
} else {
 lean_dec_ref(x_2268);
 x_2395 = lean_box(0);
}
if (lean_is_scalar(x_2395)) {
 x_2396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2396 = x_2395;
}
lean_ctor_set(x_2396, 0, x_2267);
lean_ctor_set(x_2396, 1, x_2394);
return x_2396;
}
}
else
{
lean_object* x_2397; lean_object* x_2398; 
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2397 = lean_ctor_get(x_2268, 0);
lean_inc(x_2397);
x_2398 = lean_ctor_get(x_2268, 1);
lean_inc(x_2398);
lean_dec(x_2268);
x_8 = x_2397;
x_9 = x_2398;
goto block_16;
}
}
else
{
lean_object* x_2399; lean_object* x_2400; 
lean_dec(x_2252);
lean_dec(x_2250);
lean_dec(x_2239);
lean_dec(x_2235);
lean_dec(x_2233);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2399 = lean_ctor_get(x_2253, 0);
lean_inc(x_2399);
x_2400 = lean_ctor_get(x_2253, 1);
lean_inc(x_2400);
lean_dec(x_2253);
x_8 = x_2399;
x_9 = x_2400;
goto block_16;
}
}
else
{
lean_object* x_2401; lean_object* x_2402; 
lean_dec(x_2239);
lean_dec(x_2235);
lean_dec(x_2233);
lean_dec(x_2231);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2401 = lean_ctor_get(x_2249, 0);
lean_inc(x_2401);
x_2402 = lean_ctor_get(x_2249, 1);
lean_inc(x_2402);
lean_dec(x_2249);
x_8 = x_2401;
x_9 = x_2402;
goto block_16;
}
}
}
else
{
lean_object* x_2403; lean_object* x_2404; 
lean_dec(x_2239);
lean_dec(x_2235);
lean_dec(x_2233);
lean_dec(x_2231);
lean_dec(x_2221);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2403 = lean_ctor_get(x_2241, 0);
lean_inc(x_2403);
x_2404 = lean_ctor_get(x_2241, 1);
lean_inc(x_2404);
lean_dec(x_2241);
x_8 = x_2403;
x_9 = x_2404;
goto block_16;
}
}
else
{
lean_object* x_2405; lean_object* x_2406; 
lean_dec(x_2235);
lean_dec(x_2233);
lean_dec(x_2231);
lean_dec(x_2221);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2405 = lean_ctor_get(x_2236, 0);
lean_inc(x_2405);
x_2406 = lean_ctor_get(x_2236, 1);
lean_inc(x_2406);
lean_dec(x_2236);
x_8 = x_2405;
x_9 = x_2406;
goto block_16;
}
}
else
{
lean_object* x_2407; lean_object* x_2408; 
lean_dec(x_2231);
lean_dec(x_2230);
lean_dec(x_2221);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2407 = lean_ctor_get(x_2232, 0);
lean_inc(x_2407);
x_2408 = lean_ctor_get(x_2232, 1);
lean_inc(x_2408);
lean_dec(x_2232);
x_8 = x_2407;
x_9 = x_2408;
goto block_16;
}
}
else
{
lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; 
lean_dec(x_2228);
lean_dec(x_2227);
lean_dec(x_2221);
lean_dec(x_2220);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2409 = lean_ctor_get(x_2225, 1);
lean_inc(x_2409);
if (lean_is_exclusive(x_2225)) {
 lean_ctor_release(x_2225, 0);
 lean_ctor_release(x_2225, 1);
 x_2410 = x_2225;
} else {
 lean_dec_ref(x_2225);
 x_2410 = lean_box(0);
}
x_2411 = lean_box(0);
if (lean_is_scalar(x_2410)) {
 x_2412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2412 = x_2410;
}
lean_ctor_set(x_2412, 0, x_2411);
lean_ctor_set(x_2412, 1, x_2409);
return x_2412;
}
}
else
{
lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; 
lean_dec(x_2227);
lean_dec(x_2226);
lean_dec(x_2221);
lean_dec(x_2220);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2413 = lean_ctor_get(x_2225, 1);
lean_inc(x_2413);
if (lean_is_exclusive(x_2225)) {
 lean_ctor_release(x_2225, 0);
 lean_ctor_release(x_2225, 1);
 x_2414 = x_2225;
} else {
 lean_dec_ref(x_2225);
 x_2414 = lean_box(0);
}
x_2415 = lean_box(0);
if (lean_is_scalar(x_2414)) {
 x_2416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2416 = x_2414;
}
lean_ctor_set(x_2416, 0, x_2415);
lean_ctor_set(x_2416, 1, x_2413);
return x_2416;
}
}
else
{
lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; 
lean_dec(x_2226);
lean_dec(x_2221);
lean_dec(x_2220);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2417 = lean_ctor_get(x_2225, 1);
lean_inc(x_2417);
if (lean_is_exclusive(x_2225)) {
 lean_ctor_release(x_2225, 0);
 lean_ctor_release(x_2225, 1);
 x_2418 = x_2225;
} else {
 lean_dec_ref(x_2225);
 x_2418 = lean_box(0);
}
x_2419 = lean_box(0);
if (lean_is_scalar(x_2418)) {
 x_2420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2420 = x_2418;
}
lean_ctor_set(x_2420, 0, x_2419);
lean_ctor_set(x_2420, 1, x_2417);
return x_2420;
}
}
else
{
lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; uint8_t x_2424; 
lean_dec(x_2221);
lean_dec(x_2220);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2421 = lean_ctor_get(x_2225, 0);
lean_inc(x_2421);
x_2422 = lean_ctor_get(x_2225, 1);
lean_inc(x_2422);
if (lean_is_exclusive(x_2225)) {
 lean_ctor_release(x_2225, 0);
 lean_ctor_release(x_2225, 1);
 x_2423 = x_2225;
} else {
 lean_dec_ref(x_2225);
 x_2423 = lean_box(0);
}
x_2424 = l_Lean_Exception_isInterrupt(x_2421);
if (x_2424 == 0)
{
uint8_t x_2425; 
x_2425 = l_Lean_Exception_isRuntime(x_2421);
if (x_2425 == 0)
{
lean_object* x_2426; lean_object* x_2427; 
lean_dec(x_2421);
x_2426 = lean_box(0);
if (lean_is_scalar(x_2423)) {
 x_2427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2427 = x_2423;
 lean_ctor_set_tag(x_2427, 0);
}
lean_ctor_set(x_2427, 0, x_2426);
lean_ctor_set(x_2427, 1, x_2422);
return x_2427;
}
else
{
lean_object* x_2428; 
if (lean_is_scalar(x_2423)) {
 x_2428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2428 = x_2423;
}
lean_ctor_set(x_2428, 0, x_2421);
lean_ctor_set(x_2428, 1, x_2422);
return x_2428;
}
}
else
{
lean_object* x_2429; 
if (lean_is_scalar(x_2423)) {
 x_2429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2429 = x_2423;
}
lean_ctor_set(x_2429, 0, x_2421);
lean_ctor_set(x_2429, 1, x_2422);
return x_2429;
}
}
}
else
{
lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; uint8_t x_2433; 
lean_dec(x_2221);
lean_dec(x_2220);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2430 = lean_ctor_get(x_2222, 0);
lean_inc(x_2430);
x_2431 = lean_ctor_get(x_2222, 1);
lean_inc(x_2431);
if (lean_is_exclusive(x_2222)) {
 lean_ctor_release(x_2222, 0);
 lean_ctor_release(x_2222, 1);
 x_2432 = x_2222;
} else {
 lean_dec_ref(x_2222);
 x_2432 = lean_box(0);
}
x_2433 = l_Lean_Exception_isInterrupt(x_2430);
if (x_2433 == 0)
{
uint8_t x_2434; 
x_2434 = l_Lean_Exception_isRuntime(x_2430);
if (x_2434 == 0)
{
lean_object* x_2435; lean_object* x_2436; 
lean_dec(x_2430);
x_2435 = lean_box(0);
if (lean_is_scalar(x_2432)) {
 x_2436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2436 = x_2432;
 lean_ctor_set_tag(x_2436, 0);
}
lean_ctor_set(x_2436, 0, x_2435);
lean_ctor_set(x_2436, 1, x_2431);
return x_2436;
}
else
{
lean_object* x_2437; 
if (lean_is_scalar(x_2432)) {
 x_2437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2437 = x_2432;
}
lean_ctor_set(x_2437, 0, x_2430);
lean_ctor_set(x_2437, 1, x_2431);
return x_2437;
}
}
else
{
lean_object* x_2438; 
if (lean_is_scalar(x_2432)) {
 x_2438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2438 = x_2432;
}
lean_ctor_set(x_2438, 0, x_2430);
lean_ctor_set(x_2438, 1, x_2431);
return x_2438;
}
}
}
else
{
lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; 
lean_dec(x_2218);
lean_dec(x_2217);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2439 = lean_ctor_get(x_2215, 1);
lean_inc(x_2439);
if (lean_is_exclusive(x_2215)) {
 lean_ctor_release(x_2215, 0);
 lean_ctor_release(x_2215, 1);
 x_2440 = x_2215;
} else {
 lean_dec_ref(x_2215);
 x_2440 = lean_box(0);
}
x_2441 = lean_box(0);
if (lean_is_scalar(x_2440)) {
 x_2442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2442 = x_2440;
}
lean_ctor_set(x_2442, 0, x_2441);
lean_ctor_set(x_2442, 1, x_2439);
return x_2442;
}
}
else
{
lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; 
lean_dec(x_2217);
lean_dec(x_2216);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2443 = lean_ctor_get(x_2215, 1);
lean_inc(x_2443);
if (lean_is_exclusive(x_2215)) {
 lean_ctor_release(x_2215, 0);
 lean_ctor_release(x_2215, 1);
 x_2444 = x_2215;
} else {
 lean_dec_ref(x_2215);
 x_2444 = lean_box(0);
}
x_2445 = lean_box(0);
if (lean_is_scalar(x_2444)) {
 x_2446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2446 = x_2444;
}
lean_ctor_set(x_2446, 0, x_2445);
lean_ctor_set(x_2446, 1, x_2443);
return x_2446;
}
}
else
{
lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; 
lean_dec(x_2216);
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2447 = lean_ctor_get(x_2215, 1);
lean_inc(x_2447);
if (lean_is_exclusive(x_2215)) {
 lean_ctor_release(x_2215, 0);
 lean_ctor_release(x_2215, 1);
 x_2448 = x_2215;
} else {
 lean_dec_ref(x_2215);
 x_2448 = lean_box(0);
}
x_2449 = lean_box(0);
if (lean_is_scalar(x_2448)) {
 x_2450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2450 = x_2448;
}
lean_ctor_set(x_2450, 0, x_2449);
lean_ctor_set(x_2450, 1, x_2447);
return x_2450;
}
}
else
{
lean_object* x_2451; lean_object* x_2452; lean_object* x_2453; uint8_t x_2454; 
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2451 = lean_ctor_get(x_2215, 0);
lean_inc(x_2451);
x_2452 = lean_ctor_get(x_2215, 1);
lean_inc(x_2452);
if (lean_is_exclusive(x_2215)) {
 lean_ctor_release(x_2215, 0);
 lean_ctor_release(x_2215, 1);
 x_2453 = x_2215;
} else {
 lean_dec_ref(x_2215);
 x_2453 = lean_box(0);
}
x_2454 = l_Lean_Exception_isInterrupt(x_2451);
if (x_2454 == 0)
{
uint8_t x_2455; 
x_2455 = l_Lean_Exception_isRuntime(x_2451);
if (x_2455 == 0)
{
lean_object* x_2456; lean_object* x_2457; 
lean_dec(x_2451);
x_2456 = lean_box(0);
if (lean_is_scalar(x_2453)) {
 x_2457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2457 = x_2453;
 lean_ctor_set_tag(x_2457, 0);
}
lean_ctor_set(x_2457, 0, x_2456);
lean_ctor_set(x_2457, 1, x_2452);
return x_2457;
}
else
{
lean_object* x_2458; 
if (lean_is_scalar(x_2453)) {
 x_2458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2458 = x_2453;
}
lean_ctor_set(x_2458, 0, x_2451);
lean_ctor_set(x_2458, 1, x_2452);
return x_2458;
}
}
else
{
lean_object* x_2459; 
if (lean_is_scalar(x_2453)) {
 x_2459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2459 = x_2453;
}
lean_ctor_set(x_2459, 0, x_2451);
lean_ctor_set(x_2459, 1, x_2452);
return x_2459;
}
}
}
else
{
lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; uint8_t x_2463; 
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2460 = lean_ctor_get(x_2212, 0);
lean_inc(x_2460);
x_2461 = lean_ctor_get(x_2212, 1);
lean_inc(x_2461);
if (lean_is_exclusive(x_2212)) {
 lean_ctor_release(x_2212, 0);
 lean_ctor_release(x_2212, 1);
 x_2462 = x_2212;
} else {
 lean_dec_ref(x_2212);
 x_2462 = lean_box(0);
}
x_2463 = l_Lean_Exception_isInterrupt(x_2460);
if (x_2463 == 0)
{
uint8_t x_2464; 
x_2464 = l_Lean_Exception_isRuntime(x_2460);
if (x_2464 == 0)
{
lean_object* x_2465; lean_object* x_2466; 
lean_dec(x_2460);
x_2465 = lean_box(0);
if (lean_is_scalar(x_2462)) {
 x_2466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2466 = x_2462;
 lean_ctor_set_tag(x_2466, 0);
}
lean_ctor_set(x_2466, 0, x_2465);
lean_ctor_set(x_2466, 1, x_2461);
return x_2466;
}
else
{
lean_object* x_2467; 
if (lean_is_scalar(x_2462)) {
 x_2467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2467 = x_2462;
}
lean_ctor_set(x_2467, 0, x_2460);
lean_ctor_set(x_2467, 1, x_2461);
return x_2467;
}
}
else
{
lean_object* x_2468; 
if (lean_is_scalar(x_2462)) {
 x_2468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2468 = x_2462;
}
lean_ctor_set(x_2468, 0, x_2460);
lean_ctor_set(x_2468, 1, x_2461);
return x_2468;
}
}
}
}
else
{
lean_object* x_2469; lean_object* x_2470; 
lean_dec(x_40);
lean_dec(x_33);
x_2469 = lean_ctor_get(x_2202, 1);
lean_inc(x_2469);
lean_dec(x_2202);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2470 = l_Lean_Meta_isMonad_x3f(x_54, x_3, x_4, x_5, x_6, x_2469);
if (lean_obj_tag(x_2470) == 0)
{
lean_object* x_2471; 
x_2471 = lean_ctor_get(x_2470, 0);
lean_inc(x_2471);
if (lean_obj_tag(x_2471) == 0)
{
lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; 
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_free_object(x_43);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2472 = lean_ctor_get(x_2470, 1);
lean_inc(x_2472);
if (lean_is_exclusive(x_2470)) {
 lean_ctor_release(x_2470, 0);
 lean_ctor_release(x_2470, 1);
 x_2473 = x_2470;
} else {
 lean_dec_ref(x_2470);
 x_2473 = lean_box(0);
}
x_2474 = lean_box(0);
if (lean_is_scalar(x_2473)) {
 x_2475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2475 = x_2473;
}
lean_ctor_set(x_2475, 0, x_2474);
lean_ctor_set(x_2475, 1, x_2472);
return x_2475;
}
else
{
lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; 
x_2476 = lean_ctor_get(x_2470, 1);
lean_inc(x_2476);
lean_dec(x_2470);
x_2477 = lean_ctor_get(x_2471, 0);
lean_inc(x_2477);
if (lean_is_exclusive(x_2471)) {
 lean_ctor_release(x_2471, 0);
 x_2478 = x_2471;
} else {
 lean_dec_ref(x_2471);
 x_2478 = lean_box(0);
}
if (lean_is_scalar(x_2478)) {
 x_2479 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2479 = x_2478;
}
lean_ctor_set(x_2479, 0, x_2199);
x_2480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2480, 0, x_2200);
lean_ctor_set(x_43, 0, x_55);
x_2481 = lean_box(0);
x_2482 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2482, 0, x_2477);
x_2483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2483, 0, x_1);
x_2484 = lean_box(0);
if (lean_is_scalar(x_2201)) {
 x_2485 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2485 = x_2201;
 lean_ctor_set_tag(x_2485, 1);
}
lean_ctor_set(x_2485, 0, x_2483);
lean_ctor_set(x_2485, 1, x_2484);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_2485);
lean_ctor_set(x_51, 0, x_2482);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_2481);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_43);
x_2486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2486, 0, x_2480);
lean_ctor_set(x_2486, 1, x_31);
x_2487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2487, 0, x_2479);
lean_ctor_set(x_2487, 1, x_2486);
x_2488 = lean_array_mk(x_2487);
x_2489 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2490 = l_Lean_Meta_mkAppOptM(x_2489, x_2488, x_3, x_4, x_5, x_6, x_2476);
if (lean_obj_tag(x_2490) == 0)
{
lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; 
x_2491 = lean_ctor_get(x_2490, 0);
lean_inc(x_2491);
x_2492 = lean_ctor_get(x_2490, 1);
lean_inc(x_2492);
lean_dec(x_2490);
x_2493 = l_Lean_Meta_expandCoe(x_2491, x_3, x_4, x_5, x_6, x_2492);
if (lean_obj_tag(x_2493) == 0)
{
lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; 
x_2494 = lean_ctor_get(x_2493, 0);
lean_inc(x_2494);
x_2495 = lean_ctor_get(x_2493, 1);
lean_inc(x_2495);
lean_dec(x_2493);
x_2496 = lean_box(0);
x_2497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2497, 0, x_2494);
lean_ctor_set(x_2497, 1, x_2496);
x_17 = x_2497;
x_18 = x_2495;
goto block_30;
}
else
{
lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; uint8_t x_2501; 
x_2498 = lean_ctor_get(x_2493, 0);
lean_inc(x_2498);
x_2499 = lean_ctor_get(x_2493, 1);
lean_inc(x_2499);
if (lean_is_exclusive(x_2493)) {
 lean_ctor_release(x_2493, 0);
 lean_ctor_release(x_2493, 1);
 x_2500 = x_2493;
} else {
 lean_dec_ref(x_2493);
 x_2500 = lean_box(0);
}
x_2501 = l_Lean_Exception_isInterrupt(x_2498);
if (x_2501 == 0)
{
uint8_t x_2502; 
x_2502 = l_Lean_Exception_isRuntime(x_2498);
if (x_2502 == 0)
{
lean_object* x_2503; 
lean_dec(x_2500);
lean_dec(x_2498);
x_2503 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_2503;
x_18 = x_2499;
goto block_30;
}
else
{
lean_object* x_2504; 
if (lean_is_scalar(x_2500)) {
 x_2504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2504 = x_2500;
}
lean_ctor_set(x_2504, 0, x_2498);
lean_ctor_set(x_2504, 1, x_2499);
return x_2504;
}
}
else
{
lean_object* x_2505; 
if (lean_is_scalar(x_2500)) {
 x_2505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2505 = x_2500;
}
lean_ctor_set(x_2505, 0, x_2498);
lean_ctor_set(x_2505, 1, x_2499);
return x_2505;
}
}
}
else
{
lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; uint8_t x_2509; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2506 = lean_ctor_get(x_2490, 0);
lean_inc(x_2506);
x_2507 = lean_ctor_get(x_2490, 1);
lean_inc(x_2507);
if (lean_is_exclusive(x_2490)) {
 lean_ctor_release(x_2490, 0);
 lean_ctor_release(x_2490, 1);
 x_2508 = x_2490;
} else {
 lean_dec_ref(x_2490);
 x_2508 = lean_box(0);
}
x_2509 = l_Lean_Exception_isInterrupt(x_2506);
if (x_2509 == 0)
{
uint8_t x_2510; 
x_2510 = l_Lean_Exception_isRuntime(x_2506);
if (x_2510 == 0)
{
lean_object* x_2511; 
lean_dec(x_2508);
lean_dec(x_2506);
x_2511 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_2511;
x_18 = x_2507;
goto block_30;
}
else
{
lean_object* x_2512; 
if (lean_is_scalar(x_2508)) {
 x_2512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2512 = x_2508;
}
lean_ctor_set(x_2512, 0, x_2506);
lean_ctor_set(x_2512, 1, x_2507);
return x_2512;
}
}
else
{
lean_object* x_2513; 
if (lean_is_scalar(x_2508)) {
 x_2513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2513 = x_2508;
}
lean_ctor_set(x_2513, 0, x_2506);
lean_ctor_set(x_2513, 1, x_2507);
return x_2513;
}
}
}
}
else
{
lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; 
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_free_object(x_43);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2514 = lean_ctor_get(x_2470, 0);
lean_inc(x_2514);
x_2515 = lean_ctor_get(x_2470, 1);
lean_inc(x_2515);
if (lean_is_exclusive(x_2470)) {
 lean_ctor_release(x_2470, 0);
 lean_ctor_release(x_2470, 1);
 x_2516 = x_2470;
} else {
 lean_dec_ref(x_2470);
 x_2516 = lean_box(0);
}
if (lean_is_scalar(x_2516)) {
 x_2517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2517 = x_2516;
}
lean_ctor_set(x_2517, 0, x_2514);
lean_ctor_set(x_2517, 1, x_2515);
return x_2517;
}
}
}
else
{
lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; 
lean_dec(x_2201);
lean_dec(x_2200);
lean_dec(x_2199);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2518 = lean_ctor_get(x_2202, 0);
lean_inc(x_2518);
x_2519 = lean_ctor_get(x_2202, 1);
lean_inc(x_2519);
if (lean_is_exclusive(x_2202)) {
 lean_ctor_release(x_2202, 0);
 lean_ctor_release(x_2202, 1);
 x_2520 = x_2202;
} else {
 lean_dec_ref(x_2202);
 x_2520 = lean_box(0);
}
if (lean_is_scalar(x_2520)) {
 x_2521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2521 = x_2520;
}
lean_ctor_set(x_2521, 0, x_2518);
lean_ctor_set(x_2521, 1, x_2519);
return x_2521;
}
}
}
}
else
{
uint8_t x_2522; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2522 = !lean_is_exclusive(x_56);
if (x_2522 == 0)
{
return x_56;
}
else
{
lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; 
x_2523 = lean_ctor_get(x_56, 0);
x_2524 = lean_ctor_get(x_56, 1);
lean_inc(x_2524);
lean_inc(x_2523);
lean_dec(x_56);
x_2525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2525, 0, x_2523);
lean_ctor_set(x_2525, 1, x_2524);
return x_2525;
}
}
}
else
{
lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; 
x_2526 = lean_ctor_get(x_51, 0);
x_2527 = lean_ctor_get(x_51, 1);
lean_inc(x_2527);
lean_inc(x_2526);
lean_dec(x_51);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_2528 = l_Lean_Meta_isTypeApp_x3f(x_40, x_3, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_2528) == 0)
{
lean_object* x_2529; 
x_2529 = lean_ctor_get(x_2528, 0);
lean_inc(x_2529);
if (lean_obj_tag(x_2529) == 0)
{
lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; 
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2530 = lean_ctor_get(x_2528, 1);
lean_inc(x_2530);
if (lean_is_exclusive(x_2528)) {
 lean_ctor_release(x_2528, 0);
 lean_ctor_release(x_2528, 1);
 x_2531 = x_2528;
} else {
 lean_dec_ref(x_2528);
 x_2531 = lean_box(0);
}
x_2532 = lean_box(0);
if (lean_is_scalar(x_2531)) {
 x_2533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2533 = x_2531;
}
lean_ctor_set(x_2533, 0, x_2532);
lean_ctor_set(x_2533, 1, x_2530);
return x_2533;
}
else
{
lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; 
x_2534 = lean_ctor_get(x_2529, 0);
lean_inc(x_2534);
if (lean_is_exclusive(x_2529)) {
 lean_ctor_release(x_2529, 0);
 x_2535 = x_2529;
} else {
 lean_dec_ref(x_2529);
 x_2535 = lean_box(0);
}
x_2536 = lean_ctor_get(x_2528, 1);
lean_inc(x_2536);
lean_dec(x_2528);
x_2537 = lean_ctor_get(x_2534, 0);
lean_inc(x_2537);
x_2538 = lean_ctor_get(x_2534, 1);
lean_inc(x_2538);
if (lean_is_exclusive(x_2534)) {
 lean_ctor_release(x_2534, 0);
 lean_ctor_release(x_2534, 1);
 x_2539 = x_2534;
} else {
 lean_dec_ref(x_2534);
 x_2539 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2526);
lean_inc(x_2537);
x_2540 = l_Lean_Meta_isExprDefEq(x_2537, x_2526, x_3, x_4, x_5, x_6, x_2536);
if (lean_obj_tag(x_2540) == 0)
{
lean_object* x_2541; uint8_t x_2542; 
x_2541 = lean_ctor_get(x_2540, 0);
lean_inc(x_2541);
x_2542 = lean_unbox(x_2541);
lean_dec(x_2541);
if (x_2542 == 0)
{
lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; uint8_t x_2547; 
lean_free_object(x_43);
x_2543 = lean_ctor_get(x_2540, 1);
lean_inc(x_2543);
if (lean_is_exclusive(x_2540)) {
 lean_ctor_release(x_2540, 0);
 lean_ctor_release(x_2540, 1);
 x_2544 = x_2540;
} else {
 lean_dec_ref(x_2540);
 x_2544 = lean_box(0);
}
x_2545 = lean_ctor_get(x_5, 2);
lean_inc(x_2545);
x_2546 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_2547 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2545, x_2546);
lean_dec(x_2545);
if (x_2547 == 0)
{
lean_object* x_2548; lean_object* x_2549; 
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2548 = lean_box(0);
if (lean_is_scalar(x_2544)) {
 x_2549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2549 = x_2544;
}
lean_ctor_set(x_2549, 0, x_2548);
lean_ctor_set(x_2549, 1, x_2543);
return x_2549;
}
else
{
lean_object* x_2550; 
lean_dec(x_2544);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2537);
x_2550 = lean_infer_type(x_2537, x_3, x_4, x_5, x_6, x_2543);
if (lean_obj_tag(x_2550) == 0)
{
lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; 
x_2551 = lean_ctor_get(x_2550, 0);
lean_inc(x_2551);
x_2552 = lean_ctor_get(x_2550, 1);
lean_inc(x_2552);
lean_dec(x_2550);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2553 = lean_whnf(x_2551, x_3, x_4, x_5, x_6, x_2552);
if (lean_obj_tag(x_2553) == 0)
{
lean_object* x_2554; 
x_2554 = lean_ctor_get(x_2553, 0);
lean_inc(x_2554);
if (lean_obj_tag(x_2554) == 7)
{
lean_object* x_2555; 
x_2555 = lean_ctor_get(x_2554, 1);
lean_inc(x_2555);
if (lean_obj_tag(x_2555) == 3)
{
lean_object* x_2556; 
x_2556 = lean_ctor_get(x_2554, 2);
lean_inc(x_2556);
lean_dec(x_2554);
if (lean_obj_tag(x_2556) == 3)
{
lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; 
x_2557 = lean_ctor_get(x_2553, 1);
lean_inc(x_2557);
lean_dec(x_2553);
x_2558 = lean_ctor_get(x_2555, 0);
lean_inc(x_2558);
lean_dec(x_2555);
x_2559 = lean_ctor_get(x_2556, 0);
lean_inc(x_2559);
lean_dec(x_2556);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2526);
x_2560 = lean_infer_type(x_2526, x_3, x_4, x_5, x_6, x_2557);
if (lean_obj_tag(x_2560) == 0)
{
lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; 
x_2561 = lean_ctor_get(x_2560, 0);
lean_inc(x_2561);
x_2562 = lean_ctor_get(x_2560, 1);
lean_inc(x_2562);
lean_dec(x_2560);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2563 = lean_whnf(x_2561, x_3, x_4, x_5, x_6, x_2562);
if (lean_obj_tag(x_2563) == 0)
{
lean_object* x_2564; 
x_2564 = lean_ctor_get(x_2563, 0);
lean_inc(x_2564);
if (lean_obj_tag(x_2564) == 7)
{
lean_object* x_2565; 
x_2565 = lean_ctor_get(x_2564, 1);
lean_inc(x_2565);
if (lean_obj_tag(x_2565) == 3)
{
lean_object* x_2566; 
x_2566 = lean_ctor_get(x_2564, 2);
lean_inc(x_2566);
lean_dec(x_2564);
if (lean_obj_tag(x_2566) == 3)
{
lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; 
x_2567 = lean_ctor_get(x_2563, 1);
lean_inc(x_2567);
lean_dec(x_2563);
x_2568 = lean_ctor_get(x_2565, 0);
lean_inc(x_2568);
lean_dec(x_2565);
x_2569 = lean_ctor_get(x_2566, 0);
lean_inc(x_2569);
lean_dec(x_2566);
x_2570 = l_Lean_Meta_decLevel(x_2558, x_3, x_4, x_5, x_6, x_2567);
if (lean_obj_tag(x_2570) == 0)
{
lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; 
x_2571 = lean_ctor_get(x_2570, 0);
lean_inc(x_2571);
x_2572 = lean_ctor_get(x_2570, 1);
lean_inc(x_2572);
if (lean_is_exclusive(x_2570)) {
 lean_ctor_release(x_2570, 0);
 lean_ctor_release(x_2570, 1);
 x_2573 = x_2570;
} else {
 lean_dec_ref(x_2570);
 x_2573 = lean_box(0);
}
x_2574 = l_Lean_Meta_decLevel(x_2568, x_3, x_4, x_5, x_6, x_2572);
if (lean_obj_tag(x_2574) == 0)
{
lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; uint8_t x_2578; lean_object* x_2579; 
x_2575 = lean_ctor_get(x_2574, 0);
lean_inc(x_2575);
x_2576 = lean_ctor_get(x_2574, 1);
lean_inc(x_2576);
if (lean_is_exclusive(x_2574)) {
 lean_ctor_release(x_2574, 0);
 lean_ctor_release(x_2574, 1);
 x_2577 = x_2574;
} else {
 lean_dec_ref(x_2574);
 x_2577 = lean_box(0);
}
x_2578 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2571);
x_2579 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_2571, x_2575, x_2578, x_3, x_4, x_5, x_6, x_2576);
if (lean_obj_tag(x_2579) == 0)
{
lean_object* x_2580; uint8_t x_2581; 
x_2580 = lean_ctor_get(x_2579, 0);
lean_inc(x_2580);
x_2581 = lean_unbox(x_2580);
lean_dec(x_2580);
if (x_2581 == 0)
{
lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; 
lean_dec(x_2577);
lean_dec(x_2573);
lean_dec(x_2571);
lean_dec(x_2569);
lean_dec(x_2559);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2582 = lean_ctor_get(x_2579, 1);
lean_inc(x_2582);
if (lean_is_exclusive(x_2579)) {
 lean_ctor_release(x_2579, 0);
 lean_ctor_release(x_2579, 1);
 x_2583 = x_2579;
} else {
 lean_dec_ref(x_2579);
 x_2583 = lean_box(0);
}
x_2584 = lean_box(0);
if (lean_is_scalar(x_2583)) {
 x_2585 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2585 = x_2583;
}
lean_ctor_set(x_2585, 0, x_2584);
lean_ctor_set(x_2585, 1, x_2582);
return x_2585;
}
else
{
lean_object* x_2586; lean_object* x_2587; 
x_2586 = lean_ctor_get(x_2579, 1);
lean_inc(x_2586);
lean_dec(x_2579);
x_2587 = l_Lean_Meta_decLevel(x_2559, x_3, x_4, x_5, x_6, x_2586);
if (lean_obj_tag(x_2587) == 0)
{
lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; 
x_2588 = lean_ctor_get(x_2587, 0);
lean_inc(x_2588);
x_2589 = lean_ctor_get(x_2587, 1);
lean_inc(x_2589);
if (lean_is_exclusive(x_2587)) {
 lean_ctor_release(x_2587, 0);
 lean_ctor_release(x_2587, 1);
 x_2590 = x_2587;
} else {
 lean_dec_ref(x_2587);
 x_2590 = lean_box(0);
}
x_2591 = l_Lean_Meta_decLevel(x_2569, x_3, x_4, x_5, x_6, x_2589);
if (lean_obj_tag(x_2591) == 0)
{
lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; 
x_2592 = lean_ctor_get(x_2591, 0);
lean_inc(x_2592);
x_2593 = lean_ctor_get(x_2591, 1);
lean_inc(x_2593);
if (lean_is_exclusive(x_2591)) {
 lean_ctor_release(x_2591, 0);
 lean_ctor_release(x_2591, 1);
 x_2594 = x_2591;
} else {
 lean_dec_ref(x_2591);
 x_2594 = lean_box(0);
}
x_2595 = lean_box(0);
if (lean_is_scalar(x_2594)) {
 x_2596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2596 = x_2594;
 lean_ctor_set_tag(x_2596, 1);
}
lean_ctor_set(x_2596, 0, x_2592);
lean_ctor_set(x_2596, 1, x_2595);
if (lean_is_scalar(x_2590)) {
 x_2597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2597 = x_2590;
 lean_ctor_set_tag(x_2597, 1);
}
lean_ctor_set(x_2597, 0, x_2588);
lean_ctor_set(x_2597, 1, x_2596);
if (lean_is_scalar(x_2577)) {
 x_2598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2598 = x_2577;
 lean_ctor_set_tag(x_2598, 1);
}
lean_ctor_set(x_2598, 0, x_2571);
lean_ctor_set(x_2598, 1, x_2597);
x_2599 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2600 = l_Lean_Expr_const___override(x_2599, x_2598);
lean_inc(x_2526);
if (lean_is_scalar(x_2573)) {
 x_2601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2601 = x_2573;
 lean_ctor_set_tag(x_2601, 1);
}
lean_ctor_set(x_2601, 0, x_2526);
lean_ctor_set(x_2601, 1, x_2595);
lean_inc(x_2537);
if (lean_is_scalar(x_2539)) {
 x_2602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2602 = x_2539;
 lean_ctor_set_tag(x_2602, 1);
}
lean_ctor_set(x_2602, 0, x_2537);
lean_ctor_set(x_2602, 1, x_2601);
x_2603 = lean_array_mk(x_2602);
x_2604 = l_Lean_mkAppN(x_2600, x_2603);
lean_dec(x_2603);
x_2605 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2606 = l_Lean_Meta_trySynthInstance(x_2604, x_2605, x_3, x_4, x_5, x_6, x_2593);
if (lean_obj_tag(x_2606) == 0)
{
lean_object* x_2607; 
x_2607 = lean_ctor_get(x_2606, 0);
lean_inc(x_2607);
if (lean_obj_tag(x_2607) == 1)
{
lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; 
x_2608 = lean_ctor_get(x_2606, 1);
lean_inc(x_2608);
lean_dec(x_2606);
x_2609 = lean_ctor_get(x_2607, 0);
lean_inc(x_2609);
lean_dec(x_2607);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2538);
x_2610 = l_Lean_Meta_getDecLevel(x_2538, x_3, x_4, x_5, x_6, x_2608);
if (lean_obj_tag(x_2610) == 0)
{
lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; 
x_2611 = lean_ctor_get(x_2610, 0);
lean_inc(x_2611);
x_2612 = lean_ctor_get(x_2610, 1);
lean_inc(x_2612);
if (lean_is_exclusive(x_2610)) {
 lean_ctor_release(x_2610, 0);
 lean_ctor_release(x_2610, 1);
 x_2613 = x_2610;
} else {
 lean_dec_ref(x_2610);
 x_2613 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2614 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_2612);
if (lean_obj_tag(x_2614) == 0)
{
lean_object* x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; 
x_2615 = lean_ctor_get(x_2614, 0);
lean_inc(x_2615);
x_2616 = lean_ctor_get(x_2614, 1);
lean_inc(x_2616);
if (lean_is_exclusive(x_2614)) {
 lean_ctor_release(x_2614, 0);
 lean_ctor_release(x_2614, 1);
 x_2617 = x_2614;
} else {
 lean_dec_ref(x_2614);
 x_2617 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_2618 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_2616);
if (lean_obj_tag(x_2618) == 0)
{
lean_object* x_2619; lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; 
x_2619 = lean_ctor_get(x_2618, 0);
lean_inc(x_2619);
x_2620 = lean_ctor_get(x_2618, 1);
lean_inc(x_2620);
if (lean_is_exclusive(x_2618)) {
 lean_ctor_release(x_2618, 0);
 lean_ctor_release(x_2618, 1);
 x_2621 = x_2618;
} else {
 lean_dec_ref(x_2618);
 x_2621 = lean_box(0);
}
if (lean_is_scalar(x_2621)) {
 x_2622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2622 = x_2621;
 lean_ctor_set_tag(x_2622, 1);
}
lean_ctor_set(x_2622, 0, x_2619);
lean_ctor_set(x_2622, 1, x_2595);
if (lean_is_scalar(x_2617)) {
 x_2623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2623 = x_2617;
 lean_ctor_set_tag(x_2623, 1);
}
lean_ctor_set(x_2623, 0, x_2615);
lean_ctor_set(x_2623, 1, x_2622);
if (lean_is_scalar(x_2613)) {
 x_2624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2624 = x_2613;
 lean_ctor_set_tag(x_2624, 1);
}
lean_ctor_set(x_2624, 0, x_2611);
lean_ctor_set(x_2624, 1, x_2623);
x_2625 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_2624);
x_2626 = l_Lean_Expr_const___override(x_2625, x_2624);
x_2627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2627, 0, x_1);
lean_ctor_set(x_2627, 1, x_2595);
lean_inc(x_2627);
lean_inc(x_2538);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_2627);
lean_ctor_set(x_38, 0, x_2538);
lean_inc(x_2609);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_2609);
lean_inc(x_2526);
x_2628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2628, 0, x_2526);
lean_ctor_set(x_2628, 1, x_31);
lean_inc(x_2537);
x_2629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2629, 0, x_2537);
lean_ctor_set(x_2629, 1, x_2628);
x_2630 = lean_array_mk(x_2629);
x_2631 = l_Lean_mkAppN(x_2626, x_2630);
lean_dec(x_2630);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2631);
x_2632 = lean_infer_type(x_2631, x_3, x_4, x_5, x_6, x_2620);
if (lean_obj_tag(x_2632) == 0)
{
lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; lean_object* x_2636; 
x_2633 = lean_ctor_get(x_2632, 0);
lean_inc(x_2633);
x_2634 = lean_ctor_get(x_2632, 1);
lean_inc(x_2634);
if (lean_is_exclusive(x_2632)) {
 lean_ctor_release(x_2632, 0);
 lean_ctor_release(x_2632, 1);
 x_2635 = x_2632;
} else {
 lean_dec_ref(x_2632);
 x_2635 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_2636 = l_Lean_Meta_isExprDefEq(x_33, x_2633, x_3, x_4, x_5, x_6, x_2634);
if (lean_obj_tag(x_2636) == 0)
{
lean_object* x_2637; uint8_t x_2638; 
x_2637 = lean_ctor_get(x_2636, 0);
lean_inc(x_2637);
x_2638 = lean_unbox(x_2637);
lean_dec(x_2637);
if (x_2638 == 0)
{
lean_object* x_2639; lean_object* x_2640; 
lean_dec(x_2631);
lean_dec(x_2535);
x_2639 = lean_ctor_get(x_2636, 1);
lean_inc(x_2639);
lean_dec(x_2636);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2526);
x_2640 = l_Lean_Meta_isMonad_x3f(x_2526, x_3, x_4, x_5, x_6, x_2639);
if (lean_obj_tag(x_2640) == 0)
{
lean_object* x_2641; 
x_2641 = lean_ctor_get(x_2640, 0);
lean_inc(x_2641);
if (lean_obj_tag(x_2641) == 0)
{
lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; 
lean_dec(x_2635);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2642 = lean_ctor_get(x_2640, 1);
lean_inc(x_2642);
if (lean_is_exclusive(x_2640)) {
 lean_ctor_release(x_2640, 0);
 lean_ctor_release(x_2640, 1);
 x_2643 = x_2640;
} else {
 lean_dec_ref(x_2640);
 x_2643 = lean_box(0);
}
if (lean_is_scalar(x_2643)) {
 x_2644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2644 = x_2643;
}
lean_ctor_set(x_2644, 0, x_2605);
lean_ctor_set(x_2644, 1, x_2642);
return x_2644;
}
else
{
lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; 
x_2645 = lean_ctor_get(x_2640, 1);
lean_inc(x_2645);
lean_dec(x_2640);
x_2646 = lean_ctor_get(x_2641, 0);
lean_inc(x_2646);
lean_dec(x_2641);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2538);
x_2647 = l_Lean_Meta_getLevel(x_2538, x_3, x_4, x_5, x_6, x_2645);
if (lean_obj_tag(x_2647) == 0)
{
lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; 
x_2648 = lean_ctor_get(x_2647, 0);
lean_inc(x_2648);
x_2649 = lean_ctor_get(x_2647, 1);
lean_inc(x_2649);
if (lean_is_exclusive(x_2647)) {
 lean_ctor_release(x_2647, 0);
 lean_ctor_release(x_2647, 1);
 x_2650 = x_2647;
} else {
 lean_dec_ref(x_2647);
 x_2650 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2527);
x_2651 = l_Lean_Meta_getLevel(x_2527, x_3, x_4, x_5, x_6, x_2649);
if (lean_obj_tag(x_2651) == 0)
{
lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; uint8_t x_2666; lean_object* x_2667; lean_object* x_2668; 
x_2652 = lean_ctor_get(x_2651, 0);
lean_inc(x_2652);
x_2653 = lean_ctor_get(x_2651, 1);
lean_inc(x_2653);
if (lean_is_exclusive(x_2651)) {
 lean_ctor_release(x_2651, 0);
 lean_ctor_release(x_2651, 1);
 x_2654 = x_2651;
} else {
 lean_dec_ref(x_2651);
 x_2654 = lean_box(0);
}
if (lean_is_scalar(x_2654)) {
 x_2655 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2655 = x_2654;
 lean_ctor_set_tag(x_2655, 1);
}
lean_ctor_set(x_2655, 0, x_2652);
lean_ctor_set(x_2655, 1, x_2595);
if (lean_is_scalar(x_2650)) {
 x_2656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2656 = x_2650;
 lean_ctor_set_tag(x_2656, 1);
}
lean_ctor_set(x_2656, 0, x_2648);
lean_ctor_set(x_2656, 1, x_2655);
x_2657 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_2658 = l_Lean_Expr_const___override(x_2657, x_2656);
lean_inc(x_2527);
if (lean_is_scalar(x_2635)) {
 x_2659 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2659 = x_2635;
 lean_ctor_set_tag(x_2659, 1);
}
lean_ctor_set(x_2659, 0, x_2527);
lean_ctor_set(x_2659, 1, x_2595);
x_2660 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_2661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2661, 0, x_2660);
lean_ctor_set(x_2661, 1, x_2659);
lean_inc(x_2538);
x_2662 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2662, 0, x_2538);
lean_ctor_set(x_2662, 1, x_2661);
x_2663 = lean_array_mk(x_2662);
x_2664 = l_Lean_mkAppN(x_2658, x_2663);
lean_dec(x_2663);
x_2665 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_2666 = 0;
lean_inc(x_2538);
x_2667 = l_Lean_Expr_forallE___override(x_2665, x_2538, x_2664, x_2666);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2668 = l_Lean_Meta_trySynthInstance(x_2667, x_2605, x_3, x_4, x_5, x_6, x_2653);
if (lean_obj_tag(x_2668) == 0)
{
lean_object* x_2669; 
x_2669 = lean_ctor_get(x_2668, 0);
lean_inc(x_2669);
if (lean_obj_tag(x_2669) == 1)
{
lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; 
x_2670 = lean_ctor_get(x_2668, 1);
lean_inc(x_2670);
lean_dec(x_2668);
x_2671 = lean_ctor_get(x_2669, 0);
lean_inc(x_2671);
lean_dec(x_2669);
x_2672 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_2673 = l_Lean_Expr_const___override(x_2672, x_2624);
x_2674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2674, 0, x_2646);
lean_ctor_set(x_2674, 1, x_2627);
x_2675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2675, 0, x_2671);
lean_ctor_set(x_2675, 1, x_2674);
x_2676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2676, 0, x_2609);
lean_ctor_set(x_2676, 1, x_2675);
x_2677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2677, 0, x_2527);
lean_ctor_set(x_2677, 1, x_2676);
x_2678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2678, 0, x_2538);
lean_ctor_set(x_2678, 1, x_2677);
x_2679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2679, 0, x_2526);
lean_ctor_set(x_2679, 1, x_2678);
x_2680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2680, 0, x_2537);
lean_ctor_set(x_2680, 1, x_2679);
x_2681 = lean_array_mk(x_2680);
x_2682 = l_Lean_mkAppN(x_2673, x_2681);
lean_dec(x_2681);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2683 = l_Lean_Meta_expandCoe(x_2682, x_3, x_4, x_5, x_6, x_2670);
if (lean_obj_tag(x_2683) == 0)
{
lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; 
x_2684 = lean_ctor_get(x_2683, 0);
lean_inc(x_2684);
x_2685 = lean_ctor_get(x_2683, 1);
lean_inc(x_2685);
lean_dec(x_2683);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2684);
x_2686 = lean_infer_type(x_2684, x_3, x_4, x_5, x_6, x_2685);
if (lean_obj_tag(x_2686) == 0)
{
lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; 
x_2687 = lean_ctor_get(x_2686, 0);
lean_inc(x_2687);
x_2688 = lean_ctor_get(x_2686, 1);
lean_inc(x_2688);
lean_dec(x_2686);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2689 = l_Lean_Meta_isExprDefEq(x_33, x_2687, x_3, x_4, x_5, x_6, x_2688);
if (lean_obj_tag(x_2689) == 0)
{
lean_object* x_2690; uint8_t x_2691; 
x_2690 = lean_ctor_get(x_2689, 0);
lean_inc(x_2690);
x_2691 = lean_unbox(x_2690);
lean_dec(x_2690);
if (x_2691 == 0)
{
lean_object* x_2692; lean_object* x_2693; lean_object* x_2694; 
lean_dec(x_2684);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2692 = lean_ctor_get(x_2689, 1);
lean_inc(x_2692);
if (lean_is_exclusive(x_2689)) {
 lean_ctor_release(x_2689, 0);
 lean_ctor_release(x_2689, 1);
 x_2693 = x_2689;
} else {
 lean_dec_ref(x_2689);
 x_2693 = lean_box(0);
}
if (lean_is_scalar(x_2693)) {
 x_2694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2694 = x_2693;
}
lean_ctor_set(x_2694, 0, x_2605);
lean_ctor_set(x_2694, 1, x_2692);
return x_2694;
}
else
{
lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; 
x_2695 = lean_ctor_get(x_2689, 1);
lean_inc(x_2695);
lean_dec(x_2689);
x_2696 = lean_box(0);
x_2697 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2684, x_2696, x_3, x_4, x_5, x_6, x_2695);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2698 = lean_ctor_get(x_2697, 0);
lean_inc(x_2698);
x_2699 = lean_ctor_get(x_2697, 1);
lean_inc(x_2699);
if (lean_is_exclusive(x_2697)) {
 lean_ctor_release(x_2697, 0);
 lean_ctor_release(x_2697, 1);
 x_2700 = x_2697;
} else {
 lean_dec_ref(x_2697);
 x_2700 = lean_box(0);
}
if (lean_is_scalar(x_2700)) {
 x_2701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2701 = x_2700;
}
lean_ctor_set(x_2701, 0, x_2698);
lean_ctor_set(x_2701, 1, x_2699);
return x_2701;
}
}
else
{
lean_object* x_2702; lean_object* x_2703; 
lean_dec(x_2684);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2702 = lean_ctor_get(x_2689, 0);
lean_inc(x_2702);
x_2703 = lean_ctor_get(x_2689, 1);
lean_inc(x_2703);
lean_dec(x_2689);
x_8 = x_2702;
x_9 = x_2703;
goto block_16;
}
}
else
{
lean_object* x_2704; lean_object* x_2705; 
lean_dec(x_2684);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2704 = lean_ctor_get(x_2686, 0);
lean_inc(x_2704);
x_2705 = lean_ctor_get(x_2686, 1);
lean_inc(x_2705);
lean_dec(x_2686);
x_8 = x_2704;
x_9 = x_2705;
goto block_16;
}
}
else
{
lean_object* x_2706; lean_object* x_2707; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2706 = lean_ctor_get(x_2683, 0);
lean_inc(x_2706);
x_2707 = lean_ctor_get(x_2683, 1);
lean_inc(x_2707);
lean_dec(x_2683);
x_8 = x_2706;
x_9 = x_2707;
goto block_16;
}
}
else
{
lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; 
lean_dec(x_2669);
lean_dec(x_2646);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2708 = lean_ctor_get(x_2668, 1);
lean_inc(x_2708);
if (lean_is_exclusive(x_2668)) {
 lean_ctor_release(x_2668, 0);
 lean_ctor_release(x_2668, 1);
 x_2709 = x_2668;
} else {
 lean_dec_ref(x_2668);
 x_2709 = lean_box(0);
}
if (lean_is_scalar(x_2709)) {
 x_2710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2710 = x_2709;
}
lean_ctor_set(x_2710, 0, x_2605);
lean_ctor_set(x_2710, 1, x_2708);
return x_2710;
}
}
else
{
lean_object* x_2711; lean_object* x_2712; 
lean_dec(x_2646);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2711 = lean_ctor_get(x_2668, 0);
lean_inc(x_2711);
x_2712 = lean_ctor_get(x_2668, 1);
lean_inc(x_2712);
lean_dec(x_2668);
x_8 = x_2711;
x_9 = x_2712;
goto block_16;
}
}
else
{
lean_object* x_2713; lean_object* x_2714; 
lean_dec(x_2650);
lean_dec(x_2648);
lean_dec(x_2646);
lean_dec(x_2635);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2713 = lean_ctor_get(x_2651, 0);
lean_inc(x_2713);
x_2714 = lean_ctor_get(x_2651, 1);
lean_inc(x_2714);
lean_dec(x_2651);
x_8 = x_2713;
x_9 = x_2714;
goto block_16;
}
}
else
{
lean_object* x_2715; lean_object* x_2716; 
lean_dec(x_2646);
lean_dec(x_2635);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2715 = lean_ctor_get(x_2647, 0);
lean_inc(x_2715);
x_2716 = lean_ctor_get(x_2647, 1);
lean_inc(x_2716);
lean_dec(x_2647);
x_8 = x_2715;
x_9 = x_2716;
goto block_16;
}
}
}
else
{
lean_object* x_2717; lean_object* x_2718; 
lean_dec(x_2635);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2717 = lean_ctor_get(x_2640, 0);
lean_inc(x_2717);
x_2718 = lean_ctor_get(x_2640, 1);
lean_inc(x_2718);
lean_dec(x_2640);
x_8 = x_2717;
x_9 = x_2718;
goto block_16;
}
}
else
{
lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; 
lean_dec(x_2635);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2719 = lean_ctor_get(x_2636, 1);
lean_inc(x_2719);
if (lean_is_exclusive(x_2636)) {
 lean_ctor_release(x_2636, 0);
 lean_ctor_release(x_2636, 1);
 x_2720 = x_2636;
} else {
 lean_dec_ref(x_2636);
 x_2720 = lean_box(0);
}
if (lean_is_scalar(x_2535)) {
 x_2721 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2721 = x_2535;
}
lean_ctor_set(x_2721, 0, x_2631);
if (lean_is_scalar(x_2720)) {
 x_2722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2722 = x_2720;
}
lean_ctor_set(x_2722, 0, x_2721);
lean_ctor_set(x_2722, 1, x_2719);
return x_2722;
}
}
else
{
lean_object* x_2723; lean_object* x_2724; 
lean_dec(x_2635);
lean_dec(x_2631);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2723 = lean_ctor_get(x_2636, 0);
lean_inc(x_2723);
x_2724 = lean_ctor_get(x_2636, 1);
lean_inc(x_2724);
lean_dec(x_2636);
x_8 = x_2723;
x_9 = x_2724;
goto block_16;
}
}
else
{
lean_object* x_2725; lean_object* x_2726; 
lean_dec(x_2631);
lean_dec(x_2627);
lean_dec(x_2624);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2725 = lean_ctor_get(x_2632, 0);
lean_inc(x_2725);
x_2726 = lean_ctor_get(x_2632, 1);
lean_inc(x_2726);
lean_dec(x_2632);
x_8 = x_2725;
x_9 = x_2726;
goto block_16;
}
}
else
{
lean_object* x_2727; lean_object* x_2728; 
lean_dec(x_2617);
lean_dec(x_2615);
lean_dec(x_2613);
lean_dec(x_2611);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2727 = lean_ctor_get(x_2618, 0);
lean_inc(x_2727);
x_2728 = lean_ctor_get(x_2618, 1);
lean_inc(x_2728);
lean_dec(x_2618);
x_8 = x_2727;
x_9 = x_2728;
goto block_16;
}
}
else
{
lean_object* x_2729; lean_object* x_2730; 
lean_dec(x_2613);
lean_dec(x_2611);
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2729 = lean_ctor_get(x_2614, 0);
lean_inc(x_2729);
x_2730 = lean_ctor_get(x_2614, 1);
lean_inc(x_2730);
lean_dec(x_2614);
x_8 = x_2729;
x_9 = x_2730;
goto block_16;
}
}
else
{
lean_object* x_2731; lean_object* x_2732; 
lean_dec(x_2609);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2731 = lean_ctor_get(x_2610, 0);
lean_inc(x_2731);
x_2732 = lean_ctor_get(x_2610, 1);
lean_inc(x_2732);
lean_dec(x_2610);
x_8 = x_2731;
x_9 = x_2732;
goto block_16;
}
}
else
{
lean_object* x_2733; lean_object* x_2734; lean_object* x_2735; 
lean_dec(x_2607);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2733 = lean_ctor_get(x_2606, 1);
lean_inc(x_2733);
if (lean_is_exclusive(x_2606)) {
 lean_ctor_release(x_2606, 0);
 lean_ctor_release(x_2606, 1);
 x_2734 = x_2606;
} else {
 lean_dec_ref(x_2606);
 x_2734 = lean_box(0);
}
if (lean_is_scalar(x_2734)) {
 x_2735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2735 = x_2734;
}
lean_ctor_set(x_2735, 0, x_2605);
lean_ctor_set(x_2735, 1, x_2733);
return x_2735;
}
}
else
{
lean_object* x_2736; lean_object* x_2737; 
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2736 = lean_ctor_get(x_2606, 0);
lean_inc(x_2736);
x_2737 = lean_ctor_get(x_2606, 1);
lean_inc(x_2737);
lean_dec(x_2606);
x_8 = x_2736;
x_9 = x_2737;
goto block_16;
}
}
else
{
lean_object* x_2738; lean_object* x_2739; 
lean_dec(x_2590);
lean_dec(x_2588);
lean_dec(x_2577);
lean_dec(x_2573);
lean_dec(x_2571);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2738 = lean_ctor_get(x_2591, 0);
lean_inc(x_2738);
x_2739 = lean_ctor_get(x_2591, 1);
lean_inc(x_2739);
lean_dec(x_2591);
x_8 = x_2738;
x_9 = x_2739;
goto block_16;
}
}
else
{
lean_object* x_2740; lean_object* x_2741; 
lean_dec(x_2577);
lean_dec(x_2573);
lean_dec(x_2571);
lean_dec(x_2569);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2740 = lean_ctor_get(x_2587, 0);
lean_inc(x_2740);
x_2741 = lean_ctor_get(x_2587, 1);
lean_inc(x_2741);
lean_dec(x_2587);
x_8 = x_2740;
x_9 = x_2741;
goto block_16;
}
}
}
else
{
lean_object* x_2742; lean_object* x_2743; 
lean_dec(x_2577);
lean_dec(x_2573);
lean_dec(x_2571);
lean_dec(x_2569);
lean_dec(x_2559);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2742 = lean_ctor_get(x_2579, 0);
lean_inc(x_2742);
x_2743 = lean_ctor_get(x_2579, 1);
lean_inc(x_2743);
lean_dec(x_2579);
x_8 = x_2742;
x_9 = x_2743;
goto block_16;
}
}
else
{
lean_object* x_2744; lean_object* x_2745; 
lean_dec(x_2573);
lean_dec(x_2571);
lean_dec(x_2569);
lean_dec(x_2559);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2744 = lean_ctor_get(x_2574, 0);
lean_inc(x_2744);
x_2745 = lean_ctor_get(x_2574, 1);
lean_inc(x_2745);
lean_dec(x_2574);
x_8 = x_2744;
x_9 = x_2745;
goto block_16;
}
}
else
{
lean_object* x_2746; lean_object* x_2747; 
lean_dec(x_2569);
lean_dec(x_2568);
lean_dec(x_2559);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2746 = lean_ctor_get(x_2570, 0);
lean_inc(x_2746);
x_2747 = lean_ctor_get(x_2570, 1);
lean_inc(x_2747);
lean_dec(x_2570);
x_8 = x_2746;
x_9 = x_2747;
goto block_16;
}
}
else
{
lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; 
lean_dec(x_2566);
lean_dec(x_2565);
lean_dec(x_2559);
lean_dec(x_2558);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2748 = lean_ctor_get(x_2563, 1);
lean_inc(x_2748);
if (lean_is_exclusive(x_2563)) {
 lean_ctor_release(x_2563, 0);
 lean_ctor_release(x_2563, 1);
 x_2749 = x_2563;
} else {
 lean_dec_ref(x_2563);
 x_2749 = lean_box(0);
}
x_2750 = lean_box(0);
if (lean_is_scalar(x_2749)) {
 x_2751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2751 = x_2749;
}
lean_ctor_set(x_2751, 0, x_2750);
lean_ctor_set(x_2751, 1, x_2748);
return x_2751;
}
}
else
{
lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; 
lean_dec(x_2565);
lean_dec(x_2564);
lean_dec(x_2559);
lean_dec(x_2558);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2752 = lean_ctor_get(x_2563, 1);
lean_inc(x_2752);
if (lean_is_exclusive(x_2563)) {
 lean_ctor_release(x_2563, 0);
 lean_ctor_release(x_2563, 1);
 x_2753 = x_2563;
} else {
 lean_dec_ref(x_2563);
 x_2753 = lean_box(0);
}
x_2754 = lean_box(0);
if (lean_is_scalar(x_2753)) {
 x_2755 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2755 = x_2753;
}
lean_ctor_set(x_2755, 0, x_2754);
lean_ctor_set(x_2755, 1, x_2752);
return x_2755;
}
}
else
{
lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; 
lean_dec(x_2564);
lean_dec(x_2559);
lean_dec(x_2558);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2756 = lean_ctor_get(x_2563, 1);
lean_inc(x_2756);
if (lean_is_exclusive(x_2563)) {
 lean_ctor_release(x_2563, 0);
 lean_ctor_release(x_2563, 1);
 x_2757 = x_2563;
} else {
 lean_dec_ref(x_2563);
 x_2757 = lean_box(0);
}
x_2758 = lean_box(0);
if (lean_is_scalar(x_2757)) {
 x_2759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2759 = x_2757;
}
lean_ctor_set(x_2759, 0, x_2758);
lean_ctor_set(x_2759, 1, x_2756);
return x_2759;
}
}
else
{
lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; uint8_t x_2763; 
lean_dec(x_2559);
lean_dec(x_2558);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2760 = lean_ctor_get(x_2563, 0);
lean_inc(x_2760);
x_2761 = lean_ctor_get(x_2563, 1);
lean_inc(x_2761);
if (lean_is_exclusive(x_2563)) {
 lean_ctor_release(x_2563, 0);
 lean_ctor_release(x_2563, 1);
 x_2762 = x_2563;
} else {
 lean_dec_ref(x_2563);
 x_2762 = lean_box(0);
}
x_2763 = l_Lean_Exception_isInterrupt(x_2760);
if (x_2763 == 0)
{
uint8_t x_2764; 
x_2764 = l_Lean_Exception_isRuntime(x_2760);
if (x_2764 == 0)
{
lean_object* x_2765; lean_object* x_2766; 
lean_dec(x_2760);
x_2765 = lean_box(0);
if (lean_is_scalar(x_2762)) {
 x_2766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2766 = x_2762;
 lean_ctor_set_tag(x_2766, 0);
}
lean_ctor_set(x_2766, 0, x_2765);
lean_ctor_set(x_2766, 1, x_2761);
return x_2766;
}
else
{
lean_object* x_2767; 
if (lean_is_scalar(x_2762)) {
 x_2767 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2767 = x_2762;
}
lean_ctor_set(x_2767, 0, x_2760);
lean_ctor_set(x_2767, 1, x_2761);
return x_2767;
}
}
else
{
lean_object* x_2768; 
if (lean_is_scalar(x_2762)) {
 x_2768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2768 = x_2762;
}
lean_ctor_set(x_2768, 0, x_2760);
lean_ctor_set(x_2768, 1, x_2761);
return x_2768;
}
}
}
else
{
lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; uint8_t x_2772; 
lean_dec(x_2559);
lean_dec(x_2558);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2769 = lean_ctor_get(x_2560, 0);
lean_inc(x_2769);
x_2770 = lean_ctor_get(x_2560, 1);
lean_inc(x_2770);
if (lean_is_exclusive(x_2560)) {
 lean_ctor_release(x_2560, 0);
 lean_ctor_release(x_2560, 1);
 x_2771 = x_2560;
} else {
 lean_dec_ref(x_2560);
 x_2771 = lean_box(0);
}
x_2772 = l_Lean_Exception_isInterrupt(x_2769);
if (x_2772 == 0)
{
uint8_t x_2773; 
x_2773 = l_Lean_Exception_isRuntime(x_2769);
if (x_2773 == 0)
{
lean_object* x_2774; lean_object* x_2775; 
lean_dec(x_2769);
x_2774 = lean_box(0);
if (lean_is_scalar(x_2771)) {
 x_2775 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2775 = x_2771;
 lean_ctor_set_tag(x_2775, 0);
}
lean_ctor_set(x_2775, 0, x_2774);
lean_ctor_set(x_2775, 1, x_2770);
return x_2775;
}
else
{
lean_object* x_2776; 
if (lean_is_scalar(x_2771)) {
 x_2776 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2776 = x_2771;
}
lean_ctor_set(x_2776, 0, x_2769);
lean_ctor_set(x_2776, 1, x_2770);
return x_2776;
}
}
else
{
lean_object* x_2777; 
if (lean_is_scalar(x_2771)) {
 x_2777 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2777 = x_2771;
}
lean_ctor_set(x_2777, 0, x_2769);
lean_ctor_set(x_2777, 1, x_2770);
return x_2777;
}
}
}
else
{
lean_object* x_2778; lean_object* x_2779; lean_object* x_2780; lean_object* x_2781; 
lean_dec(x_2556);
lean_dec(x_2555);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2778 = lean_ctor_get(x_2553, 1);
lean_inc(x_2778);
if (lean_is_exclusive(x_2553)) {
 lean_ctor_release(x_2553, 0);
 lean_ctor_release(x_2553, 1);
 x_2779 = x_2553;
} else {
 lean_dec_ref(x_2553);
 x_2779 = lean_box(0);
}
x_2780 = lean_box(0);
if (lean_is_scalar(x_2779)) {
 x_2781 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2781 = x_2779;
}
lean_ctor_set(x_2781, 0, x_2780);
lean_ctor_set(x_2781, 1, x_2778);
return x_2781;
}
}
else
{
lean_object* x_2782; lean_object* x_2783; lean_object* x_2784; lean_object* x_2785; 
lean_dec(x_2555);
lean_dec(x_2554);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2782 = lean_ctor_get(x_2553, 1);
lean_inc(x_2782);
if (lean_is_exclusive(x_2553)) {
 lean_ctor_release(x_2553, 0);
 lean_ctor_release(x_2553, 1);
 x_2783 = x_2553;
} else {
 lean_dec_ref(x_2553);
 x_2783 = lean_box(0);
}
x_2784 = lean_box(0);
if (lean_is_scalar(x_2783)) {
 x_2785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2785 = x_2783;
}
lean_ctor_set(x_2785, 0, x_2784);
lean_ctor_set(x_2785, 1, x_2782);
return x_2785;
}
}
else
{
lean_object* x_2786; lean_object* x_2787; lean_object* x_2788; lean_object* x_2789; 
lean_dec(x_2554);
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2786 = lean_ctor_get(x_2553, 1);
lean_inc(x_2786);
if (lean_is_exclusive(x_2553)) {
 lean_ctor_release(x_2553, 0);
 lean_ctor_release(x_2553, 1);
 x_2787 = x_2553;
} else {
 lean_dec_ref(x_2553);
 x_2787 = lean_box(0);
}
x_2788 = lean_box(0);
if (lean_is_scalar(x_2787)) {
 x_2789 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2789 = x_2787;
}
lean_ctor_set(x_2789, 0, x_2788);
lean_ctor_set(x_2789, 1, x_2786);
return x_2789;
}
}
else
{
lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; uint8_t x_2793; 
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2790 = lean_ctor_get(x_2553, 0);
lean_inc(x_2790);
x_2791 = lean_ctor_get(x_2553, 1);
lean_inc(x_2791);
if (lean_is_exclusive(x_2553)) {
 lean_ctor_release(x_2553, 0);
 lean_ctor_release(x_2553, 1);
 x_2792 = x_2553;
} else {
 lean_dec_ref(x_2553);
 x_2792 = lean_box(0);
}
x_2793 = l_Lean_Exception_isInterrupt(x_2790);
if (x_2793 == 0)
{
uint8_t x_2794; 
x_2794 = l_Lean_Exception_isRuntime(x_2790);
if (x_2794 == 0)
{
lean_object* x_2795; lean_object* x_2796; 
lean_dec(x_2790);
x_2795 = lean_box(0);
if (lean_is_scalar(x_2792)) {
 x_2796 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2796 = x_2792;
 lean_ctor_set_tag(x_2796, 0);
}
lean_ctor_set(x_2796, 0, x_2795);
lean_ctor_set(x_2796, 1, x_2791);
return x_2796;
}
else
{
lean_object* x_2797; 
if (lean_is_scalar(x_2792)) {
 x_2797 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2797 = x_2792;
}
lean_ctor_set(x_2797, 0, x_2790);
lean_ctor_set(x_2797, 1, x_2791);
return x_2797;
}
}
else
{
lean_object* x_2798; 
if (lean_is_scalar(x_2792)) {
 x_2798 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2798 = x_2792;
}
lean_ctor_set(x_2798, 0, x_2790);
lean_ctor_set(x_2798, 1, x_2791);
return x_2798;
}
}
}
else
{
lean_object* x_2799; lean_object* x_2800; lean_object* x_2801; uint8_t x_2802; 
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2799 = lean_ctor_get(x_2550, 0);
lean_inc(x_2799);
x_2800 = lean_ctor_get(x_2550, 1);
lean_inc(x_2800);
if (lean_is_exclusive(x_2550)) {
 lean_ctor_release(x_2550, 0);
 lean_ctor_release(x_2550, 1);
 x_2801 = x_2550;
} else {
 lean_dec_ref(x_2550);
 x_2801 = lean_box(0);
}
x_2802 = l_Lean_Exception_isInterrupt(x_2799);
if (x_2802 == 0)
{
uint8_t x_2803; 
x_2803 = l_Lean_Exception_isRuntime(x_2799);
if (x_2803 == 0)
{
lean_object* x_2804; lean_object* x_2805; 
lean_dec(x_2799);
x_2804 = lean_box(0);
if (lean_is_scalar(x_2801)) {
 x_2805 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2805 = x_2801;
 lean_ctor_set_tag(x_2805, 0);
}
lean_ctor_set(x_2805, 0, x_2804);
lean_ctor_set(x_2805, 1, x_2800);
return x_2805;
}
else
{
lean_object* x_2806; 
if (lean_is_scalar(x_2801)) {
 x_2806 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2806 = x_2801;
}
lean_ctor_set(x_2806, 0, x_2799);
lean_ctor_set(x_2806, 1, x_2800);
return x_2806;
}
}
else
{
lean_object* x_2807; 
if (lean_is_scalar(x_2801)) {
 x_2807 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2807 = x_2801;
}
lean_ctor_set(x_2807, 0, x_2799);
lean_ctor_set(x_2807, 1, x_2800);
return x_2807;
}
}
}
}
else
{
lean_object* x_2808; lean_object* x_2809; 
lean_dec(x_40);
lean_dec(x_33);
x_2808 = lean_ctor_get(x_2540, 1);
lean_inc(x_2808);
lean_dec(x_2540);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2809 = l_Lean_Meta_isMonad_x3f(x_2526, x_3, x_4, x_5, x_6, x_2808);
if (lean_obj_tag(x_2809) == 0)
{
lean_object* x_2810; 
x_2810 = lean_ctor_get(x_2809, 0);
lean_inc(x_2810);
if (lean_obj_tag(x_2810) == 0)
{
lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; 
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_free_object(x_43);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2811 = lean_ctor_get(x_2809, 1);
lean_inc(x_2811);
if (lean_is_exclusive(x_2809)) {
 lean_ctor_release(x_2809, 0);
 lean_ctor_release(x_2809, 1);
 x_2812 = x_2809;
} else {
 lean_dec_ref(x_2809);
 x_2812 = lean_box(0);
}
x_2813 = lean_box(0);
if (lean_is_scalar(x_2812)) {
 x_2814 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2814 = x_2812;
}
lean_ctor_set(x_2814, 0, x_2813);
lean_ctor_set(x_2814, 1, x_2811);
return x_2814;
}
else
{
lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; 
x_2815 = lean_ctor_get(x_2809, 1);
lean_inc(x_2815);
lean_dec(x_2809);
x_2816 = lean_ctor_get(x_2810, 0);
lean_inc(x_2816);
if (lean_is_exclusive(x_2810)) {
 lean_ctor_release(x_2810, 0);
 x_2817 = x_2810;
} else {
 lean_dec_ref(x_2810);
 x_2817 = lean_box(0);
}
if (lean_is_scalar(x_2817)) {
 x_2818 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2818 = x_2817;
}
lean_ctor_set(x_2818, 0, x_2537);
if (lean_is_scalar(x_2535)) {
 x_2819 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2819 = x_2535;
}
lean_ctor_set(x_2819, 0, x_2538);
lean_ctor_set(x_43, 0, x_2527);
x_2820 = lean_box(0);
x_2821 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2821, 0, x_2816);
x_2822 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2822, 0, x_1);
x_2823 = lean_box(0);
if (lean_is_scalar(x_2539)) {
 x_2824 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2824 = x_2539;
 lean_ctor_set_tag(x_2824, 1);
}
lean_ctor_set(x_2824, 0, x_2822);
lean_ctor_set(x_2824, 1, x_2823);
x_2825 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2825, 0, x_2821);
lean_ctor_set(x_2825, 1, x_2824);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_2825);
lean_ctor_set(x_38, 0, x_2820);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_43);
x_2826 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2826, 0, x_2819);
lean_ctor_set(x_2826, 1, x_31);
x_2827 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2827, 0, x_2818);
lean_ctor_set(x_2827, 1, x_2826);
x_2828 = lean_array_mk(x_2827);
x_2829 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2830 = l_Lean_Meta_mkAppOptM(x_2829, x_2828, x_3, x_4, x_5, x_6, x_2815);
if (lean_obj_tag(x_2830) == 0)
{
lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; 
x_2831 = lean_ctor_get(x_2830, 0);
lean_inc(x_2831);
x_2832 = lean_ctor_get(x_2830, 1);
lean_inc(x_2832);
lean_dec(x_2830);
x_2833 = l_Lean_Meta_expandCoe(x_2831, x_3, x_4, x_5, x_6, x_2832);
if (lean_obj_tag(x_2833) == 0)
{
lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; 
x_2834 = lean_ctor_get(x_2833, 0);
lean_inc(x_2834);
x_2835 = lean_ctor_get(x_2833, 1);
lean_inc(x_2835);
lean_dec(x_2833);
x_2836 = lean_box(0);
x_2837 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2837, 0, x_2834);
lean_ctor_set(x_2837, 1, x_2836);
x_17 = x_2837;
x_18 = x_2835;
goto block_30;
}
else
{
lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; uint8_t x_2841; 
x_2838 = lean_ctor_get(x_2833, 0);
lean_inc(x_2838);
x_2839 = lean_ctor_get(x_2833, 1);
lean_inc(x_2839);
if (lean_is_exclusive(x_2833)) {
 lean_ctor_release(x_2833, 0);
 lean_ctor_release(x_2833, 1);
 x_2840 = x_2833;
} else {
 lean_dec_ref(x_2833);
 x_2840 = lean_box(0);
}
x_2841 = l_Lean_Exception_isInterrupt(x_2838);
if (x_2841 == 0)
{
uint8_t x_2842; 
x_2842 = l_Lean_Exception_isRuntime(x_2838);
if (x_2842 == 0)
{
lean_object* x_2843; 
lean_dec(x_2840);
lean_dec(x_2838);
x_2843 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_2843;
x_18 = x_2839;
goto block_30;
}
else
{
lean_object* x_2844; 
if (lean_is_scalar(x_2840)) {
 x_2844 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2844 = x_2840;
}
lean_ctor_set(x_2844, 0, x_2838);
lean_ctor_set(x_2844, 1, x_2839);
return x_2844;
}
}
else
{
lean_object* x_2845; 
if (lean_is_scalar(x_2840)) {
 x_2845 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2845 = x_2840;
}
lean_ctor_set(x_2845, 0, x_2838);
lean_ctor_set(x_2845, 1, x_2839);
return x_2845;
}
}
}
else
{
lean_object* x_2846; lean_object* x_2847; lean_object* x_2848; uint8_t x_2849; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2846 = lean_ctor_get(x_2830, 0);
lean_inc(x_2846);
x_2847 = lean_ctor_get(x_2830, 1);
lean_inc(x_2847);
if (lean_is_exclusive(x_2830)) {
 lean_ctor_release(x_2830, 0);
 lean_ctor_release(x_2830, 1);
 x_2848 = x_2830;
} else {
 lean_dec_ref(x_2830);
 x_2848 = lean_box(0);
}
x_2849 = l_Lean_Exception_isInterrupt(x_2846);
if (x_2849 == 0)
{
uint8_t x_2850; 
x_2850 = l_Lean_Exception_isRuntime(x_2846);
if (x_2850 == 0)
{
lean_object* x_2851; 
lean_dec(x_2848);
lean_dec(x_2846);
x_2851 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_2851;
x_18 = x_2847;
goto block_30;
}
else
{
lean_object* x_2852; 
if (lean_is_scalar(x_2848)) {
 x_2852 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2852 = x_2848;
}
lean_ctor_set(x_2852, 0, x_2846);
lean_ctor_set(x_2852, 1, x_2847);
return x_2852;
}
}
else
{
lean_object* x_2853; 
if (lean_is_scalar(x_2848)) {
 x_2853 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2853 = x_2848;
}
lean_ctor_set(x_2853, 0, x_2846);
lean_ctor_set(x_2853, 1, x_2847);
return x_2853;
}
}
}
}
else
{
lean_object* x_2854; lean_object* x_2855; lean_object* x_2856; lean_object* x_2857; 
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_free_object(x_43);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2854 = lean_ctor_get(x_2809, 0);
lean_inc(x_2854);
x_2855 = lean_ctor_get(x_2809, 1);
lean_inc(x_2855);
if (lean_is_exclusive(x_2809)) {
 lean_ctor_release(x_2809, 0);
 lean_ctor_release(x_2809, 1);
 x_2856 = x_2809;
} else {
 lean_dec_ref(x_2809);
 x_2856 = lean_box(0);
}
if (lean_is_scalar(x_2856)) {
 x_2857 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2857 = x_2856;
}
lean_ctor_set(x_2857, 0, x_2854);
lean_ctor_set(x_2857, 1, x_2855);
return x_2857;
}
}
}
else
{
lean_object* x_2858; lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; 
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2535);
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2858 = lean_ctor_get(x_2540, 0);
lean_inc(x_2858);
x_2859 = lean_ctor_get(x_2540, 1);
lean_inc(x_2859);
if (lean_is_exclusive(x_2540)) {
 lean_ctor_release(x_2540, 0);
 lean_ctor_release(x_2540, 1);
 x_2860 = x_2540;
} else {
 lean_dec_ref(x_2540);
 x_2860 = lean_box(0);
}
if (lean_is_scalar(x_2860)) {
 x_2861 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2861 = x_2860;
}
lean_ctor_set(x_2861, 0, x_2858);
lean_ctor_set(x_2861, 1, x_2859);
return x_2861;
}
}
}
else
{
lean_object* x_2862; lean_object* x_2863; lean_object* x_2864; lean_object* x_2865; 
lean_dec(x_2527);
lean_dec(x_2526);
lean_free_object(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2862 = lean_ctor_get(x_2528, 0);
lean_inc(x_2862);
x_2863 = lean_ctor_get(x_2528, 1);
lean_inc(x_2863);
if (lean_is_exclusive(x_2528)) {
 lean_ctor_release(x_2528, 0);
 lean_ctor_release(x_2528, 1);
 x_2864 = x_2528;
} else {
 lean_dec_ref(x_2528);
 x_2864 = lean_box(0);
}
if (lean_is_scalar(x_2864)) {
 x_2865 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2865 = x_2864;
}
lean_ctor_set(x_2865, 0, x_2862);
lean_ctor_set(x_2865, 1, x_2863);
return x_2865;
}
}
}
else
{
lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; lean_object* x_2870; lean_object* x_2871; 
x_2866 = lean_ctor_get(x_43, 0);
lean_inc(x_2866);
lean_dec(x_43);
x_2867 = lean_ctor_get(x_42, 1);
lean_inc(x_2867);
lean_dec(x_42);
x_2868 = lean_ctor_get(x_2866, 0);
lean_inc(x_2868);
x_2869 = lean_ctor_get(x_2866, 1);
lean_inc(x_2869);
if (lean_is_exclusive(x_2866)) {
 lean_ctor_release(x_2866, 0);
 lean_ctor_release(x_2866, 1);
 x_2870 = x_2866;
} else {
 lean_dec_ref(x_2866);
 x_2870 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_2871 = l_Lean_Meta_isTypeApp_x3f(x_40, x_3, x_4, x_5, x_6, x_2867);
if (lean_obj_tag(x_2871) == 0)
{
lean_object* x_2872; 
x_2872 = lean_ctor_get(x_2871, 0);
lean_inc(x_2872);
if (lean_obj_tag(x_2872) == 0)
{
lean_object* x_2873; lean_object* x_2874; lean_object* x_2875; lean_object* x_2876; 
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2873 = lean_ctor_get(x_2871, 1);
lean_inc(x_2873);
if (lean_is_exclusive(x_2871)) {
 lean_ctor_release(x_2871, 0);
 lean_ctor_release(x_2871, 1);
 x_2874 = x_2871;
} else {
 lean_dec_ref(x_2871);
 x_2874 = lean_box(0);
}
x_2875 = lean_box(0);
if (lean_is_scalar(x_2874)) {
 x_2876 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2876 = x_2874;
}
lean_ctor_set(x_2876, 0, x_2875);
lean_ctor_set(x_2876, 1, x_2873);
return x_2876;
}
else
{
lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; 
x_2877 = lean_ctor_get(x_2872, 0);
lean_inc(x_2877);
if (lean_is_exclusive(x_2872)) {
 lean_ctor_release(x_2872, 0);
 x_2878 = x_2872;
} else {
 lean_dec_ref(x_2872);
 x_2878 = lean_box(0);
}
x_2879 = lean_ctor_get(x_2871, 1);
lean_inc(x_2879);
lean_dec(x_2871);
x_2880 = lean_ctor_get(x_2877, 0);
lean_inc(x_2880);
x_2881 = lean_ctor_get(x_2877, 1);
lean_inc(x_2881);
if (lean_is_exclusive(x_2877)) {
 lean_ctor_release(x_2877, 0);
 lean_ctor_release(x_2877, 1);
 x_2882 = x_2877;
} else {
 lean_dec_ref(x_2877);
 x_2882 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2868);
lean_inc(x_2880);
x_2883 = l_Lean_Meta_isExprDefEq(x_2880, x_2868, x_3, x_4, x_5, x_6, x_2879);
if (lean_obj_tag(x_2883) == 0)
{
lean_object* x_2884; uint8_t x_2885; 
x_2884 = lean_ctor_get(x_2883, 0);
lean_inc(x_2884);
x_2885 = lean_unbox(x_2884);
lean_dec(x_2884);
if (x_2885 == 0)
{
lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; lean_object* x_2889; uint8_t x_2890; 
x_2886 = lean_ctor_get(x_2883, 1);
lean_inc(x_2886);
if (lean_is_exclusive(x_2883)) {
 lean_ctor_release(x_2883, 0);
 lean_ctor_release(x_2883, 1);
 x_2887 = x_2883;
} else {
 lean_dec_ref(x_2883);
 x_2887 = lean_box(0);
}
x_2888 = lean_ctor_get(x_5, 2);
lean_inc(x_2888);
x_2889 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_2890 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2888, x_2889);
lean_dec(x_2888);
if (x_2890 == 0)
{
lean_object* x_2891; lean_object* x_2892; 
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2891 = lean_box(0);
if (lean_is_scalar(x_2887)) {
 x_2892 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2892 = x_2887;
}
lean_ctor_set(x_2892, 0, x_2891);
lean_ctor_set(x_2892, 1, x_2886);
return x_2892;
}
else
{
lean_object* x_2893; 
lean_dec(x_2887);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2880);
x_2893 = lean_infer_type(x_2880, x_3, x_4, x_5, x_6, x_2886);
if (lean_obj_tag(x_2893) == 0)
{
lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; 
x_2894 = lean_ctor_get(x_2893, 0);
lean_inc(x_2894);
x_2895 = lean_ctor_get(x_2893, 1);
lean_inc(x_2895);
lean_dec(x_2893);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2896 = lean_whnf(x_2894, x_3, x_4, x_5, x_6, x_2895);
if (lean_obj_tag(x_2896) == 0)
{
lean_object* x_2897; 
x_2897 = lean_ctor_get(x_2896, 0);
lean_inc(x_2897);
if (lean_obj_tag(x_2897) == 7)
{
lean_object* x_2898; 
x_2898 = lean_ctor_get(x_2897, 1);
lean_inc(x_2898);
if (lean_obj_tag(x_2898) == 3)
{
lean_object* x_2899; 
x_2899 = lean_ctor_get(x_2897, 2);
lean_inc(x_2899);
lean_dec(x_2897);
if (lean_obj_tag(x_2899) == 3)
{
lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; 
x_2900 = lean_ctor_get(x_2896, 1);
lean_inc(x_2900);
lean_dec(x_2896);
x_2901 = lean_ctor_get(x_2898, 0);
lean_inc(x_2901);
lean_dec(x_2898);
x_2902 = lean_ctor_get(x_2899, 0);
lean_inc(x_2902);
lean_dec(x_2899);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2868);
x_2903 = lean_infer_type(x_2868, x_3, x_4, x_5, x_6, x_2900);
if (lean_obj_tag(x_2903) == 0)
{
lean_object* x_2904; lean_object* x_2905; lean_object* x_2906; 
x_2904 = lean_ctor_get(x_2903, 0);
lean_inc(x_2904);
x_2905 = lean_ctor_get(x_2903, 1);
lean_inc(x_2905);
lean_dec(x_2903);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2906 = lean_whnf(x_2904, x_3, x_4, x_5, x_6, x_2905);
if (lean_obj_tag(x_2906) == 0)
{
lean_object* x_2907; 
x_2907 = lean_ctor_get(x_2906, 0);
lean_inc(x_2907);
if (lean_obj_tag(x_2907) == 7)
{
lean_object* x_2908; 
x_2908 = lean_ctor_get(x_2907, 1);
lean_inc(x_2908);
if (lean_obj_tag(x_2908) == 3)
{
lean_object* x_2909; 
x_2909 = lean_ctor_get(x_2907, 2);
lean_inc(x_2909);
lean_dec(x_2907);
if (lean_obj_tag(x_2909) == 3)
{
lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; 
x_2910 = lean_ctor_get(x_2906, 1);
lean_inc(x_2910);
lean_dec(x_2906);
x_2911 = lean_ctor_get(x_2908, 0);
lean_inc(x_2911);
lean_dec(x_2908);
x_2912 = lean_ctor_get(x_2909, 0);
lean_inc(x_2912);
lean_dec(x_2909);
x_2913 = l_Lean_Meta_decLevel(x_2901, x_3, x_4, x_5, x_6, x_2910);
if (lean_obj_tag(x_2913) == 0)
{
lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; lean_object* x_2917; 
x_2914 = lean_ctor_get(x_2913, 0);
lean_inc(x_2914);
x_2915 = lean_ctor_get(x_2913, 1);
lean_inc(x_2915);
if (lean_is_exclusive(x_2913)) {
 lean_ctor_release(x_2913, 0);
 lean_ctor_release(x_2913, 1);
 x_2916 = x_2913;
} else {
 lean_dec_ref(x_2913);
 x_2916 = lean_box(0);
}
x_2917 = l_Lean_Meta_decLevel(x_2911, x_3, x_4, x_5, x_6, x_2915);
if (lean_obj_tag(x_2917) == 0)
{
lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; uint8_t x_2921; lean_object* x_2922; 
x_2918 = lean_ctor_get(x_2917, 0);
lean_inc(x_2918);
x_2919 = lean_ctor_get(x_2917, 1);
lean_inc(x_2919);
if (lean_is_exclusive(x_2917)) {
 lean_ctor_release(x_2917, 0);
 lean_ctor_release(x_2917, 1);
 x_2920 = x_2917;
} else {
 lean_dec_ref(x_2917);
 x_2920 = lean_box(0);
}
x_2921 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2914);
x_2922 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_2914, x_2918, x_2921, x_3, x_4, x_5, x_6, x_2919);
if (lean_obj_tag(x_2922) == 0)
{
lean_object* x_2923; uint8_t x_2924; 
x_2923 = lean_ctor_get(x_2922, 0);
lean_inc(x_2923);
x_2924 = lean_unbox(x_2923);
lean_dec(x_2923);
if (x_2924 == 0)
{
lean_object* x_2925; lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; 
lean_dec(x_2920);
lean_dec(x_2916);
lean_dec(x_2914);
lean_dec(x_2912);
lean_dec(x_2902);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2925 = lean_ctor_get(x_2922, 1);
lean_inc(x_2925);
if (lean_is_exclusive(x_2922)) {
 lean_ctor_release(x_2922, 0);
 lean_ctor_release(x_2922, 1);
 x_2926 = x_2922;
} else {
 lean_dec_ref(x_2922);
 x_2926 = lean_box(0);
}
x_2927 = lean_box(0);
if (lean_is_scalar(x_2926)) {
 x_2928 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2928 = x_2926;
}
lean_ctor_set(x_2928, 0, x_2927);
lean_ctor_set(x_2928, 1, x_2925);
return x_2928;
}
else
{
lean_object* x_2929; lean_object* x_2930; 
x_2929 = lean_ctor_get(x_2922, 1);
lean_inc(x_2929);
lean_dec(x_2922);
x_2930 = l_Lean_Meta_decLevel(x_2902, x_3, x_4, x_5, x_6, x_2929);
if (lean_obj_tag(x_2930) == 0)
{
lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; 
x_2931 = lean_ctor_get(x_2930, 0);
lean_inc(x_2931);
x_2932 = lean_ctor_get(x_2930, 1);
lean_inc(x_2932);
if (lean_is_exclusive(x_2930)) {
 lean_ctor_release(x_2930, 0);
 lean_ctor_release(x_2930, 1);
 x_2933 = x_2930;
} else {
 lean_dec_ref(x_2930);
 x_2933 = lean_box(0);
}
x_2934 = l_Lean_Meta_decLevel(x_2912, x_3, x_4, x_5, x_6, x_2932);
if (lean_obj_tag(x_2934) == 0)
{
lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; lean_object* x_2941; lean_object* x_2942; lean_object* x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; lean_object* x_2947; lean_object* x_2948; lean_object* x_2949; 
x_2935 = lean_ctor_get(x_2934, 0);
lean_inc(x_2935);
x_2936 = lean_ctor_get(x_2934, 1);
lean_inc(x_2936);
if (lean_is_exclusive(x_2934)) {
 lean_ctor_release(x_2934, 0);
 lean_ctor_release(x_2934, 1);
 x_2937 = x_2934;
} else {
 lean_dec_ref(x_2934);
 x_2937 = lean_box(0);
}
x_2938 = lean_box(0);
if (lean_is_scalar(x_2937)) {
 x_2939 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2939 = x_2937;
 lean_ctor_set_tag(x_2939, 1);
}
lean_ctor_set(x_2939, 0, x_2935);
lean_ctor_set(x_2939, 1, x_2938);
if (lean_is_scalar(x_2933)) {
 x_2940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2940 = x_2933;
 lean_ctor_set_tag(x_2940, 1);
}
lean_ctor_set(x_2940, 0, x_2931);
lean_ctor_set(x_2940, 1, x_2939);
if (lean_is_scalar(x_2920)) {
 x_2941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2941 = x_2920;
 lean_ctor_set_tag(x_2941, 1);
}
lean_ctor_set(x_2941, 0, x_2914);
lean_ctor_set(x_2941, 1, x_2940);
x_2942 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2943 = l_Lean_Expr_const___override(x_2942, x_2941);
lean_inc(x_2868);
if (lean_is_scalar(x_2916)) {
 x_2944 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2944 = x_2916;
 lean_ctor_set_tag(x_2944, 1);
}
lean_ctor_set(x_2944, 0, x_2868);
lean_ctor_set(x_2944, 1, x_2938);
lean_inc(x_2880);
if (lean_is_scalar(x_2882)) {
 x_2945 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2945 = x_2882;
 lean_ctor_set_tag(x_2945, 1);
}
lean_ctor_set(x_2945, 0, x_2880);
lean_ctor_set(x_2945, 1, x_2944);
x_2946 = lean_array_mk(x_2945);
x_2947 = l_Lean_mkAppN(x_2943, x_2946);
lean_dec(x_2946);
x_2948 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2949 = l_Lean_Meta_trySynthInstance(x_2947, x_2948, x_3, x_4, x_5, x_6, x_2936);
if (lean_obj_tag(x_2949) == 0)
{
lean_object* x_2950; 
x_2950 = lean_ctor_get(x_2949, 0);
lean_inc(x_2950);
if (lean_obj_tag(x_2950) == 1)
{
lean_object* x_2951; lean_object* x_2952; lean_object* x_2953; 
x_2951 = lean_ctor_get(x_2949, 1);
lean_inc(x_2951);
lean_dec(x_2949);
x_2952 = lean_ctor_get(x_2950, 0);
lean_inc(x_2952);
lean_dec(x_2950);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2881);
x_2953 = l_Lean_Meta_getDecLevel(x_2881, x_3, x_4, x_5, x_6, x_2951);
if (lean_obj_tag(x_2953) == 0)
{
lean_object* x_2954; lean_object* x_2955; lean_object* x_2956; lean_object* x_2957; 
x_2954 = lean_ctor_get(x_2953, 0);
lean_inc(x_2954);
x_2955 = lean_ctor_get(x_2953, 1);
lean_inc(x_2955);
if (lean_is_exclusive(x_2953)) {
 lean_ctor_release(x_2953, 0);
 lean_ctor_release(x_2953, 1);
 x_2956 = x_2953;
} else {
 lean_dec_ref(x_2953);
 x_2956 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2957 = l_Lean_Meta_getDecLevel(x_40, x_3, x_4, x_5, x_6, x_2955);
if (lean_obj_tag(x_2957) == 0)
{
lean_object* x_2958; lean_object* x_2959; lean_object* x_2960; lean_object* x_2961; 
x_2958 = lean_ctor_get(x_2957, 0);
lean_inc(x_2958);
x_2959 = lean_ctor_get(x_2957, 1);
lean_inc(x_2959);
if (lean_is_exclusive(x_2957)) {
 lean_ctor_release(x_2957, 0);
 lean_ctor_release(x_2957, 1);
 x_2960 = x_2957;
} else {
 lean_dec_ref(x_2957);
 x_2960 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_2961 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_2959);
if (lean_obj_tag(x_2961) == 0)
{
lean_object* x_2962; lean_object* x_2963; lean_object* x_2964; lean_object* x_2965; lean_object* x_2966; lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; 
x_2962 = lean_ctor_get(x_2961, 0);
lean_inc(x_2962);
x_2963 = lean_ctor_get(x_2961, 1);
lean_inc(x_2963);
if (lean_is_exclusive(x_2961)) {
 lean_ctor_release(x_2961, 0);
 lean_ctor_release(x_2961, 1);
 x_2964 = x_2961;
} else {
 lean_dec_ref(x_2961);
 x_2964 = lean_box(0);
}
if (lean_is_scalar(x_2964)) {
 x_2965 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2965 = x_2964;
 lean_ctor_set_tag(x_2965, 1);
}
lean_ctor_set(x_2965, 0, x_2962);
lean_ctor_set(x_2965, 1, x_2938);
if (lean_is_scalar(x_2960)) {
 x_2966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2966 = x_2960;
 lean_ctor_set_tag(x_2966, 1);
}
lean_ctor_set(x_2966, 0, x_2958);
lean_ctor_set(x_2966, 1, x_2965);
if (lean_is_scalar(x_2956)) {
 x_2967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2967 = x_2956;
 lean_ctor_set_tag(x_2967, 1);
}
lean_ctor_set(x_2967, 0, x_2954);
lean_ctor_set(x_2967, 1, x_2966);
x_2968 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_2967);
x_2969 = l_Lean_Expr_const___override(x_2968, x_2967);
if (lean_is_scalar(x_2870)) {
 x_2970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2970 = x_2870;
 lean_ctor_set_tag(x_2970, 1);
}
lean_ctor_set(x_2970, 0, x_1);
lean_ctor_set(x_2970, 1, x_2938);
lean_inc(x_2970);
lean_inc(x_2881);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_2970);
lean_ctor_set(x_38, 0, x_2881);
lean_inc(x_2952);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_2952);
lean_inc(x_2868);
x_2971 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2971, 0, x_2868);
lean_ctor_set(x_2971, 1, x_31);
lean_inc(x_2880);
x_2972 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2972, 0, x_2880);
lean_ctor_set(x_2972, 1, x_2971);
x_2973 = lean_array_mk(x_2972);
x_2974 = l_Lean_mkAppN(x_2969, x_2973);
lean_dec(x_2973);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2974);
x_2975 = lean_infer_type(x_2974, x_3, x_4, x_5, x_6, x_2963);
if (lean_obj_tag(x_2975) == 0)
{
lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; 
x_2976 = lean_ctor_get(x_2975, 0);
lean_inc(x_2976);
x_2977 = lean_ctor_get(x_2975, 1);
lean_inc(x_2977);
if (lean_is_exclusive(x_2975)) {
 lean_ctor_release(x_2975, 0);
 lean_ctor_release(x_2975, 1);
 x_2978 = x_2975;
} else {
 lean_dec_ref(x_2975);
 x_2978 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_2979 = l_Lean_Meta_isExprDefEq(x_33, x_2976, x_3, x_4, x_5, x_6, x_2977);
if (lean_obj_tag(x_2979) == 0)
{
lean_object* x_2980; uint8_t x_2981; 
x_2980 = lean_ctor_get(x_2979, 0);
lean_inc(x_2980);
x_2981 = lean_unbox(x_2980);
lean_dec(x_2980);
if (x_2981 == 0)
{
lean_object* x_2982; lean_object* x_2983; 
lean_dec(x_2974);
lean_dec(x_2878);
x_2982 = lean_ctor_get(x_2979, 1);
lean_inc(x_2982);
lean_dec(x_2979);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2868);
x_2983 = l_Lean_Meta_isMonad_x3f(x_2868, x_3, x_4, x_5, x_6, x_2982);
if (lean_obj_tag(x_2983) == 0)
{
lean_object* x_2984; 
x_2984 = lean_ctor_get(x_2983, 0);
lean_inc(x_2984);
if (lean_obj_tag(x_2984) == 0)
{
lean_object* x_2985; lean_object* x_2986; lean_object* x_2987; 
lean_dec(x_2978);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2985 = lean_ctor_get(x_2983, 1);
lean_inc(x_2985);
if (lean_is_exclusive(x_2983)) {
 lean_ctor_release(x_2983, 0);
 lean_ctor_release(x_2983, 1);
 x_2986 = x_2983;
} else {
 lean_dec_ref(x_2983);
 x_2986 = lean_box(0);
}
if (lean_is_scalar(x_2986)) {
 x_2987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2987 = x_2986;
}
lean_ctor_set(x_2987, 0, x_2948);
lean_ctor_set(x_2987, 1, x_2985);
return x_2987;
}
else
{
lean_object* x_2988; lean_object* x_2989; lean_object* x_2990; 
x_2988 = lean_ctor_get(x_2983, 1);
lean_inc(x_2988);
lean_dec(x_2983);
x_2989 = lean_ctor_get(x_2984, 0);
lean_inc(x_2989);
lean_dec(x_2984);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2881);
x_2990 = l_Lean_Meta_getLevel(x_2881, x_3, x_4, x_5, x_6, x_2988);
if (lean_obj_tag(x_2990) == 0)
{
lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; 
x_2991 = lean_ctor_get(x_2990, 0);
lean_inc(x_2991);
x_2992 = lean_ctor_get(x_2990, 1);
lean_inc(x_2992);
if (lean_is_exclusive(x_2990)) {
 lean_ctor_release(x_2990, 0);
 lean_ctor_release(x_2990, 1);
 x_2993 = x_2990;
} else {
 lean_dec_ref(x_2990);
 x_2993 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2869);
x_2994 = l_Lean_Meta_getLevel(x_2869, x_3, x_4, x_5, x_6, x_2992);
if (lean_obj_tag(x_2994) == 0)
{
lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; lean_object* x_3004; lean_object* x_3005; lean_object* x_3006; lean_object* x_3007; lean_object* x_3008; uint8_t x_3009; lean_object* x_3010; lean_object* x_3011; 
x_2995 = lean_ctor_get(x_2994, 0);
lean_inc(x_2995);
x_2996 = lean_ctor_get(x_2994, 1);
lean_inc(x_2996);
if (lean_is_exclusive(x_2994)) {
 lean_ctor_release(x_2994, 0);
 lean_ctor_release(x_2994, 1);
 x_2997 = x_2994;
} else {
 lean_dec_ref(x_2994);
 x_2997 = lean_box(0);
}
if (lean_is_scalar(x_2997)) {
 x_2998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2998 = x_2997;
 lean_ctor_set_tag(x_2998, 1);
}
lean_ctor_set(x_2998, 0, x_2995);
lean_ctor_set(x_2998, 1, x_2938);
if (lean_is_scalar(x_2993)) {
 x_2999 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2999 = x_2993;
 lean_ctor_set_tag(x_2999, 1);
}
lean_ctor_set(x_2999, 0, x_2991);
lean_ctor_set(x_2999, 1, x_2998);
x_3000 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_3001 = l_Lean_Expr_const___override(x_3000, x_2999);
lean_inc(x_2869);
if (lean_is_scalar(x_2978)) {
 x_3002 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3002 = x_2978;
 lean_ctor_set_tag(x_3002, 1);
}
lean_ctor_set(x_3002, 0, x_2869);
lean_ctor_set(x_3002, 1, x_2938);
x_3003 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_3004 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3004, 0, x_3003);
lean_ctor_set(x_3004, 1, x_3002);
lean_inc(x_2881);
x_3005 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3005, 0, x_2881);
lean_ctor_set(x_3005, 1, x_3004);
x_3006 = lean_array_mk(x_3005);
x_3007 = l_Lean_mkAppN(x_3001, x_3006);
lean_dec(x_3006);
x_3008 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_3009 = 0;
lean_inc(x_2881);
x_3010 = l_Lean_Expr_forallE___override(x_3008, x_2881, x_3007, x_3009);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3011 = l_Lean_Meta_trySynthInstance(x_3010, x_2948, x_3, x_4, x_5, x_6, x_2996);
if (lean_obj_tag(x_3011) == 0)
{
lean_object* x_3012; 
x_3012 = lean_ctor_get(x_3011, 0);
lean_inc(x_3012);
if (lean_obj_tag(x_3012) == 1)
{
lean_object* x_3013; lean_object* x_3014; lean_object* x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; 
x_3013 = lean_ctor_get(x_3011, 1);
lean_inc(x_3013);
lean_dec(x_3011);
x_3014 = lean_ctor_get(x_3012, 0);
lean_inc(x_3014);
lean_dec(x_3012);
x_3015 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_3016 = l_Lean_Expr_const___override(x_3015, x_2967);
x_3017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3017, 0, x_2989);
lean_ctor_set(x_3017, 1, x_2970);
x_3018 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3018, 0, x_3014);
lean_ctor_set(x_3018, 1, x_3017);
x_3019 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3019, 0, x_2952);
lean_ctor_set(x_3019, 1, x_3018);
x_3020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3020, 0, x_2869);
lean_ctor_set(x_3020, 1, x_3019);
x_3021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3021, 0, x_2881);
lean_ctor_set(x_3021, 1, x_3020);
x_3022 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3022, 0, x_2868);
lean_ctor_set(x_3022, 1, x_3021);
x_3023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3023, 0, x_2880);
lean_ctor_set(x_3023, 1, x_3022);
x_3024 = lean_array_mk(x_3023);
x_3025 = l_Lean_mkAppN(x_3016, x_3024);
lean_dec(x_3024);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3026 = l_Lean_Meta_expandCoe(x_3025, x_3, x_4, x_5, x_6, x_3013);
if (lean_obj_tag(x_3026) == 0)
{
lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; 
x_3027 = lean_ctor_get(x_3026, 0);
lean_inc(x_3027);
x_3028 = lean_ctor_get(x_3026, 1);
lean_inc(x_3028);
lean_dec(x_3026);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3027);
x_3029 = lean_infer_type(x_3027, x_3, x_4, x_5, x_6, x_3028);
if (lean_obj_tag(x_3029) == 0)
{
lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; 
x_3030 = lean_ctor_get(x_3029, 0);
lean_inc(x_3030);
x_3031 = lean_ctor_get(x_3029, 1);
lean_inc(x_3031);
lean_dec(x_3029);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3032 = l_Lean_Meta_isExprDefEq(x_33, x_3030, x_3, x_4, x_5, x_6, x_3031);
if (lean_obj_tag(x_3032) == 0)
{
lean_object* x_3033; uint8_t x_3034; 
x_3033 = lean_ctor_get(x_3032, 0);
lean_inc(x_3033);
x_3034 = lean_unbox(x_3033);
lean_dec(x_3033);
if (x_3034 == 0)
{
lean_object* x_3035; lean_object* x_3036; lean_object* x_3037; 
lean_dec(x_3027);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3035 = lean_ctor_get(x_3032, 1);
lean_inc(x_3035);
if (lean_is_exclusive(x_3032)) {
 lean_ctor_release(x_3032, 0);
 lean_ctor_release(x_3032, 1);
 x_3036 = x_3032;
} else {
 lean_dec_ref(x_3032);
 x_3036 = lean_box(0);
}
if (lean_is_scalar(x_3036)) {
 x_3037 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3037 = x_3036;
}
lean_ctor_set(x_3037, 0, x_2948);
lean_ctor_set(x_3037, 1, x_3035);
return x_3037;
}
else
{
lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; 
x_3038 = lean_ctor_get(x_3032, 1);
lean_inc(x_3038);
lean_dec(x_3032);
x_3039 = lean_box(0);
x_3040 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_3027, x_3039, x_3, x_4, x_5, x_6, x_3038);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3041 = lean_ctor_get(x_3040, 0);
lean_inc(x_3041);
x_3042 = lean_ctor_get(x_3040, 1);
lean_inc(x_3042);
if (lean_is_exclusive(x_3040)) {
 lean_ctor_release(x_3040, 0);
 lean_ctor_release(x_3040, 1);
 x_3043 = x_3040;
} else {
 lean_dec_ref(x_3040);
 x_3043 = lean_box(0);
}
if (lean_is_scalar(x_3043)) {
 x_3044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3044 = x_3043;
}
lean_ctor_set(x_3044, 0, x_3041);
lean_ctor_set(x_3044, 1, x_3042);
return x_3044;
}
}
else
{
lean_object* x_3045; lean_object* x_3046; 
lean_dec(x_3027);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3045 = lean_ctor_get(x_3032, 0);
lean_inc(x_3045);
x_3046 = lean_ctor_get(x_3032, 1);
lean_inc(x_3046);
lean_dec(x_3032);
x_8 = x_3045;
x_9 = x_3046;
goto block_16;
}
}
else
{
lean_object* x_3047; lean_object* x_3048; 
lean_dec(x_3027);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3047 = lean_ctor_get(x_3029, 0);
lean_inc(x_3047);
x_3048 = lean_ctor_get(x_3029, 1);
lean_inc(x_3048);
lean_dec(x_3029);
x_8 = x_3047;
x_9 = x_3048;
goto block_16;
}
}
else
{
lean_object* x_3049; lean_object* x_3050; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3049 = lean_ctor_get(x_3026, 0);
lean_inc(x_3049);
x_3050 = lean_ctor_get(x_3026, 1);
lean_inc(x_3050);
lean_dec(x_3026);
x_8 = x_3049;
x_9 = x_3050;
goto block_16;
}
}
else
{
lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; 
lean_dec(x_3012);
lean_dec(x_2989);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3051 = lean_ctor_get(x_3011, 1);
lean_inc(x_3051);
if (lean_is_exclusive(x_3011)) {
 lean_ctor_release(x_3011, 0);
 lean_ctor_release(x_3011, 1);
 x_3052 = x_3011;
} else {
 lean_dec_ref(x_3011);
 x_3052 = lean_box(0);
}
if (lean_is_scalar(x_3052)) {
 x_3053 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3053 = x_3052;
}
lean_ctor_set(x_3053, 0, x_2948);
lean_ctor_set(x_3053, 1, x_3051);
return x_3053;
}
}
else
{
lean_object* x_3054; lean_object* x_3055; 
lean_dec(x_2989);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3054 = lean_ctor_get(x_3011, 0);
lean_inc(x_3054);
x_3055 = lean_ctor_get(x_3011, 1);
lean_inc(x_3055);
lean_dec(x_3011);
x_8 = x_3054;
x_9 = x_3055;
goto block_16;
}
}
else
{
lean_object* x_3056; lean_object* x_3057; 
lean_dec(x_2993);
lean_dec(x_2991);
lean_dec(x_2989);
lean_dec(x_2978);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3056 = lean_ctor_get(x_2994, 0);
lean_inc(x_3056);
x_3057 = lean_ctor_get(x_2994, 1);
lean_inc(x_3057);
lean_dec(x_2994);
x_8 = x_3056;
x_9 = x_3057;
goto block_16;
}
}
else
{
lean_object* x_3058; lean_object* x_3059; 
lean_dec(x_2989);
lean_dec(x_2978);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3058 = lean_ctor_get(x_2990, 0);
lean_inc(x_3058);
x_3059 = lean_ctor_get(x_2990, 1);
lean_inc(x_3059);
lean_dec(x_2990);
x_8 = x_3058;
x_9 = x_3059;
goto block_16;
}
}
}
else
{
lean_object* x_3060; lean_object* x_3061; 
lean_dec(x_2978);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3060 = lean_ctor_get(x_2983, 0);
lean_inc(x_3060);
x_3061 = lean_ctor_get(x_2983, 1);
lean_inc(x_3061);
lean_dec(x_2983);
x_8 = x_3060;
x_9 = x_3061;
goto block_16;
}
}
else
{
lean_object* x_3062; lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; 
lean_dec(x_2978);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3062 = lean_ctor_get(x_2979, 1);
lean_inc(x_3062);
if (lean_is_exclusive(x_2979)) {
 lean_ctor_release(x_2979, 0);
 lean_ctor_release(x_2979, 1);
 x_3063 = x_2979;
} else {
 lean_dec_ref(x_2979);
 x_3063 = lean_box(0);
}
if (lean_is_scalar(x_2878)) {
 x_3064 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3064 = x_2878;
}
lean_ctor_set(x_3064, 0, x_2974);
if (lean_is_scalar(x_3063)) {
 x_3065 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3065 = x_3063;
}
lean_ctor_set(x_3065, 0, x_3064);
lean_ctor_set(x_3065, 1, x_3062);
return x_3065;
}
}
else
{
lean_object* x_3066; lean_object* x_3067; 
lean_dec(x_2978);
lean_dec(x_2974);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3066 = lean_ctor_get(x_2979, 0);
lean_inc(x_3066);
x_3067 = lean_ctor_get(x_2979, 1);
lean_inc(x_3067);
lean_dec(x_2979);
x_8 = x_3066;
x_9 = x_3067;
goto block_16;
}
}
else
{
lean_object* x_3068; lean_object* x_3069; 
lean_dec(x_2974);
lean_dec(x_2970);
lean_dec(x_2967);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3068 = lean_ctor_get(x_2975, 0);
lean_inc(x_3068);
x_3069 = lean_ctor_get(x_2975, 1);
lean_inc(x_3069);
lean_dec(x_2975);
x_8 = x_3068;
x_9 = x_3069;
goto block_16;
}
}
else
{
lean_object* x_3070; lean_object* x_3071; 
lean_dec(x_2960);
lean_dec(x_2958);
lean_dec(x_2956);
lean_dec(x_2954);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3070 = lean_ctor_get(x_2961, 0);
lean_inc(x_3070);
x_3071 = lean_ctor_get(x_2961, 1);
lean_inc(x_3071);
lean_dec(x_2961);
x_8 = x_3070;
x_9 = x_3071;
goto block_16;
}
}
else
{
lean_object* x_3072; lean_object* x_3073; 
lean_dec(x_2956);
lean_dec(x_2954);
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3072 = lean_ctor_get(x_2957, 0);
lean_inc(x_3072);
x_3073 = lean_ctor_get(x_2957, 1);
lean_inc(x_3073);
lean_dec(x_2957);
x_8 = x_3072;
x_9 = x_3073;
goto block_16;
}
}
else
{
lean_object* x_3074; lean_object* x_3075; 
lean_dec(x_2952);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3074 = lean_ctor_get(x_2953, 0);
lean_inc(x_3074);
x_3075 = lean_ctor_get(x_2953, 1);
lean_inc(x_3075);
lean_dec(x_2953);
x_8 = x_3074;
x_9 = x_3075;
goto block_16;
}
}
else
{
lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; 
lean_dec(x_2950);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3076 = lean_ctor_get(x_2949, 1);
lean_inc(x_3076);
if (lean_is_exclusive(x_2949)) {
 lean_ctor_release(x_2949, 0);
 lean_ctor_release(x_2949, 1);
 x_3077 = x_2949;
} else {
 lean_dec_ref(x_2949);
 x_3077 = lean_box(0);
}
if (lean_is_scalar(x_3077)) {
 x_3078 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3078 = x_3077;
}
lean_ctor_set(x_3078, 0, x_2948);
lean_ctor_set(x_3078, 1, x_3076);
return x_3078;
}
}
else
{
lean_object* x_3079; lean_object* x_3080; 
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3079 = lean_ctor_get(x_2949, 0);
lean_inc(x_3079);
x_3080 = lean_ctor_get(x_2949, 1);
lean_inc(x_3080);
lean_dec(x_2949);
x_8 = x_3079;
x_9 = x_3080;
goto block_16;
}
}
else
{
lean_object* x_3081; lean_object* x_3082; 
lean_dec(x_2933);
lean_dec(x_2931);
lean_dec(x_2920);
lean_dec(x_2916);
lean_dec(x_2914);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3081 = lean_ctor_get(x_2934, 0);
lean_inc(x_3081);
x_3082 = lean_ctor_get(x_2934, 1);
lean_inc(x_3082);
lean_dec(x_2934);
x_8 = x_3081;
x_9 = x_3082;
goto block_16;
}
}
else
{
lean_object* x_3083; lean_object* x_3084; 
lean_dec(x_2920);
lean_dec(x_2916);
lean_dec(x_2914);
lean_dec(x_2912);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3083 = lean_ctor_get(x_2930, 0);
lean_inc(x_3083);
x_3084 = lean_ctor_get(x_2930, 1);
lean_inc(x_3084);
lean_dec(x_2930);
x_8 = x_3083;
x_9 = x_3084;
goto block_16;
}
}
}
else
{
lean_object* x_3085; lean_object* x_3086; 
lean_dec(x_2920);
lean_dec(x_2916);
lean_dec(x_2914);
lean_dec(x_2912);
lean_dec(x_2902);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3085 = lean_ctor_get(x_2922, 0);
lean_inc(x_3085);
x_3086 = lean_ctor_get(x_2922, 1);
lean_inc(x_3086);
lean_dec(x_2922);
x_8 = x_3085;
x_9 = x_3086;
goto block_16;
}
}
else
{
lean_object* x_3087; lean_object* x_3088; 
lean_dec(x_2916);
lean_dec(x_2914);
lean_dec(x_2912);
lean_dec(x_2902);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3087 = lean_ctor_get(x_2917, 0);
lean_inc(x_3087);
x_3088 = lean_ctor_get(x_2917, 1);
lean_inc(x_3088);
lean_dec(x_2917);
x_8 = x_3087;
x_9 = x_3088;
goto block_16;
}
}
else
{
lean_object* x_3089; lean_object* x_3090; 
lean_dec(x_2912);
lean_dec(x_2911);
lean_dec(x_2902);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3089 = lean_ctor_get(x_2913, 0);
lean_inc(x_3089);
x_3090 = lean_ctor_get(x_2913, 1);
lean_inc(x_3090);
lean_dec(x_2913);
x_8 = x_3089;
x_9 = x_3090;
goto block_16;
}
}
else
{
lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; 
lean_dec(x_2909);
lean_dec(x_2908);
lean_dec(x_2902);
lean_dec(x_2901);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3091 = lean_ctor_get(x_2906, 1);
lean_inc(x_3091);
if (lean_is_exclusive(x_2906)) {
 lean_ctor_release(x_2906, 0);
 lean_ctor_release(x_2906, 1);
 x_3092 = x_2906;
} else {
 lean_dec_ref(x_2906);
 x_3092 = lean_box(0);
}
x_3093 = lean_box(0);
if (lean_is_scalar(x_3092)) {
 x_3094 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3094 = x_3092;
}
lean_ctor_set(x_3094, 0, x_3093);
lean_ctor_set(x_3094, 1, x_3091);
return x_3094;
}
}
else
{
lean_object* x_3095; lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; 
lean_dec(x_2908);
lean_dec(x_2907);
lean_dec(x_2902);
lean_dec(x_2901);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3095 = lean_ctor_get(x_2906, 1);
lean_inc(x_3095);
if (lean_is_exclusive(x_2906)) {
 lean_ctor_release(x_2906, 0);
 lean_ctor_release(x_2906, 1);
 x_3096 = x_2906;
} else {
 lean_dec_ref(x_2906);
 x_3096 = lean_box(0);
}
x_3097 = lean_box(0);
if (lean_is_scalar(x_3096)) {
 x_3098 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3098 = x_3096;
}
lean_ctor_set(x_3098, 0, x_3097);
lean_ctor_set(x_3098, 1, x_3095);
return x_3098;
}
}
else
{
lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; lean_object* x_3102; 
lean_dec(x_2907);
lean_dec(x_2902);
lean_dec(x_2901);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3099 = lean_ctor_get(x_2906, 1);
lean_inc(x_3099);
if (lean_is_exclusive(x_2906)) {
 lean_ctor_release(x_2906, 0);
 lean_ctor_release(x_2906, 1);
 x_3100 = x_2906;
} else {
 lean_dec_ref(x_2906);
 x_3100 = lean_box(0);
}
x_3101 = lean_box(0);
if (lean_is_scalar(x_3100)) {
 x_3102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3102 = x_3100;
}
lean_ctor_set(x_3102, 0, x_3101);
lean_ctor_set(x_3102, 1, x_3099);
return x_3102;
}
}
else
{
lean_object* x_3103; lean_object* x_3104; lean_object* x_3105; uint8_t x_3106; 
lean_dec(x_2902);
lean_dec(x_2901);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3103 = lean_ctor_get(x_2906, 0);
lean_inc(x_3103);
x_3104 = lean_ctor_get(x_2906, 1);
lean_inc(x_3104);
if (lean_is_exclusive(x_2906)) {
 lean_ctor_release(x_2906, 0);
 lean_ctor_release(x_2906, 1);
 x_3105 = x_2906;
} else {
 lean_dec_ref(x_2906);
 x_3105 = lean_box(0);
}
x_3106 = l_Lean_Exception_isInterrupt(x_3103);
if (x_3106 == 0)
{
uint8_t x_3107; 
x_3107 = l_Lean_Exception_isRuntime(x_3103);
if (x_3107 == 0)
{
lean_object* x_3108; lean_object* x_3109; 
lean_dec(x_3103);
x_3108 = lean_box(0);
if (lean_is_scalar(x_3105)) {
 x_3109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3109 = x_3105;
 lean_ctor_set_tag(x_3109, 0);
}
lean_ctor_set(x_3109, 0, x_3108);
lean_ctor_set(x_3109, 1, x_3104);
return x_3109;
}
else
{
lean_object* x_3110; 
if (lean_is_scalar(x_3105)) {
 x_3110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3110 = x_3105;
}
lean_ctor_set(x_3110, 0, x_3103);
lean_ctor_set(x_3110, 1, x_3104);
return x_3110;
}
}
else
{
lean_object* x_3111; 
if (lean_is_scalar(x_3105)) {
 x_3111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3111 = x_3105;
}
lean_ctor_set(x_3111, 0, x_3103);
lean_ctor_set(x_3111, 1, x_3104);
return x_3111;
}
}
}
else
{
lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; uint8_t x_3115; 
lean_dec(x_2902);
lean_dec(x_2901);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3112 = lean_ctor_get(x_2903, 0);
lean_inc(x_3112);
x_3113 = lean_ctor_get(x_2903, 1);
lean_inc(x_3113);
if (lean_is_exclusive(x_2903)) {
 lean_ctor_release(x_2903, 0);
 lean_ctor_release(x_2903, 1);
 x_3114 = x_2903;
} else {
 lean_dec_ref(x_2903);
 x_3114 = lean_box(0);
}
x_3115 = l_Lean_Exception_isInterrupt(x_3112);
if (x_3115 == 0)
{
uint8_t x_3116; 
x_3116 = l_Lean_Exception_isRuntime(x_3112);
if (x_3116 == 0)
{
lean_object* x_3117; lean_object* x_3118; 
lean_dec(x_3112);
x_3117 = lean_box(0);
if (lean_is_scalar(x_3114)) {
 x_3118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3118 = x_3114;
 lean_ctor_set_tag(x_3118, 0);
}
lean_ctor_set(x_3118, 0, x_3117);
lean_ctor_set(x_3118, 1, x_3113);
return x_3118;
}
else
{
lean_object* x_3119; 
if (lean_is_scalar(x_3114)) {
 x_3119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3119 = x_3114;
}
lean_ctor_set(x_3119, 0, x_3112);
lean_ctor_set(x_3119, 1, x_3113);
return x_3119;
}
}
else
{
lean_object* x_3120; 
if (lean_is_scalar(x_3114)) {
 x_3120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3120 = x_3114;
}
lean_ctor_set(x_3120, 0, x_3112);
lean_ctor_set(x_3120, 1, x_3113);
return x_3120;
}
}
}
else
{
lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; 
lean_dec(x_2899);
lean_dec(x_2898);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3121 = lean_ctor_get(x_2896, 1);
lean_inc(x_3121);
if (lean_is_exclusive(x_2896)) {
 lean_ctor_release(x_2896, 0);
 lean_ctor_release(x_2896, 1);
 x_3122 = x_2896;
} else {
 lean_dec_ref(x_2896);
 x_3122 = lean_box(0);
}
x_3123 = lean_box(0);
if (lean_is_scalar(x_3122)) {
 x_3124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3124 = x_3122;
}
lean_ctor_set(x_3124, 0, x_3123);
lean_ctor_set(x_3124, 1, x_3121);
return x_3124;
}
}
else
{
lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; lean_object* x_3128; 
lean_dec(x_2898);
lean_dec(x_2897);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3125 = lean_ctor_get(x_2896, 1);
lean_inc(x_3125);
if (lean_is_exclusive(x_2896)) {
 lean_ctor_release(x_2896, 0);
 lean_ctor_release(x_2896, 1);
 x_3126 = x_2896;
} else {
 lean_dec_ref(x_2896);
 x_3126 = lean_box(0);
}
x_3127 = lean_box(0);
if (lean_is_scalar(x_3126)) {
 x_3128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3128 = x_3126;
}
lean_ctor_set(x_3128, 0, x_3127);
lean_ctor_set(x_3128, 1, x_3125);
return x_3128;
}
}
else
{
lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; lean_object* x_3132; 
lean_dec(x_2897);
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3129 = lean_ctor_get(x_2896, 1);
lean_inc(x_3129);
if (lean_is_exclusive(x_2896)) {
 lean_ctor_release(x_2896, 0);
 lean_ctor_release(x_2896, 1);
 x_3130 = x_2896;
} else {
 lean_dec_ref(x_2896);
 x_3130 = lean_box(0);
}
x_3131 = lean_box(0);
if (lean_is_scalar(x_3130)) {
 x_3132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3132 = x_3130;
}
lean_ctor_set(x_3132, 0, x_3131);
lean_ctor_set(x_3132, 1, x_3129);
return x_3132;
}
}
else
{
lean_object* x_3133; lean_object* x_3134; lean_object* x_3135; uint8_t x_3136; 
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3133 = lean_ctor_get(x_2896, 0);
lean_inc(x_3133);
x_3134 = lean_ctor_get(x_2896, 1);
lean_inc(x_3134);
if (lean_is_exclusive(x_2896)) {
 lean_ctor_release(x_2896, 0);
 lean_ctor_release(x_2896, 1);
 x_3135 = x_2896;
} else {
 lean_dec_ref(x_2896);
 x_3135 = lean_box(0);
}
x_3136 = l_Lean_Exception_isInterrupt(x_3133);
if (x_3136 == 0)
{
uint8_t x_3137; 
x_3137 = l_Lean_Exception_isRuntime(x_3133);
if (x_3137 == 0)
{
lean_object* x_3138; lean_object* x_3139; 
lean_dec(x_3133);
x_3138 = lean_box(0);
if (lean_is_scalar(x_3135)) {
 x_3139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3139 = x_3135;
 lean_ctor_set_tag(x_3139, 0);
}
lean_ctor_set(x_3139, 0, x_3138);
lean_ctor_set(x_3139, 1, x_3134);
return x_3139;
}
else
{
lean_object* x_3140; 
if (lean_is_scalar(x_3135)) {
 x_3140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3140 = x_3135;
}
lean_ctor_set(x_3140, 0, x_3133);
lean_ctor_set(x_3140, 1, x_3134);
return x_3140;
}
}
else
{
lean_object* x_3141; 
if (lean_is_scalar(x_3135)) {
 x_3141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3141 = x_3135;
}
lean_ctor_set(x_3141, 0, x_3133);
lean_ctor_set(x_3141, 1, x_3134);
return x_3141;
}
}
}
else
{
lean_object* x_3142; lean_object* x_3143; lean_object* x_3144; uint8_t x_3145; 
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3142 = lean_ctor_get(x_2893, 0);
lean_inc(x_3142);
x_3143 = lean_ctor_get(x_2893, 1);
lean_inc(x_3143);
if (lean_is_exclusive(x_2893)) {
 lean_ctor_release(x_2893, 0);
 lean_ctor_release(x_2893, 1);
 x_3144 = x_2893;
} else {
 lean_dec_ref(x_2893);
 x_3144 = lean_box(0);
}
x_3145 = l_Lean_Exception_isInterrupt(x_3142);
if (x_3145 == 0)
{
uint8_t x_3146; 
x_3146 = l_Lean_Exception_isRuntime(x_3142);
if (x_3146 == 0)
{
lean_object* x_3147; lean_object* x_3148; 
lean_dec(x_3142);
x_3147 = lean_box(0);
if (lean_is_scalar(x_3144)) {
 x_3148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3148 = x_3144;
 lean_ctor_set_tag(x_3148, 0);
}
lean_ctor_set(x_3148, 0, x_3147);
lean_ctor_set(x_3148, 1, x_3143);
return x_3148;
}
else
{
lean_object* x_3149; 
if (lean_is_scalar(x_3144)) {
 x_3149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3149 = x_3144;
}
lean_ctor_set(x_3149, 0, x_3142);
lean_ctor_set(x_3149, 1, x_3143);
return x_3149;
}
}
else
{
lean_object* x_3150; 
if (lean_is_scalar(x_3144)) {
 x_3150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3150 = x_3144;
}
lean_ctor_set(x_3150, 0, x_3142);
lean_ctor_set(x_3150, 1, x_3143);
return x_3150;
}
}
}
}
else
{
lean_object* x_3151; lean_object* x_3152; 
lean_dec(x_40);
lean_dec(x_33);
x_3151 = lean_ctor_get(x_2883, 1);
lean_inc(x_3151);
lean_dec(x_2883);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3152 = l_Lean_Meta_isMonad_x3f(x_2868, x_3, x_4, x_5, x_6, x_3151);
if (lean_obj_tag(x_3152) == 0)
{
lean_object* x_3153; 
x_3153 = lean_ctor_get(x_3152, 0);
lean_inc(x_3153);
if (lean_obj_tag(x_3153) == 0)
{
lean_object* x_3154; lean_object* x_3155; lean_object* x_3156; lean_object* x_3157; 
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3154 = lean_ctor_get(x_3152, 1);
lean_inc(x_3154);
if (lean_is_exclusive(x_3152)) {
 lean_ctor_release(x_3152, 0);
 lean_ctor_release(x_3152, 1);
 x_3155 = x_3152;
} else {
 lean_dec_ref(x_3152);
 x_3155 = lean_box(0);
}
x_3156 = lean_box(0);
if (lean_is_scalar(x_3155)) {
 x_3157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3157 = x_3155;
}
lean_ctor_set(x_3157, 0, x_3156);
lean_ctor_set(x_3157, 1, x_3154);
return x_3157;
}
else
{
lean_object* x_3158; lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; lean_object* x_3165; lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; lean_object* x_3170; lean_object* x_3171; lean_object* x_3172; lean_object* x_3173; lean_object* x_3174; 
x_3158 = lean_ctor_get(x_3152, 1);
lean_inc(x_3158);
lean_dec(x_3152);
x_3159 = lean_ctor_get(x_3153, 0);
lean_inc(x_3159);
if (lean_is_exclusive(x_3153)) {
 lean_ctor_release(x_3153, 0);
 x_3160 = x_3153;
} else {
 lean_dec_ref(x_3153);
 x_3160 = lean_box(0);
}
if (lean_is_scalar(x_3160)) {
 x_3161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3161 = x_3160;
}
lean_ctor_set(x_3161, 0, x_2880);
if (lean_is_scalar(x_2878)) {
 x_3162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3162 = x_2878;
}
lean_ctor_set(x_3162, 0, x_2881);
x_3163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3163, 0, x_2869);
x_3164 = lean_box(0);
x_3165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3165, 0, x_3159);
x_3166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3166, 0, x_1);
x_3167 = lean_box(0);
if (lean_is_scalar(x_2882)) {
 x_3168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3168 = x_2882;
 lean_ctor_set_tag(x_3168, 1);
}
lean_ctor_set(x_3168, 0, x_3166);
lean_ctor_set(x_3168, 1, x_3167);
if (lean_is_scalar(x_2870)) {
 x_3169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3169 = x_2870;
 lean_ctor_set_tag(x_3169, 1);
}
lean_ctor_set(x_3169, 0, x_3165);
lean_ctor_set(x_3169, 1, x_3168);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_3169);
lean_ctor_set(x_38, 0, x_3164);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_3163);
x_3170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3170, 0, x_3162);
lean_ctor_set(x_3170, 1, x_31);
x_3171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3171, 0, x_3161);
lean_ctor_set(x_3171, 1, x_3170);
x_3172 = lean_array_mk(x_3171);
x_3173 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3174 = l_Lean_Meta_mkAppOptM(x_3173, x_3172, x_3, x_4, x_5, x_6, x_3158);
if (lean_obj_tag(x_3174) == 0)
{
lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; 
x_3175 = lean_ctor_get(x_3174, 0);
lean_inc(x_3175);
x_3176 = lean_ctor_get(x_3174, 1);
lean_inc(x_3176);
lean_dec(x_3174);
x_3177 = l_Lean_Meta_expandCoe(x_3175, x_3, x_4, x_5, x_6, x_3176);
if (lean_obj_tag(x_3177) == 0)
{
lean_object* x_3178; lean_object* x_3179; lean_object* x_3180; lean_object* x_3181; 
x_3178 = lean_ctor_get(x_3177, 0);
lean_inc(x_3178);
x_3179 = lean_ctor_get(x_3177, 1);
lean_inc(x_3179);
lean_dec(x_3177);
x_3180 = lean_box(0);
x_3181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3181, 0, x_3178);
lean_ctor_set(x_3181, 1, x_3180);
x_17 = x_3181;
x_18 = x_3179;
goto block_30;
}
else
{
lean_object* x_3182; lean_object* x_3183; lean_object* x_3184; uint8_t x_3185; 
x_3182 = lean_ctor_get(x_3177, 0);
lean_inc(x_3182);
x_3183 = lean_ctor_get(x_3177, 1);
lean_inc(x_3183);
if (lean_is_exclusive(x_3177)) {
 lean_ctor_release(x_3177, 0);
 lean_ctor_release(x_3177, 1);
 x_3184 = x_3177;
} else {
 lean_dec_ref(x_3177);
 x_3184 = lean_box(0);
}
x_3185 = l_Lean_Exception_isInterrupt(x_3182);
if (x_3185 == 0)
{
uint8_t x_3186; 
x_3186 = l_Lean_Exception_isRuntime(x_3182);
if (x_3186 == 0)
{
lean_object* x_3187; 
lean_dec(x_3184);
lean_dec(x_3182);
x_3187 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_3187;
x_18 = x_3183;
goto block_30;
}
else
{
lean_object* x_3188; 
if (lean_is_scalar(x_3184)) {
 x_3188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3188 = x_3184;
}
lean_ctor_set(x_3188, 0, x_3182);
lean_ctor_set(x_3188, 1, x_3183);
return x_3188;
}
}
else
{
lean_object* x_3189; 
if (lean_is_scalar(x_3184)) {
 x_3189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3189 = x_3184;
}
lean_ctor_set(x_3189, 0, x_3182);
lean_ctor_set(x_3189, 1, x_3183);
return x_3189;
}
}
}
else
{
lean_object* x_3190; lean_object* x_3191; lean_object* x_3192; uint8_t x_3193; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3190 = lean_ctor_get(x_3174, 0);
lean_inc(x_3190);
x_3191 = lean_ctor_get(x_3174, 1);
lean_inc(x_3191);
if (lean_is_exclusive(x_3174)) {
 lean_ctor_release(x_3174, 0);
 lean_ctor_release(x_3174, 1);
 x_3192 = x_3174;
} else {
 lean_dec_ref(x_3174);
 x_3192 = lean_box(0);
}
x_3193 = l_Lean_Exception_isInterrupt(x_3190);
if (x_3193 == 0)
{
uint8_t x_3194; 
x_3194 = l_Lean_Exception_isRuntime(x_3190);
if (x_3194 == 0)
{
lean_object* x_3195; 
lean_dec(x_3192);
lean_dec(x_3190);
x_3195 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_3195;
x_18 = x_3191;
goto block_30;
}
else
{
lean_object* x_3196; 
if (lean_is_scalar(x_3192)) {
 x_3196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3196 = x_3192;
}
lean_ctor_set(x_3196, 0, x_3190);
lean_ctor_set(x_3196, 1, x_3191);
return x_3196;
}
}
else
{
lean_object* x_3197; 
if (lean_is_scalar(x_3192)) {
 x_3197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3197 = x_3192;
}
lean_ctor_set(x_3197, 0, x_3190);
lean_ctor_set(x_3197, 1, x_3191);
return x_3197;
}
}
}
}
else
{
lean_object* x_3198; lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; 
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_free_object(x_38);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3198 = lean_ctor_get(x_3152, 0);
lean_inc(x_3198);
x_3199 = lean_ctor_get(x_3152, 1);
lean_inc(x_3199);
if (lean_is_exclusive(x_3152)) {
 lean_ctor_release(x_3152, 0);
 lean_ctor_release(x_3152, 1);
 x_3200 = x_3152;
} else {
 lean_dec_ref(x_3152);
 x_3200 = lean_box(0);
}
if (lean_is_scalar(x_3200)) {
 x_3201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3201 = x_3200;
}
lean_ctor_set(x_3201, 0, x_3198);
lean_ctor_set(x_3201, 1, x_3199);
return x_3201;
}
}
}
else
{
lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; lean_object* x_3205; 
lean_dec(x_2882);
lean_dec(x_2881);
lean_dec(x_2880);
lean_dec(x_2878);
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3202 = lean_ctor_get(x_2883, 0);
lean_inc(x_3202);
x_3203 = lean_ctor_get(x_2883, 1);
lean_inc(x_3203);
if (lean_is_exclusive(x_2883)) {
 lean_ctor_release(x_2883, 0);
 lean_ctor_release(x_2883, 1);
 x_3204 = x_2883;
} else {
 lean_dec_ref(x_2883);
 x_3204 = lean_box(0);
}
if (lean_is_scalar(x_3204)) {
 x_3205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3205 = x_3204;
}
lean_ctor_set(x_3205, 0, x_3202);
lean_ctor_set(x_3205, 1, x_3203);
return x_3205;
}
}
}
else
{
lean_object* x_3206; lean_object* x_3207; lean_object* x_3208; lean_object* x_3209; 
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2868);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3206 = lean_ctor_get(x_2871, 0);
lean_inc(x_3206);
x_3207 = lean_ctor_get(x_2871, 1);
lean_inc(x_3207);
if (lean_is_exclusive(x_2871)) {
 lean_ctor_release(x_2871, 0);
 lean_ctor_release(x_2871, 1);
 x_3208 = x_2871;
} else {
 lean_dec_ref(x_2871);
 x_3208 = lean_box(0);
}
if (lean_is_scalar(x_3208)) {
 x_3209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3209 = x_3208;
}
lean_ctor_set(x_3209, 0, x_3206);
lean_ctor_set(x_3209, 1, x_3207);
return x_3209;
}
}
}
}
else
{
uint8_t x_3210; 
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3210 = !lean_is_exclusive(x_42);
if (x_3210 == 0)
{
return x_42;
}
else
{
lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; 
x_3211 = lean_ctor_get(x_42, 0);
x_3212 = lean_ctor_get(x_42, 1);
lean_inc(x_3212);
lean_inc(x_3211);
lean_dec(x_42);
x_3213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3213, 0, x_3211);
lean_ctor_set(x_3213, 1, x_3212);
return x_3213;
}
}
}
else
{
lean_object* x_3214; lean_object* x_3215; lean_object* x_3216; 
x_3214 = lean_ctor_get(x_38, 0);
x_3215 = lean_ctor_get(x_38, 1);
lean_inc(x_3215);
lean_inc(x_3214);
lean_dec(x_38);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_3216 = l_Lean_Meta_isTypeApp_x3f(x_33, x_3, x_4, x_5, x_6, x_3215);
if (lean_obj_tag(x_3216) == 0)
{
lean_object* x_3217; 
x_3217 = lean_ctor_get(x_3216, 0);
lean_inc(x_3217);
if (lean_obj_tag(x_3217) == 0)
{
lean_object* x_3218; lean_object* x_3219; lean_object* x_3220; lean_object* x_3221; 
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3218 = lean_ctor_get(x_3216, 1);
lean_inc(x_3218);
if (lean_is_exclusive(x_3216)) {
 lean_ctor_release(x_3216, 0);
 lean_ctor_release(x_3216, 1);
 x_3219 = x_3216;
} else {
 lean_dec_ref(x_3216);
 x_3219 = lean_box(0);
}
x_3220 = lean_box(0);
if (lean_is_scalar(x_3219)) {
 x_3221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3221 = x_3219;
}
lean_ctor_set(x_3221, 0, x_3220);
lean_ctor_set(x_3221, 1, x_3218);
return x_3221;
}
else
{
lean_object* x_3222; lean_object* x_3223; lean_object* x_3224; lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; lean_object* x_3228; 
x_3222 = lean_ctor_get(x_3217, 0);
lean_inc(x_3222);
if (lean_is_exclusive(x_3217)) {
 lean_ctor_release(x_3217, 0);
 x_3223 = x_3217;
} else {
 lean_dec_ref(x_3217);
 x_3223 = lean_box(0);
}
x_3224 = lean_ctor_get(x_3216, 1);
lean_inc(x_3224);
lean_dec(x_3216);
x_3225 = lean_ctor_get(x_3222, 0);
lean_inc(x_3225);
x_3226 = lean_ctor_get(x_3222, 1);
lean_inc(x_3226);
if (lean_is_exclusive(x_3222)) {
 lean_ctor_release(x_3222, 0);
 lean_ctor_release(x_3222, 1);
 x_3227 = x_3222;
} else {
 lean_dec_ref(x_3222);
 x_3227 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3214);
x_3228 = l_Lean_Meta_isTypeApp_x3f(x_3214, x_3, x_4, x_5, x_6, x_3224);
if (lean_obj_tag(x_3228) == 0)
{
lean_object* x_3229; 
x_3229 = lean_ctor_get(x_3228, 0);
lean_inc(x_3229);
if (lean_obj_tag(x_3229) == 0)
{
lean_object* x_3230; lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; 
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3223);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3230 = lean_ctor_get(x_3228, 1);
lean_inc(x_3230);
if (lean_is_exclusive(x_3228)) {
 lean_ctor_release(x_3228, 0);
 lean_ctor_release(x_3228, 1);
 x_3231 = x_3228;
} else {
 lean_dec_ref(x_3228);
 x_3231 = lean_box(0);
}
x_3232 = lean_box(0);
if (lean_is_scalar(x_3231)) {
 x_3233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3233 = x_3231;
}
lean_ctor_set(x_3233, 0, x_3232);
lean_ctor_set(x_3233, 1, x_3230);
return x_3233;
}
else
{
lean_object* x_3234; lean_object* x_3235; lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; 
x_3234 = lean_ctor_get(x_3229, 0);
lean_inc(x_3234);
if (lean_is_exclusive(x_3229)) {
 lean_ctor_release(x_3229, 0);
 x_3235 = x_3229;
} else {
 lean_dec_ref(x_3229);
 x_3235 = lean_box(0);
}
x_3236 = lean_ctor_get(x_3228, 1);
lean_inc(x_3236);
lean_dec(x_3228);
x_3237 = lean_ctor_get(x_3234, 0);
lean_inc(x_3237);
x_3238 = lean_ctor_get(x_3234, 1);
lean_inc(x_3238);
if (lean_is_exclusive(x_3234)) {
 lean_ctor_release(x_3234, 0);
 lean_ctor_release(x_3234, 1);
 x_3239 = x_3234;
} else {
 lean_dec_ref(x_3234);
 x_3239 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3225);
lean_inc(x_3237);
x_3240 = l_Lean_Meta_isExprDefEq(x_3237, x_3225, x_3, x_4, x_5, x_6, x_3236);
if (lean_obj_tag(x_3240) == 0)
{
lean_object* x_3241; uint8_t x_3242; 
x_3241 = lean_ctor_get(x_3240, 0);
lean_inc(x_3241);
x_3242 = lean_unbox(x_3241);
lean_dec(x_3241);
if (x_3242 == 0)
{
lean_object* x_3243; lean_object* x_3244; lean_object* x_3245; lean_object* x_3246; uint8_t x_3247; 
lean_dec(x_3223);
x_3243 = lean_ctor_get(x_3240, 1);
lean_inc(x_3243);
if (lean_is_exclusive(x_3240)) {
 lean_ctor_release(x_3240, 0);
 lean_ctor_release(x_3240, 1);
 x_3244 = x_3240;
} else {
 lean_dec_ref(x_3240);
 x_3244 = lean_box(0);
}
x_3245 = lean_ctor_get(x_5, 2);
lean_inc(x_3245);
x_3246 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_3247 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_3245, x_3246);
lean_dec(x_3245);
if (x_3247 == 0)
{
lean_object* x_3248; lean_object* x_3249; 
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3248 = lean_box(0);
if (lean_is_scalar(x_3244)) {
 x_3249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3249 = x_3244;
}
lean_ctor_set(x_3249, 0, x_3248);
lean_ctor_set(x_3249, 1, x_3243);
return x_3249;
}
else
{
lean_object* x_3250; 
lean_dec(x_3244);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3237);
x_3250 = lean_infer_type(x_3237, x_3, x_4, x_5, x_6, x_3243);
if (lean_obj_tag(x_3250) == 0)
{
lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; 
x_3251 = lean_ctor_get(x_3250, 0);
lean_inc(x_3251);
x_3252 = lean_ctor_get(x_3250, 1);
lean_inc(x_3252);
lean_dec(x_3250);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3253 = lean_whnf(x_3251, x_3, x_4, x_5, x_6, x_3252);
if (lean_obj_tag(x_3253) == 0)
{
lean_object* x_3254; 
x_3254 = lean_ctor_get(x_3253, 0);
lean_inc(x_3254);
if (lean_obj_tag(x_3254) == 7)
{
lean_object* x_3255; 
x_3255 = lean_ctor_get(x_3254, 1);
lean_inc(x_3255);
if (lean_obj_tag(x_3255) == 3)
{
lean_object* x_3256; 
x_3256 = lean_ctor_get(x_3254, 2);
lean_inc(x_3256);
lean_dec(x_3254);
if (lean_obj_tag(x_3256) == 3)
{
lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; lean_object* x_3260; 
x_3257 = lean_ctor_get(x_3253, 1);
lean_inc(x_3257);
lean_dec(x_3253);
x_3258 = lean_ctor_get(x_3255, 0);
lean_inc(x_3258);
lean_dec(x_3255);
x_3259 = lean_ctor_get(x_3256, 0);
lean_inc(x_3259);
lean_dec(x_3256);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3225);
x_3260 = lean_infer_type(x_3225, x_3, x_4, x_5, x_6, x_3257);
if (lean_obj_tag(x_3260) == 0)
{
lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; 
x_3261 = lean_ctor_get(x_3260, 0);
lean_inc(x_3261);
x_3262 = lean_ctor_get(x_3260, 1);
lean_inc(x_3262);
lean_dec(x_3260);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3263 = lean_whnf(x_3261, x_3, x_4, x_5, x_6, x_3262);
if (lean_obj_tag(x_3263) == 0)
{
lean_object* x_3264; 
x_3264 = lean_ctor_get(x_3263, 0);
lean_inc(x_3264);
if (lean_obj_tag(x_3264) == 7)
{
lean_object* x_3265; 
x_3265 = lean_ctor_get(x_3264, 1);
lean_inc(x_3265);
if (lean_obj_tag(x_3265) == 3)
{
lean_object* x_3266; 
x_3266 = lean_ctor_get(x_3264, 2);
lean_inc(x_3266);
lean_dec(x_3264);
if (lean_obj_tag(x_3266) == 3)
{
lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; 
x_3267 = lean_ctor_get(x_3263, 1);
lean_inc(x_3267);
lean_dec(x_3263);
x_3268 = lean_ctor_get(x_3265, 0);
lean_inc(x_3268);
lean_dec(x_3265);
x_3269 = lean_ctor_get(x_3266, 0);
lean_inc(x_3269);
lean_dec(x_3266);
x_3270 = l_Lean_Meta_decLevel(x_3258, x_3, x_4, x_5, x_6, x_3267);
if (lean_obj_tag(x_3270) == 0)
{
lean_object* x_3271; lean_object* x_3272; lean_object* x_3273; lean_object* x_3274; 
x_3271 = lean_ctor_get(x_3270, 0);
lean_inc(x_3271);
x_3272 = lean_ctor_get(x_3270, 1);
lean_inc(x_3272);
if (lean_is_exclusive(x_3270)) {
 lean_ctor_release(x_3270, 0);
 lean_ctor_release(x_3270, 1);
 x_3273 = x_3270;
} else {
 lean_dec_ref(x_3270);
 x_3273 = lean_box(0);
}
x_3274 = l_Lean_Meta_decLevel(x_3268, x_3, x_4, x_5, x_6, x_3272);
if (lean_obj_tag(x_3274) == 0)
{
lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; uint8_t x_3278; lean_object* x_3279; 
x_3275 = lean_ctor_get(x_3274, 0);
lean_inc(x_3275);
x_3276 = lean_ctor_get(x_3274, 1);
lean_inc(x_3276);
if (lean_is_exclusive(x_3274)) {
 lean_ctor_release(x_3274, 0);
 lean_ctor_release(x_3274, 1);
 x_3277 = x_3274;
} else {
 lean_dec_ref(x_3274);
 x_3277 = lean_box(0);
}
x_3278 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3271);
x_3279 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_3271, x_3275, x_3278, x_3, x_4, x_5, x_6, x_3276);
if (lean_obj_tag(x_3279) == 0)
{
lean_object* x_3280; uint8_t x_3281; 
x_3280 = lean_ctor_get(x_3279, 0);
lean_inc(x_3280);
x_3281 = lean_unbox(x_3280);
lean_dec(x_3280);
if (x_3281 == 0)
{
lean_object* x_3282; lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; 
lean_dec(x_3277);
lean_dec(x_3273);
lean_dec(x_3271);
lean_dec(x_3269);
lean_dec(x_3259);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3282 = lean_ctor_get(x_3279, 1);
lean_inc(x_3282);
if (lean_is_exclusive(x_3279)) {
 lean_ctor_release(x_3279, 0);
 lean_ctor_release(x_3279, 1);
 x_3283 = x_3279;
} else {
 lean_dec_ref(x_3279);
 x_3283 = lean_box(0);
}
x_3284 = lean_box(0);
if (lean_is_scalar(x_3283)) {
 x_3285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3285 = x_3283;
}
lean_ctor_set(x_3285, 0, x_3284);
lean_ctor_set(x_3285, 1, x_3282);
return x_3285;
}
else
{
lean_object* x_3286; lean_object* x_3287; 
x_3286 = lean_ctor_get(x_3279, 1);
lean_inc(x_3286);
lean_dec(x_3279);
x_3287 = l_Lean_Meta_decLevel(x_3259, x_3, x_4, x_5, x_6, x_3286);
if (lean_obj_tag(x_3287) == 0)
{
lean_object* x_3288; lean_object* x_3289; lean_object* x_3290; lean_object* x_3291; 
x_3288 = lean_ctor_get(x_3287, 0);
lean_inc(x_3288);
x_3289 = lean_ctor_get(x_3287, 1);
lean_inc(x_3289);
if (lean_is_exclusive(x_3287)) {
 lean_ctor_release(x_3287, 0);
 lean_ctor_release(x_3287, 1);
 x_3290 = x_3287;
} else {
 lean_dec_ref(x_3287);
 x_3290 = lean_box(0);
}
x_3291 = l_Lean_Meta_decLevel(x_3269, x_3, x_4, x_5, x_6, x_3289);
if (lean_obj_tag(x_3291) == 0)
{
lean_object* x_3292; lean_object* x_3293; lean_object* x_3294; lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; lean_object* x_3299; lean_object* x_3300; lean_object* x_3301; lean_object* x_3302; lean_object* x_3303; lean_object* x_3304; lean_object* x_3305; lean_object* x_3306; 
x_3292 = lean_ctor_get(x_3291, 0);
lean_inc(x_3292);
x_3293 = lean_ctor_get(x_3291, 1);
lean_inc(x_3293);
if (lean_is_exclusive(x_3291)) {
 lean_ctor_release(x_3291, 0);
 lean_ctor_release(x_3291, 1);
 x_3294 = x_3291;
} else {
 lean_dec_ref(x_3291);
 x_3294 = lean_box(0);
}
x_3295 = lean_box(0);
if (lean_is_scalar(x_3294)) {
 x_3296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3296 = x_3294;
 lean_ctor_set_tag(x_3296, 1);
}
lean_ctor_set(x_3296, 0, x_3292);
lean_ctor_set(x_3296, 1, x_3295);
if (lean_is_scalar(x_3290)) {
 x_3297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3297 = x_3290;
 lean_ctor_set_tag(x_3297, 1);
}
lean_ctor_set(x_3297, 0, x_3288);
lean_ctor_set(x_3297, 1, x_3296);
if (lean_is_scalar(x_3277)) {
 x_3298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3298 = x_3277;
 lean_ctor_set_tag(x_3298, 1);
}
lean_ctor_set(x_3298, 0, x_3271);
lean_ctor_set(x_3298, 1, x_3297);
x_3299 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_3300 = l_Lean_Expr_const___override(x_3299, x_3298);
lean_inc(x_3225);
if (lean_is_scalar(x_3273)) {
 x_3301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3301 = x_3273;
 lean_ctor_set_tag(x_3301, 1);
}
lean_ctor_set(x_3301, 0, x_3225);
lean_ctor_set(x_3301, 1, x_3295);
lean_inc(x_3237);
if (lean_is_scalar(x_3239)) {
 x_3302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3302 = x_3239;
 lean_ctor_set_tag(x_3302, 1);
}
lean_ctor_set(x_3302, 0, x_3237);
lean_ctor_set(x_3302, 1, x_3301);
x_3303 = lean_array_mk(x_3302);
x_3304 = l_Lean_mkAppN(x_3300, x_3303);
lean_dec(x_3303);
x_3305 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3306 = l_Lean_Meta_trySynthInstance(x_3304, x_3305, x_3, x_4, x_5, x_6, x_3293);
if (lean_obj_tag(x_3306) == 0)
{
lean_object* x_3307; 
x_3307 = lean_ctor_get(x_3306, 0);
lean_inc(x_3307);
if (lean_obj_tag(x_3307) == 1)
{
lean_object* x_3308; lean_object* x_3309; lean_object* x_3310; 
x_3308 = lean_ctor_get(x_3306, 1);
lean_inc(x_3308);
lean_dec(x_3306);
x_3309 = lean_ctor_get(x_3307, 0);
lean_inc(x_3309);
lean_dec(x_3307);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3238);
x_3310 = l_Lean_Meta_getDecLevel(x_3238, x_3, x_4, x_5, x_6, x_3308);
if (lean_obj_tag(x_3310) == 0)
{
lean_object* x_3311; lean_object* x_3312; lean_object* x_3313; lean_object* x_3314; 
x_3311 = lean_ctor_get(x_3310, 0);
lean_inc(x_3311);
x_3312 = lean_ctor_get(x_3310, 1);
lean_inc(x_3312);
if (lean_is_exclusive(x_3310)) {
 lean_ctor_release(x_3310, 0);
 lean_ctor_release(x_3310, 1);
 x_3313 = x_3310;
} else {
 lean_dec_ref(x_3310);
 x_3313 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3314 = l_Lean_Meta_getDecLevel(x_3214, x_3, x_4, x_5, x_6, x_3312);
if (lean_obj_tag(x_3314) == 0)
{
lean_object* x_3315; lean_object* x_3316; lean_object* x_3317; lean_object* x_3318; 
x_3315 = lean_ctor_get(x_3314, 0);
lean_inc(x_3315);
x_3316 = lean_ctor_get(x_3314, 1);
lean_inc(x_3316);
if (lean_is_exclusive(x_3314)) {
 lean_ctor_release(x_3314, 0);
 lean_ctor_release(x_3314, 1);
 x_3317 = x_3314;
} else {
 lean_dec_ref(x_3314);
 x_3317 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_3318 = l_Lean_Meta_getDecLevel(x_33, x_3, x_4, x_5, x_6, x_3316);
if (lean_obj_tag(x_3318) == 0)
{
lean_object* x_3319; lean_object* x_3320; lean_object* x_3321; lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; lean_object* x_3329; lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; 
x_3319 = lean_ctor_get(x_3318, 0);
lean_inc(x_3319);
x_3320 = lean_ctor_get(x_3318, 1);
lean_inc(x_3320);
if (lean_is_exclusive(x_3318)) {
 lean_ctor_release(x_3318, 0);
 lean_ctor_release(x_3318, 1);
 x_3321 = x_3318;
} else {
 lean_dec_ref(x_3318);
 x_3321 = lean_box(0);
}
if (lean_is_scalar(x_3321)) {
 x_3322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3322 = x_3321;
 lean_ctor_set_tag(x_3322, 1);
}
lean_ctor_set(x_3322, 0, x_3319);
lean_ctor_set(x_3322, 1, x_3295);
if (lean_is_scalar(x_3317)) {
 x_3323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3323 = x_3317;
 lean_ctor_set_tag(x_3323, 1);
}
lean_ctor_set(x_3323, 0, x_3315);
lean_ctor_set(x_3323, 1, x_3322);
if (lean_is_scalar(x_3313)) {
 x_3324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3324 = x_3313;
 lean_ctor_set_tag(x_3324, 1);
}
lean_ctor_set(x_3324, 0, x_3311);
lean_ctor_set(x_3324, 1, x_3323);
x_3325 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_3324);
x_3326 = l_Lean_Expr_const___override(x_3325, x_3324);
if (lean_is_scalar(x_3227)) {
 x_3327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3327 = x_3227;
 lean_ctor_set_tag(x_3327, 1);
}
lean_ctor_set(x_3327, 0, x_1);
lean_ctor_set(x_3327, 1, x_3295);
lean_inc(x_3327);
lean_inc(x_3238);
x_3328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3328, 0, x_3238);
lean_ctor_set(x_3328, 1, x_3327);
lean_inc(x_3309);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_3328);
lean_ctor_set(x_31, 0, x_3309);
lean_inc(x_3225);
x_3329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3329, 0, x_3225);
lean_ctor_set(x_3329, 1, x_31);
lean_inc(x_3237);
x_3330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3330, 0, x_3237);
lean_ctor_set(x_3330, 1, x_3329);
x_3331 = lean_array_mk(x_3330);
x_3332 = l_Lean_mkAppN(x_3326, x_3331);
lean_dec(x_3331);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3332);
x_3333 = lean_infer_type(x_3332, x_3, x_4, x_5, x_6, x_3320);
if (lean_obj_tag(x_3333) == 0)
{
lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; 
x_3334 = lean_ctor_get(x_3333, 0);
lean_inc(x_3334);
x_3335 = lean_ctor_get(x_3333, 1);
lean_inc(x_3335);
if (lean_is_exclusive(x_3333)) {
 lean_ctor_release(x_3333, 0);
 lean_ctor_release(x_3333, 1);
 x_3336 = x_3333;
} else {
 lean_dec_ref(x_3333);
 x_3336 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_3337 = l_Lean_Meta_isExprDefEq(x_33, x_3334, x_3, x_4, x_5, x_6, x_3335);
if (lean_obj_tag(x_3337) == 0)
{
lean_object* x_3338; uint8_t x_3339; 
x_3338 = lean_ctor_get(x_3337, 0);
lean_inc(x_3338);
x_3339 = lean_unbox(x_3338);
lean_dec(x_3338);
if (x_3339 == 0)
{
lean_object* x_3340; lean_object* x_3341; 
lean_dec(x_3332);
lean_dec(x_3235);
x_3340 = lean_ctor_get(x_3337, 1);
lean_inc(x_3340);
lean_dec(x_3337);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3225);
x_3341 = l_Lean_Meta_isMonad_x3f(x_3225, x_3, x_4, x_5, x_6, x_3340);
if (lean_obj_tag(x_3341) == 0)
{
lean_object* x_3342; 
x_3342 = lean_ctor_get(x_3341, 0);
lean_inc(x_3342);
if (lean_obj_tag(x_3342) == 0)
{
lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; 
lean_dec(x_3336);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3343 = lean_ctor_get(x_3341, 1);
lean_inc(x_3343);
if (lean_is_exclusive(x_3341)) {
 lean_ctor_release(x_3341, 0);
 lean_ctor_release(x_3341, 1);
 x_3344 = x_3341;
} else {
 lean_dec_ref(x_3341);
 x_3344 = lean_box(0);
}
if (lean_is_scalar(x_3344)) {
 x_3345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3345 = x_3344;
}
lean_ctor_set(x_3345, 0, x_3305);
lean_ctor_set(x_3345, 1, x_3343);
return x_3345;
}
else
{
lean_object* x_3346; lean_object* x_3347; lean_object* x_3348; 
x_3346 = lean_ctor_get(x_3341, 1);
lean_inc(x_3346);
lean_dec(x_3341);
x_3347 = lean_ctor_get(x_3342, 0);
lean_inc(x_3347);
lean_dec(x_3342);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3238);
x_3348 = l_Lean_Meta_getLevel(x_3238, x_3, x_4, x_5, x_6, x_3346);
if (lean_obj_tag(x_3348) == 0)
{
lean_object* x_3349; lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; 
x_3349 = lean_ctor_get(x_3348, 0);
lean_inc(x_3349);
x_3350 = lean_ctor_get(x_3348, 1);
lean_inc(x_3350);
if (lean_is_exclusive(x_3348)) {
 lean_ctor_release(x_3348, 0);
 lean_ctor_release(x_3348, 1);
 x_3351 = x_3348;
} else {
 lean_dec_ref(x_3348);
 x_3351 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3226);
x_3352 = l_Lean_Meta_getLevel(x_3226, x_3, x_4, x_5, x_6, x_3350);
if (lean_obj_tag(x_3352) == 0)
{
lean_object* x_3353; lean_object* x_3354; lean_object* x_3355; lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; lean_object* x_3359; lean_object* x_3360; lean_object* x_3361; lean_object* x_3362; lean_object* x_3363; lean_object* x_3364; lean_object* x_3365; lean_object* x_3366; uint8_t x_3367; lean_object* x_3368; lean_object* x_3369; 
x_3353 = lean_ctor_get(x_3352, 0);
lean_inc(x_3353);
x_3354 = lean_ctor_get(x_3352, 1);
lean_inc(x_3354);
if (lean_is_exclusive(x_3352)) {
 lean_ctor_release(x_3352, 0);
 lean_ctor_release(x_3352, 1);
 x_3355 = x_3352;
} else {
 lean_dec_ref(x_3352);
 x_3355 = lean_box(0);
}
if (lean_is_scalar(x_3355)) {
 x_3356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3356 = x_3355;
 lean_ctor_set_tag(x_3356, 1);
}
lean_ctor_set(x_3356, 0, x_3353);
lean_ctor_set(x_3356, 1, x_3295);
if (lean_is_scalar(x_3351)) {
 x_3357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3357 = x_3351;
 lean_ctor_set_tag(x_3357, 1);
}
lean_ctor_set(x_3357, 0, x_3349);
lean_ctor_set(x_3357, 1, x_3356);
x_3358 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_3359 = l_Lean_Expr_const___override(x_3358, x_3357);
lean_inc(x_3226);
if (lean_is_scalar(x_3336)) {
 x_3360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3360 = x_3336;
 lean_ctor_set_tag(x_3360, 1);
}
lean_ctor_set(x_3360, 0, x_3226);
lean_ctor_set(x_3360, 1, x_3295);
x_3361 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_3362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3362, 0, x_3361);
lean_ctor_set(x_3362, 1, x_3360);
lean_inc(x_3238);
x_3363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3363, 0, x_3238);
lean_ctor_set(x_3363, 1, x_3362);
x_3364 = lean_array_mk(x_3363);
x_3365 = l_Lean_mkAppN(x_3359, x_3364);
lean_dec(x_3364);
x_3366 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_3367 = 0;
lean_inc(x_3238);
x_3368 = l_Lean_Expr_forallE___override(x_3366, x_3238, x_3365, x_3367);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3369 = l_Lean_Meta_trySynthInstance(x_3368, x_3305, x_3, x_4, x_5, x_6, x_3354);
if (lean_obj_tag(x_3369) == 0)
{
lean_object* x_3370; 
x_3370 = lean_ctor_get(x_3369, 0);
lean_inc(x_3370);
if (lean_obj_tag(x_3370) == 1)
{
lean_object* x_3371; lean_object* x_3372; lean_object* x_3373; lean_object* x_3374; lean_object* x_3375; lean_object* x_3376; lean_object* x_3377; lean_object* x_3378; lean_object* x_3379; lean_object* x_3380; lean_object* x_3381; lean_object* x_3382; lean_object* x_3383; lean_object* x_3384; 
x_3371 = lean_ctor_get(x_3369, 1);
lean_inc(x_3371);
lean_dec(x_3369);
x_3372 = lean_ctor_get(x_3370, 0);
lean_inc(x_3372);
lean_dec(x_3370);
x_3373 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_3374 = l_Lean_Expr_const___override(x_3373, x_3324);
x_3375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3375, 0, x_3347);
lean_ctor_set(x_3375, 1, x_3327);
x_3376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3376, 0, x_3372);
lean_ctor_set(x_3376, 1, x_3375);
x_3377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3377, 0, x_3309);
lean_ctor_set(x_3377, 1, x_3376);
x_3378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3378, 0, x_3226);
lean_ctor_set(x_3378, 1, x_3377);
x_3379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3379, 0, x_3238);
lean_ctor_set(x_3379, 1, x_3378);
x_3380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3380, 0, x_3225);
lean_ctor_set(x_3380, 1, x_3379);
x_3381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3381, 0, x_3237);
lean_ctor_set(x_3381, 1, x_3380);
x_3382 = lean_array_mk(x_3381);
x_3383 = l_Lean_mkAppN(x_3374, x_3382);
lean_dec(x_3382);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3384 = l_Lean_Meta_expandCoe(x_3383, x_3, x_4, x_5, x_6, x_3371);
if (lean_obj_tag(x_3384) == 0)
{
lean_object* x_3385; lean_object* x_3386; lean_object* x_3387; 
x_3385 = lean_ctor_get(x_3384, 0);
lean_inc(x_3385);
x_3386 = lean_ctor_get(x_3384, 1);
lean_inc(x_3386);
lean_dec(x_3384);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3385);
x_3387 = lean_infer_type(x_3385, x_3, x_4, x_5, x_6, x_3386);
if (lean_obj_tag(x_3387) == 0)
{
lean_object* x_3388; lean_object* x_3389; lean_object* x_3390; 
x_3388 = lean_ctor_get(x_3387, 0);
lean_inc(x_3388);
x_3389 = lean_ctor_get(x_3387, 1);
lean_inc(x_3389);
lean_dec(x_3387);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3390 = l_Lean_Meta_isExprDefEq(x_33, x_3388, x_3, x_4, x_5, x_6, x_3389);
if (lean_obj_tag(x_3390) == 0)
{
lean_object* x_3391; uint8_t x_3392; 
x_3391 = lean_ctor_get(x_3390, 0);
lean_inc(x_3391);
x_3392 = lean_unbox(x_3391);
lean_dec(x_3391);
if (x_3392 == 0)
{
lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; 
lean_dec(x_3385);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3393 = lean_ctor_get(x_3390, 1);
lean_inc(x_3393);
if (lean_is_exclusive(x_3390)) {
 lean_ctor_release(x_3390, 0);
 lean_ctor_release(x_3390, 1);
 x_3394 = x_3390;
} else {
 lean_dec_ref(x_3390);
 x_3394 = lean_box(0);
}
if (lean_is_scalar(x_3394)) {
 x_3395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3395 = x_3394;
}
lean_ctor_set(x_3395, 0, x_3305);
lean_ctor_set(x_3395, 1, x_3393);
return x_3395;
}
else
{
lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3401; lean_object* x_3402; 
x_3396 = lean_ctor_get(x_3390, 1);
lean_inc(x_3396);
lean_dec(x_3390);
x_3397 = lean_box(0);
x_3398 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_3385, x_3397, x_3, x_4, x_5, x_6, x_3396);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3399 = lean_ctor_get(x_3398, 0);
lean_inc(x_3399);
x_3400 = lean_ctor_get(x_3398, 1);
lean_inc(x_3400);
if (lean_is_exclusive(x_3398)) {
 lean_ctor_release(x_3398, 0);
 lean_ctor_release(x_3398, 1);
 x_3401 = x_3398;
} else {
 lean_dec_ref(x_3398);
 x_3401 = lean_box(0);
}
if (lean_is_scalar(x_3401)) {
 x_3402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3402 = x_3401;
}
lean_ctor_set(x_3402, 0, x_3399);
lean_ctor_set(x_3402, 1, x_3400);
return x_3402;
}
}
else
{
lean_object* x_3403; lean_object* x_3404; 
lean_dec(x_3385);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3403 = lean_ctor_get(x_3390, 0);
lean_inc(x_3403);
x_3404 = lean_ctor_get(x_3390, 1);
lean_inc(x_3404);
lean_dec(x_3390);
x_8 = x_3403;
x_9 = x_3404;
goto block_16;
}
}
else
{
lean_object* x_3405; lean_object* x_3406; 
lean_dec(x_3385);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3405 = lean_ctor_get(x_3387, 0);
lean_inc(x_3405);
x_3406 = lean_ctor_get(x_3387, 1);
lean_inc(x_3406);
lean_dec(x_3387);
x_8 = x_3405;
x_9 = x_3406;
goto block_16;
}
}
else
{
lean_object* x_3407; lean_object* x_3408; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3407 = lean_ctor_get(x_3384, 0);
lean_inc(x_3407);
x_3408 = lean_ctor_get(x_3384, 1);
lean_inc(x_3408);
lean_dec(x_3384);
x_8 = x_3407;
x_9 = x_3408;
goto block_16;
}
}
else
{
lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; 
lean_dec(x_3370);
lean_dec(x_3347);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3409 = lean_ctor_get(x_3369, 1);
lean_inc(x_3409);
if (lean_is_exclusive(x_3369)) {
 lean_ctor_release(x_3369, 0);
 lean_ctor_release(x_3369, 1);
 x_3410 = x_3369;
} else {
 lean_dec_ref(x_3369);
 x_3410 = lean_box(0);
}
if (lean_is_scalar(x_3410)) {
 x_3411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3411 = x_3410;
}
lean_ctor_set(x_3411, 0, x_3305);
lean_ctor_set(x_3411, 1, x_3409);
return x_3411;
}
}
else
{
lean_object* x_3412; lean_object* x_3413; 
lean_dec(x_3347);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3412 = lean_ctor_get(x_3369, 0);
lean_inc(x_3412);
x_3413 = lean_ctor_get(x_3369, 1);
lean_inc(x_3413);
lean_dec(x_3369);
x_8 = x_3412;
x_9 = x_3413;
goto block_16;
}
}
else
{
lean_object* x_3414; lean_object* x_3415; 
lean_dec(x_3351);
lean_dec(x_3349);
lean_dec(x_3347);
lean_dec(x_3336);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3414 = lean_ctor_get(x_3352, 0);
lean_inc(x_3414);
x_3415 = lean_ctor_get(x_3352, 1);
lean_inc(x_3415);
lean_dec(x_3352);
x_8 = x_3414;
x_9 = x_3415;
goto block_16;
}
}
else
{
lean_object* x_3416; lean_object* x_3417; 
lean_dec(x_3347);
lean_dec(x_3336);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3416 = lean_ctor_get(x_3348, 0);
lean_inc(x_3416);
x_3417 = lean_ctor_get(x_3348, 1);
lean_inc(x_3417);
lean_dec(x_3348);
x_8 = x_3416;
x_9 = x_3417;
goto block_16;
}
}
}
else
{
lean_object* x_3418; lean_object* x_3419; 
lean_dec(x_3336);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3418 = lean_ctor_get(x_3341, 0);
lean_inc(x_3418);
x_3419 = lean_ctor_get(x_3341, 1);
lean_inc(x_3419);
lean_dec(x_3341);
x_8 = x_3418;
x_9 = x_3419;
goto block_16;
}
}
else
{
lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; 
lean_dec(x_3336);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3420 = lean_ctor_get(x_3337, 1);
lean_inc(x_3420);
if (lean_is_exclusive(x_3337)) {
 lean_ctor_release(x_3337, 0);
 lean_ctor_release(x_3337, 1);
 x_3421 = x_3337;
} else {
 lean_dec_ref(x_3337);
 x_3421 = lean_box(0);
}
if (lean_is_scalar(x_3235)) {
 x_3422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3422 = x_3235;
}
lean_ctor_set(x_3422, 0, x_3332);
if (lean_is_scalar(x_3421)) {
 x_3423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3423 = x_3421;
}
lean_ctor_set(x_3423, 0, x_3422);
lean_ctor_set(x_3423, 1, x_3420);
return x_3423;
}
}
else
{
lean_object* x_3424; lean_object* x_3425; 
lean_dec(x_3336);
lean_dec(x_3332);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3424 = lean_ctor_get(x_3337, 0);
lean_inc(x_3424);
x_3425 = lean_ctor_get(x_3337, 1);
lean_inc(x_3425);
lean_dec(x_3337);
x_8 = x_3424;
x_9 = x_3425;
goto block_16;
}
}
else
{
lean_object* x_3426; lean_object* x_3427; 
lean_dec(x_3332);
lean_dec(x_3327);
lean_dec(x_3324);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3426 = lean_ctor_get(x_3333, 0);
lean_inc(x_3426);
x_3427 = lean_ctor_get(x_3333, 1);
lean_inc(x_3427);
lean_dec(x_3333);
x_8 = x_3426;
x_9 = x_3427;
goto block_16;
}
}
else
{
lean_object* x_3428; lean_object* x_3429; 
lean_dec(x_3317);
lean_dec(x_3315);
lean_dec(x_3313);
lean_dec(x_3311);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3428 = lean_ctor_get(x_3318, 0);
lean_inc(x_3428);
x_3429 = lean_ctor_get(x_3318, 1);
lean_inc(x_3429);
lean_dec(x_3318);
x_8 = x_3428;
x_9 = x_3429;
goto block_16;
}
}
else
{
lean_object* x_3430; lean_object* x_3431; 
lean_dec(x_3313);
lean_dec(x_3311);
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3430 = lean_ctor_get(x_3314, 0);
lean_inc(x_3430);
x_3431 = lean_ctor_get(x_3314, 1);
lean_inc(x_3431);
lean_dec(x_3314);
x_8 = x_3430;
x_9 = x_3431;
goto block_16;
}
}
else
{
lean_object* x_3432; lean_object* x_3433; 
lean_dec(x_3309);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3432 = lean_ctor_get(x_3310, 0);
lean_inc(x_3432);
x_3433 = lean_ctor_get(x_3310, 1);
lean_inc(x_3433);
lean_dec(x_3310);
x_8 = x_3432;
x_9 = x_3433;
goto block_16;
}
}
else
{
lean_object* x_3434; lean_object* x_3435; lean_object* x_3436; 
lean_dec(x_3307);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3434 = lean_ctor_get(x_3306, 1);
lean_inc(x_3434);
if (lean_is_exclusive(x_3306)) {
 lean_ctor_release(x_3306, 0);
 lean_ctor_release(x_3306, 1);
 x_3435 = x_3306;
} else {
 lean_dec_ref(x_3306);
 x_3435 = lean_box(0);
}
if (lean_is_scalar(x_3435)) {
 x_3436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3436 = x_3435;
}
lean_ctor_set(x_3436, 0, x_3305);
lean_ctor_set(x_3436, 1, x_3434);
return x_3436;
}
}
else
{
lean_object* x_3437; lean_object* x_3438; 
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3437 = lean_ctor_get(x_3306, 0);
lean_inc(x_3437);
x_3438 = lean_ctor_get(x_3306, 1);
lean_inc(x_3438);
lean_dec(x_3306);
x_8 = x_3437;
x_9 = x_3438;
goto block_16;
}
}
else
{
lean_object* x_3439; lean_object* x_3440; 
lean_dec(x_3290);
lean_dec(x_3288);
lean_dec(x_3277);
lean_dec(x_3273);
lean_dec(x_3271);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3439 = lean_ctor_get(x_3291, 0);
lean_inc(x_3439);
x_3440 = lean_ctor_get(x_3291, 1);
lean_inc(x_3440);
lean_dec(x_3291);
x_8 = x_3439;
x_9 = x_3440;
goto block_16;
}
}
else
{
lean_object* x_3441; lean_object* x_3442; 
lean_dec(x_3277);
lean_dec(x_3273);
lean_dec(x_3271);
lean_dec(x_3269);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3441 = lean_ctor_get(x_3287, 0);
lean_inc(x_3441);
x_3442 = lean_ctor_get(x_3287, 1);
lean_inc(x_3442);
lean_dec(x_3287);
x_8 = x_3441;
x_9 = x_3442;
goto block_16;
}
}
}
else
{
lean_object* x_3443; lean_object* x_3444; 
lean_dec(x_3277);
lean_dec(x_3273);
lean_dec(x_3271);
lean_dec(x_3269);
lean_dec(x_3259);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3443 = lean_ctor_get(x_3279, 0);
lean_inc(x_3443);
x_3444 = lean_ctor_get(x_3279, 1);
lean_inc(x_3444);
lean_dec(x_3279);
x_8 = x_3443;
x_9 = x_3444;
goto block_16;
}
}
else
{
lean_object* x_3445; lean_object* x_3446; 
lean_dec(x_3273);
lean_dec(x_3271);
lean_dec(x_3269);
lean_dec(x_3259);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3445 = lean_ctor_get(x_3274, 0);
lean_inc(x_3445);
x_3446 = lean_ctor_get(x_3274, 1);
lean_inc(x_3446);
lean_dec(x_3274);
x_8 = x_3445;
x_9 = x_3446;
goto block_16;
}
}
else
{
lean_object* x_3447; lean_object* x_3448; 
lean_dec(x_3269);
lean_dec(x_3268);
lean_dec(x_3259);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3447 = lean_ctor_get(x_3270, 0);
lean_inc(x_3447);
x_3448 = lean_ctor_get(x_3270, 1);
lean_inc(x_3448);
lean_dec(x_3270);
x_8 = x_3447;
x_9 = x_3448;
goto block_16;
}
}
else
{
lean_object* x_3449; lean_object* x_3450; lean_object* x_3451; lean_object* x_3452; 
lean_dec(x_3266);
lean_dec(x_3265);
lean_dec(x_3259);
lean_dec(x_3258);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3449 = lean_ctor_get(x_3263, 1);
lean_inc(x_3449);
if (lean_is_exclusive(x_3263)) {
 lean_ctor_release(x_3263, 0);
 lean_ctor_release(x_3263, 1);
 x_3450 = x_3263;
} else {
 lean_dec_ref(x_3263);
 x_3450 = lean_box(0);
}
x_3451 = lean_box(0);
if (lean_is_scalar(x_3450)) {
 x_3452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3452 = x_3450;
}
lean_ctor_set(x_3452, 0, x_3451);
lean_ctor_set(x_3452, 1, x_3449);
return x_3452;
}
}
else
{
lean_object* x_3453; lean_object* x_3454; lean_object* x_3455; lean_object* x_3456; 
lean_dec(x_3265);
lean_dec(x_3264);
lean_dec(x_3259);
lean_dec(x_3258);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3453 = lean_ctor_get(x_3263, 1);
lean_inc(x_3453);
if (lean_is_exclusive(x_3263)) {
 lean_ctor_release(x_3263, 0);
 lean_ctor_release(x_3263, 1);
 x_3454 = x_3263;
} else {
 lean_dec_ref(x_3263);
 x_3454 = lean_box(0);
}
x_3455 = lean_box(0);
if (lean_is_scalar(x_3454)) {
 x_3456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3456 = x_3454;
}
lean_ctor_set(x_3456, 0, x_3455);
lean_ctor_set(x_3456, 1, x_3453);
return x_3456;
}
}
else
{
lean_object* x_3457; lean_object* x_3458; lean_object* x_3459; lean_object* x_3460; 
lean_dec(x_3264);
lean_dec(x_3259);
lean_dec(x_3258);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3457 = lean_ctor_get(x_3263, 1);
lean_inc(x_3457);
if (lean_is_exclusive(x_3263)) {
 lean_ctor_release(x_3263, 0);
 lean_ctor_release(x_3263, 1);
 x_3458 = x_3263;
} else {
 lean_dec_ref(x_3263);
 x_3458 = lean_box(0);
}
x_3459 = lean_box(0);
if (lean_is_scalar(x_3458)) {
 x_3460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3460 = x_3458;
}
lean_ctor_set(x_3460, 0, x_3459);
lean_ctor_set(x_3460, 1, x_3457);
return x_3460;
}
}
else
{
lean_object* x_3461; lean_object* x_3462; lean_object* x_3463; uint8_t x_3464; 
lean_dec(x_3259);
lean_dec(x_3258);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3461 = lean_ctor_get(x_3263, 0);
lean_inc(x_3461);
x_3462 = lean_ctor_get(x_3263, 1);
lean_inc(x_3462);
if (lean_is_exclusive(x_3263)) {
 lean_ctor_release(x_3263, 0);
 lean_ctor_release(x_3263, 1);
 x_3463 = x_3263;
} else {
 lean_dec_ref(x_3263);
 x_3463 = lean_box(0);
}
x_3464 = l_Lean_Exception_isInterrupt(x_3461);
if (x_3464 == 0)
{
uint8_t x_3465; 
x_3465 = l_Lean_Exception_isRuntime(x_3461);
if (x_3465 == 0)
{
lean_object* x_3466; lean_object* x_3467; 
lean_dec(x_3461);
x_3466 = lean_box(0);
if (lean_is_scalar(x_3463)) {
 x_3467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3467 = x_3463;
 lean_ctor_set_tag(x_3467, 0);
}
lean_ctor_set(x_3467, 0, x_3466);
lean_ctor_set(x_3467, 1, x_3462);
return x_3467;
}
else
{
lean_object* x_3468; 
if (lean_is_scalar(x_3463)) {
 x_3468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3468 = x_3463;
}
lean_ctor_set(x_3468, 0, x_3461);
lean_ctor_set(x_3468, 1, x_3462);
return x_3468;
}
}
else
{
lean_object* x_3469; 
if (lean_is_scalar(x_3463)) {
 x_3469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3469 = x_3463;
}
lean_ctor_set(x_3469, 0, x_3461);
lean_ctor_set(x_3469, 1, x_3462);
return x_3469;
}
}
}
else
{
lean_object* x_3470; lean_object* x_3471; lean_object* x_3472; uint8_t x_3473; 
lean_dec(x_3259);
lean_dec(x_3258);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3470 = lean_ctor_get(x_3260, 0);
lean_inc(x_3470);
x_3471 = lean_ctor_get(x_3260, 1);
lean_inc(x_3471);
if (lean_is_exclusive(x_3260)) {
 lean_ctor_release(x_3260, 0);
 lean_ctor_release(x_3260, 1);
 x_3472 = x_3260;
} else {
 lean_dec_ref(x_3260);
 x_3472 = lean_box(0);
}
x_3473 = l_Lean_Exception_isInterrupt(x_3470);
if (x_3473 == 0)
{
uint8_t x_3474; 
x_3474 = l_Lean_Exception_isRuntime(x_3470);
if (x_3474 == 0)
{
lean_object* x_3475; lean_object* x_3476; 
lean_dec(x_3470);
x_3475 = lean_box(0);
if (lean_is_scalar(x_3472)) {
 x_3476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3476 = x_3472;
 lean_ctor_set_tag(x_3476, 0);
}
lean_ctor_set(x_3476, 0, x_3475);
lean_ctor_set(x_3476, 1, x_3471);
return x_3476;
}
else
{
lean_object* x_3477; 
if (lean_is_scalar(x_3472)) {
 x_3477 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3477 = x_3472;
}
lean_ctor_set(x_3477, 0, x_3470);
lean_ctor_set(x_3477, 1, x_3471);
return x_3477;
}
}
else
{
lean_object* x_3478; 
if (lean_is_scalar(x_3472)) {
 x_3478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3478 = x_3472;
}
lean_ctor_set(x_3478, 0, x_3470);
lean_ctor_set(x_3478, 1, x_3471);
return x_3478;
}
}
}
else
{
lean_object* x_3479; lean_object* x_3480; lean_object* x_3481; lean_object* x_3482; 
lean_dec(x_3256);
lean_dec(x_3255);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3479 = lean_ctor_get(x_3253, 1);
lean_inc(x_3479);
if (lean_is_exclusive(x_3253)) {
 lean_ctor_release(x_3253, 0);
 lean_ctor_release(x_3253, 1);
 x_3480 = x_3253;
} else {
 lean_dec_ref(x_3253);
 x_3480 = lean_box(0);
}
x_3481 = lean_box(0);
if (lean_is_scalar(x_3480)) {
 x_3482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3482 = x_3480;
}
lean_ctor_set(x_3482, 0, x_3481);
lean_ctor_set(x_3482, 1, x_3479);
return x_3482;
}
}
else
{
lean_object* x_3483; lean_object* x_3484; lean_object* x_3485; lean_object* x_3486; 
lean_dec(x_3255);
lean_dec(x_3254);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3483 = lean_ctor_get(x_3253, 1);
lean_inc(x_3483);
if (lean_is_exclusive(x_3253)) {
 lean_ctor_release(x_3253, 0);
 lean_ctor_release(x_3253, 1);
 x_3484 = x_3253;
} else {
 lean_dec_ref(x_3253);
 x_3484 = lean_box(0);
}
x_3485 = lean_box(0);
if (lean_is_scalar(x_3484)) {
 x_3486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3486 = x_3484;
}
lean_ctor_set(x_3486, 0, x_3485);
lean_ctor_set(x_3486, 1, x_3483);
return x_3486;
}
}
else
{
lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; lean_object* x_3490; 
lean_dec(x_3254);
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3487 = lean_ctor_get(x_3253, 1);
lean_inc(x_3487);
if (lean_is_exclusive(x_3253)) {
 lean_ctor_release(x_3253, 0);
 lean_ctor_release(x_3253, 1);
 x_3488 = x_3253;
} else {
 lean_dec_ref(x_3253);
 x_3488 = lean_box(0);
}
x_3489 = lean_box(0);
if (lean_is_scalar(x_3488)) {
 x_3490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3490 = x_3488;
}
lean_ctor_set(x_3490, 0, x_3489);
lean_ctor_set(x_3490, 1, x_3487);
return x_3490;
}
}
else
{
lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; uint8_t x_3494; 
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3491 = lean_ctor_get(x_3253, 0);
lean_inc(x_3491);
x_3492 = lean_ctor_get(x_3253, 1);
lean_inc(x_3492);
if (lean_is_exclusive(x_3253)) {
 lean_ctor_release(x_3253, 0);
 lean_ctor_release(x_3253, 1);
 x_3493 = x_3253;
} else {
 lean_dec_ref(x_3253);
 x_3493 = lean_box(0);
}
x_3494 = l_Lean_Exception_isInterrupt(x_3491);
if (x_3494 == 0)
{
uint8_t x_3495; 
x_3495 = l_Lean_Exception_isRuntime(x_3491);
if (x_3495 == 0)
{
lean_object* x_3496; lean_object* x_3497; 
lean_dec(x_3491);
x_3496 = lean_box(0);
if (lean_is_scalar(x_3493)) {
 x_3497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3497 = x_3493;
 lean_ctor_set_tag(x_3497, 0);
}
lean_ctor_set(x_3497, 0, x_3496);
lean_ctor_set(x_3497, 1, x_3492);
return x_3497;
}
else
{
lean_object* x_3498; 
if (lean_is_scalar(x_3493)) {
 x_3498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3498 = x_3493;
}
lean_ctor_set(x_3498, 0, x_3491);
lean_ctor_set(x_3498, 1, x_3492);
return x_3498;
}
}
else
{
lean_object* x_3499; 
if (lean_is_scalar(x_3493)) {
 x_3499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3499 = x_3493;
}
lean_ctor_set(x_3499, 0, x_3491);
lean_ctor_set(x_3499, 1, x_3492);
return x_3499;
}
}
}
else
{
lean_object* x_3500; lean_object* x_3501; lean_object* x_3502; uint8_t x_3503; 
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3500 = lean_ctor_get(x_3250, 0);
lean_inc(x_3500);
x_3501 = lean_ctor_get(x_3250, 1);
lean_inc(x_3501);
if (lean_is_exclusive(x_3250)) {
 lean_ctor_release(x_3250, 0);
 lean_ctor_release(x_3250, 1);
 x_3502 = x_3250;
} else {
 lean_dec_ref(x_3250);
 x_3502 = lean_box(0);
}
x_3503 = l_Lean_Exception_isInterrupt(x_3500);
if (x_3503 == 0)
{
uint8_t x_3504; 
x_3504 = l_Lean_Exception_isRuntime(x_3500);
if (x_3504 == 0)
{
lean_object* x_3505; lean_object* x_3506; 
lean_dec(x_3500);
x_3505 = lean_box(0);
if (lean_is_scalar(x_3502)) {
 x_3506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3506 = x_3502;
 lean_ctor_set_tag(x_3506, 0);
}
lean_ctor_set(x_3506, 0, x_3505);
lean_ctor_set(x_3506, 1, x_3501);
return x_3506;
}
else
{
lean_object* x_3507; 
if (lean_is_scalar(x_3502)) {
 x_3507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3507 = x_3502;
}
lean_ctor_set(x_3507, 0, x_3500);
lean_ctor_set(x_3507, 1, x_3501);
return x_3507;
}
}
else
{
lean_object* x_3508; 
if (lean_is_scalar(x_3502)) {
 x_3508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3508 = x_3502;
}
lean_ctor_set(x_3508, 0, x_3500);
lean_ctor_set(x_3508, 1, x_3501);
return x_3508;
}
}
}
}
else
{
lean_object* x_3509; lean_object* x_3510; 
lean_dec(x_3214);
lean_dec(x_33);
x_3509 = lean_ctor_get(x_3240, 1);
lean_inc(x_3509);
lean_dec(x_3240);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3510 = l_Lean_Meta_isMonad_x3f(x_3225, x_3, x_4, x_5, x_6, x_3509);
if (lean_obj_tag(x_3510) == 0)
{
lean_object* x_3511; 
x_3511 = lean_ctor_get(x_3510, 0);
lean_inc(x_3511);
if (lean_obj_tag(x_3511) == 0)
{
lean_object* x_3512; lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; 
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3223);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3512 = lean_ctor_get(x_3510, 1);
lean_inc(x_3512);
if (lean_is_exclusive(x_3510)) {
 lean_ctor_release(x_3510, 0);
 lean_ctor_release(x_3510, 1);
 x_3513 = x_3510;
} else {
 lean_dec_ref(x_3510);
 x_3513 = lean_box(0);
}
x_3514 = lean_box(0);
if (lean_is_scalar(x_3513)) {
 x_3515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3515 = x_3513;
}
lean_ctor_set(x_3515, 0, x_3514);
lean_ctor_set(x_3515, 1, x_3512);
return x_3515;
}
else
{
lean_object* x_3516; lean_object* x_3517; lean_object* x_3518; lean_object* x_3519; lean_object* x_3520; lean_object* x_3521; lean_object* x_3522; lean_object* x_3523; lean_object* x_3524; lean_object* x_3525; lean_object* x_3526; lean_object* x_3527; lean_object* x_3528; lean_object* x_3529; lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; 
x_3516 = lean_ctor_get(x_3510, 1);
lean_inc(x_3516);
lean_dec(x_3510);
x_3517 = lean_ctor_get(x_3511, 0);
lean_inc(x_3517);
if (lean_is_exclusive(x_3511)) {
 lean_ctor_release(x_3511, 0);
 x_3518 = x_3511;
} else {
 lean_dec_ref(x_3511);
 x_3518 = lean_box(0);
}
if (lean_is_scalar(x_3518)) {
 x_3519 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3519 = x_3518;
}
lean_ctor_set(x_3519, 0, x_3237);
if (lean_is_scalar(x_3235)) {
 x_3520 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3520 = x_3235;
}
lean_ctor_set(x_3520, 0, x_3238);
if (lean_is_scalar(x_3223)) {
 x_3521 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3521 = x_3223;
}
lean_ctor_set(x_3521, 0, x_3226);
x_3522 = lean_box(0);
x_3523 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3523, 0, x_3517);
x_3524 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3524, 0, x_1);
x_3525 = lean_box(0);
if (lean_is_scalar(x_3239)) {
 x_3526 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3526 = x_3239;
 lean_ctor_set_tag(x_3526, 1);
}
lean_ctor_set(x_3526, 0, x_3524);
lean_ctor_set(x_3526, 1, x_3525);
if (lean_is_scalar(x_3227)) {
 x_3527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3527 = x_3227;
 lean_ctor_set_tag(x_3527, 1);
}
lean_ctor_set(x_3527, 0, x_3523);
lean_ctor_set(x_3527, 1, x_3526);
x_3528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3528, 0, x_3522);
lean_ctor_set(x_3528, 1, x_3527);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_3528);
lean_ctor_set(x_31, 0, x_3521);
x_3529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3529, 0, x_3520);
lean_ctor_set(x_3529, 1, x_31);
x_3530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3530, 0, x_3519);
lean_ctor_set(x_3530, 1, x_3529);
x_3531 = lean_array_mk(x_3530);
x_3532 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3533 = l_Lean_Meta_mkAppOptM(x_3532, x_3531, x_3, x_4, x_5, x_6, x_3516);
if (lean_obj_tag(x_3533) == 0)
{
lean_object* x_3534; lean_object* x_3535; lean_object* x_3536; 
x_3534 = lean_ctor_get(x_3533, 0);
lean_inc(x_3534);
x_3535 = lean_ctor_get(x_3533, 1);
lean_inc(x_3535);
lean_dec(x_3533);
x_3536 = l_Lean_Meta_expandCoe(x_3534, x_3, x_4, x_5, x_6, x_3535);
if (lean_obj_tag(x_3536) == 0)
{
lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; lean_object* x_3540; 
x_3537 = lean_ctor_get(x_3536, 0);
lean_inc(x_3537);
x_3538 = lean_ctor_get(x_3536, 1);
lean_inc(x_3538);
lean_dec(x_3536);
x_3539 = lean_box(0);
x_3540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3540, 0, x_3537);
lean_ctor_set(x_3540, 1, x_3539);
x_17 = x_3540;
x_18 = x_3538;
goto block_30;
}
else
{
lean_object* x_3541; lean_object* x_3542; lean_object* x_3543; uint8_t x_3544; 
x_3541 = lean_ctor_get(x_3536, 0);
lean_inc(x_3541);
x_3542 = lean_ctor_get(x_3536, 1);
lean_inc(x_3542);
if (lean_is_exclusive(x_3536)) {
 lean_ctor_release(x_3536, 0);
 lean_ctor_release(x_3536, 1);
 x_3543 = x_3536;
} else {
 lean_dec_ref(x_3536);
 x_3543 = lean_box(0);
}
x_3544 = l_Lean_Exception_isInterrupt(x_3541);
if (x_3544 == 0)
{
uint8_t x_3545; 
x_3545 = l_Lean_Exception_isRuntime(x_3541);
if (x_3545 == 0)
{
lean_object* x_3546; 
lean_dec(x_3543);
lean_dec(x_3541);
x_3546 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_3546;
x_18 = x_3542;
goto block_30;
}
else
{
lean_object* x_3547; 
if (lean_is_scalar(x_3543)) {
 x_3547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3547 = x_3543;
}
lean_ctor_set(x_3547, 0, x_3541);
lean_ctor_set(x_3547, 1, x_3542);
return x_3547;
}
}
else
{
lean_object* x_3548; 
if (lean_is_scalar(x_3543)) {
 x_3548 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3548 = x_3543;
}
lean_ctor_set(x_3548, 0, x_3541);
lean_ctor_set(x_3548, 1, x_3542);
return x_3548;
}
}
}
else
{
lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; uint8_t x_3552; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3549 = lean_ctor_get(x_3533, 0);
lean_inc(x_3549);
x_3550 = lean_ctor_get(x_3533, 1);
lean_inc(x_3550);
if (lean_is_exclusive(x_3533)) {
 lean_ctor_release(x_3533, 0);
 lean_ctor_release(x_3533, 1);
 x_3551 = x_3533;
} else {
 lean_dec_ref(x_3533);
 x_3551 = lean_box(0);
}
x_3552 = l_Lean_Exception_isInterrupt(x_3549);
if (x_3552 == 0)
{
uint8_t x_3553; 
x_3553 = l_Lean_Exception_isRuntime(x_3549);
if (x_3553 == 0)
{
lean_object* x_3554; 
lean_dec(x_3551);
lean_dec(x_3549);
x_3554 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_3554;
x_18 = x_3550;
goto block_30;
}
else
{
lean_object* x_3555; 
if (lean_is_scalar(x_3551)) {
 x_3555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3555 = x_3551;
}
lean_ctor_set(x_3555, 0, x_3549);
lean_ctor_set(x_3555, 1, x_3550);
return x_3555;
}
}
else
{
lean_object* x_3556; 
if (lean_is_scalar(x_3551)) {
 x_3556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3556 = x_3551;
}
lean_ctor_set(x_3556, 0, x_3549);
lean_ctor_set(x_3556, 1, x_3550);
return x_3556;
}
}
}
}
else
{
lean_object* x_3557; lean_object* x_3558; lean_object* x_3559; lean_object* x_3560; 
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3223);
lean_free_object(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3557 = lean_ctor_get(x_3510, 0);
lean_inc(x_3557);
x_3558 = lean_ctor_get(x_3510, 1);
lean_inc(x_3558);
if (lean_is_exclusive(x_3510)) {
 lean_ctor_release(x_3510, 0);
 lean_ctor_release(x_3510, 1);
 x_3559 = x_3510;
} else {
 lean_dec_ref(x_3510);
 x_3559 = lean_box(0);
}
if (lean_is_scalar(x_3559)) {
 x_3560 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3560 = x_3559;
}
lean_ctor_set(x_3560, 0, x_3557);
lean_ctor_set(x_3560, 1, x_3558);
return x_3560;
}
}
}
else
{
lean_object* x_3561; lean_object* x_3562; lean_object* x_3563; lean_object* x_3564; 
lean_dec(x_3239);
lean_dec(x_3238);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3223);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3561 = lean_ctor_get(x_3240, 0);
lean_inc(x_3561);
x_3562 = lean_ctor_get(x_3240, 1);
lean_inc(x_3562);
if (lean_is_exclusive(x_3240)) {
 lean_ctor_release(x_3240, 0);
 lean_ctor_release(x_3240, 1);
 x_3563 = x_3240;
} else {
 lean_dec_ref(x_3240);
 x_3563 = lean_box(0);
}
if (lean_is_scalar(x_3563)) {
 x_3564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3564 = x_3563;
}
lean_ctor_set(x_3564, 0, x_3561);
lean_ctor_set(x_3564, 1, x_3562);
return x_3564;
}
}
}
else
{
lean_object* x_3565; lean_object* x_3566; lean_object* x_3567; lean_object* x_3568; 
lean_dec(x_3227);
lean_dec(x_3226);
lean_dec(x_3225);
lean_dec(x_3223);
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3565 = lean_ctor_get(x_3228, 0);
lean_inc(x_3565);
x_3566 = lean_ctor_get(x_3228, 1);
lean_inc(x_3566);
if (lean_is_exclusive(x_3228)) {
 lean_ctor_release(x_3228, 0);
 lean_ctor_release(x_3228, 1);
 x_3567 = x_3228;
} else {
 lean_dec_ref(x_3228);
 x_3567 = lean_box(0);
}
if (lean_is_scalar(x_3567)) {
 x_3568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3568 = x_3567;
}
lean_ctor_set(x_3568, 0, x_3565);
lean_ctor_set(x_3568, 1, x_3566);
return x_3568;
}
}
}
else
{
lean_object* x_3569; lean_object* x_3570; lean_object* x_3571; lean_object* x_3572; 
lean_dec(x_3214);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3569 = lean_ctor_get(x_3216, 0);
lean_inc(x_3569);
x_3570 = lean_ctor_get(x_3216, 1);
lean_inc(x_3570);
if (lean_is_exclusive(x_3216)) {
 lean_ctor_release(x_3216, 0);
 lean_ctor_release(x_3216, 1);
 x_3571 = x_3216;
} else {
 lean_dec_ref(x_3216);
 x_3571 = lean_box(0);
}
if (lean_is_scalar(x_3571)) {
 x_3572 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3572 = x_3571;
}
lean_ctor_set(x_3572, 0, x_3569);
lean_ctor_set(x_3572, 1, x_3570);
return x_3572;
}
}
}
else
{
uint8_t x_3573; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3573 = !lean_is_exclusive(x_35);
if (x_3573 == 0)
{
return x_35;
}
else
{
lean_object* x_3574; lean_object* x_3575; lean_object* x_3576; 
x_3574 = lean_ctor_get(x_35, 0);
x_3575 = lean_ctor_get(x_35, 1);
lean_inc(x_3575);
lean_inc(x_3574);
lean_dec(x_35);
x_3576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3576, 0, x_3574);
lean_ctor_set(x_3576, 1, x_3575);
return x_3576;
}
}
}
else
{
lean_object* x_3577; lean_object* x_3578; lean_object* x_3579; 
x_3577 = lean_ctor_get(x_31, 0);
x_3578 = lean_ctor_get(x_31, 1);
lean_inc(x_3578);
lean_inc(x_3577);
lean_dec(x_31);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_3579 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_3578);
if (lean_obj_tag(x_3579) == 0)
{
lean_object* x_3580; lean_object* x_3581; lean_object* x_3582; lean_object* x_3583; lean_object* x_3584; lean_object* x_3585; lean_object* x_3586; 
x_3580 = lean_ctor_get(x_3579, 0);
lean_inc(x_3580);
x_3581 = lean_ctor_get(x_3579, 1);
lean_inc(x_3581);
lean_dec(x_3579);
x_3582 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_3580, x_3, x_4, x_5, x_6, x_3581);
x_3583 = lean_ctor_get(x_3582, 0);
lean_inc(x_3583);
x_3584 = lean_ctor_get(x_3582, 1);
lean_inc(x_3584);
if (lean_is_exclusive(x_3582)) {
 lean_ctor_release(x_3582, 0);
 lean_ctor_release(x_3582, 1);
 x_3585 = x_3582;
} else {
 lean_dec_ref(x_3582);
 x_3585 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3577);
x_3586 = l_Lean_Meta_isTypeApp_x3f(x_3577, x_3, x_4, x_5, x_6, x_3584);
if (lean_obj_tag(x_3586) == 0)
{
lean_object* x_3587; 
x_3587 = lean_ctor_get(x_3586, 0);
lean_inc(x_3587);
if (lean_obj_tag(x_3587) == 0)
{
lean_object* x_3588; lean_object* x_3589; lean_object* x_3590; lean_object* x_3591; 
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3588 = lean_ctor_get(x_3586, 1);
lean_inc(x_3588);
if (lean_is_exclusive(x_3586)) {
 lean_ctor_release(x_3586, 0);
 lean_ctor_release(x_3586, 1);
 x_3589 = x_3586;
} else {
 lean_dec_ref(x_3586);
 x_3589 = lean_box(0);
}
x_3590 = lean_box(0);
if (lean_is_scalar(x_3589)) {
 x_3591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3591 = x_3589;
}
lean_ctor_set(x_3591, 0, x_3590);
lean_ctor_set(x_3591, 1, x_3588);
return x_3591;
}
else
{
lean_object* x_3592; lean_object* x_3593; lean_object* x_3594; lean_object* x_3595; lean_object* x_3596; lean_object* x_3597; lean_object* x_3598; 
x_3592 = lean_ctor_get(x_3587, 0);
lean_inc(x_3592);
if (lean_is_exclusive(x_3587)) {
 lean_ctor_release(x_3587, 0);
 x_3593 = x_3587;
} else {
 lean_dec_ref(x_3587);
 x_3593 = lean_box(0);
}
x_3594 = lean_ctor_get(x_3586, 1);
lean_inc(x_3594);
lean_dec(x_3586);
x_3595 = lean_ctor_get(x_3592, 0);
lean_inc(x_3595);
x_3596 = lean_ctor_get(x_3592, 1);
lean_inc(x_3596);
if (lean_is_exclusive(x_3592)) {
 lean_ctor_release(x_3592, 0);
 lean_ctor_release(x_3592, 1);
 x_3597 = x_3592;
} else {
 lean_dec_ref(x_3592);
 x_3597 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3583);
x_3598 = l_Lean_Meta_isTypeApp_x3f(x_3583, x_3, x_4, x_5, x_6, x_3594);
if (lean_obj_tag(x_3598) == 0)
{
lean_object* x_3599; 
x_3599 = lean_ctor_get(x_3598, 0);
lean_inc(x_3599);
if (lean_obj_tag(x_3599) == 0)
{
lean_object* x_3600; lean_object* x_3601; lean_object* x_3602; lean_object* x_3603; 
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3593);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3600 = lean_ctor_get(x_3598, 1);
lean_inc(x_3600);
if (lean_is_exclusive(x_3598)) {
 lean_ctor_release(x_3598, 0);
 lean_ctor_release(x_3598, 1);
 x_3601 = x_3598;
} else {
 lean_dec_ref(x_3598);
 x_3601 = lean_box(0);
}
x_3602 = lean_box(0);
if (lean_is_scalar(x_3601)) {
 x_3603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3603 = x_3601;
}
lean_ctor_set(x_3603, 0, x_3602);
lean_ctor_set(x_3603, 1, x_3600);
return x_3603;
}
else
{
lean_object* x_3604; lean_object* x_3605; lean_object* x_3606; lean_object* x_3607; lean_object* x_3608; lean_object* x_3609; lean_object* x_3610; 
x_3604 = lean_ctor_get(x_3599, 0);
lean_inc(x_3604);
if (lean_is_exclusive(x_3599)) {
 lean_ctor_release(x_3599, 0);
 x_3605 = x_3599;
} else {
 lean_dec_ref(x_3599);
 x_3605 = lean_box(0);
}
x_3606 = lean_ctor_get(x_3598, 1);
lean_inc(x_3606);
lean_dec(x_3598);
x_3607 = lean_ctor_get(x_3604, 0);
lean_inc(x_3607);
x_3608 = lean_ctor_get(x_3604, 1);
lean_inc(x_3608);
if (lean_is_exclusive(x_3604)) {
 lean_ctor_release(x_3604, 0);
 lean_ctor_release(x_3604, 1);
 x_3609 = x_3604;
} else {
 lean_dec_ref(x_3604);
 x_3609 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3595);
lean_inc(x_3607);
x_3610 = l_Lean_Meta_isExprDefEq(x_3607, x_3595, x_3, x_4, x_5, x_6, x_3606);
if (lean_obj_tag(x_3610) == 0)
{
lean_object* x_3611; uint8_t x_3612; 
x_3611 = lean_ctor_get(x_3610, 0);
lean_inc(x_3611);
x_3612 = lean_unbox(x_3611);
lean_dec(x_3611);
if (x_3612 == 0)
{
lean_object* x_3613; lean_object* x_3614; lean_object* x_3615; lean_object* x_3616; uint8_t x_3617; 
lean_dec(x_3593);
x_3613 = lean_ctor_get(x_3610, 1);
lean_inc(x_3613);
if (lean_is_exclusive(x_3610)) {
 lean_ctor_release(x_3610, 0);
 lean_ctor_release(x_3610, 1);
 x_3614 = x_3610;
} else {
 lean_dec_ref(x_3610);
 x_3614 = lean_box(0);
}
x_3615 = lean_ctor_get(x_5, 2);
lean_inc(x_3615);
x_3616 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_3617 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_3615, x_3616);
lean_dec(x_3615);
if (x_3617 == 0)
{
lean_object* x_3618; lean_object* x_3619; 
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3618 = lean_box(0);
if (lean_is_scalar(x_3614)) {
 x_3619 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3619 = x_3614;
}
lean_ctor_set(x_3619, 0, x_3618);
lean_ctor_set(x_3619, 1, x_3613);
return x_3619;
}
else
{
lean_object* x_3620; 
lean_dec(x_3614);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3607);
x_3620 = lean_infer_type(x_3607, x_3, x_4, x_5, x_6, x_3613);
if (lean_obj_tag(x_3620) == 0)
{
lean_object* x_3621; lean_object* x_3622; lean_object* x_3623; 
x_3621 = lean_ctor_get(x_3620, 0);
lean_inc(x_3621);
x_3622 = lean_ctor_get(x_3620, 1);
lean_inc(x_3622);
lean_dec(x_3620);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3623 = lean_whnf(x_3621, x_3, x_4, x_5, x_6, x_3622);
if (lean_obj_tag(x_3623) == 0)
{
lean_object* x_3624; 
x_3624 = lean_ctor_get(x_3623, 0);
lean_inc(x_3624);
if (lean_obj_tag(x_3624) == 7)
{
lean_object* x_3625; 
x_3625 = lean_ctor_get(x_3624, 1);
lean_inc(x_3625);
if (lean_obj_tag(x_3625) == 3)
{
lean_object* x_3626; 
x_3626 = lean_ctor_get(x_3624, 2);
lean_inc(x_3626);
lean_dec(x_3624);
if (lean_obj_tag(x_3626) == 3)
{
lean_object* x_3627; lean_object* x_3628; lean_object* x_3629; lean_object* x_3630; 
x_3627 = lean_ctor_get(x_3623, 1);
lean_inc(x_3627);
lean_dec(x_3623);
x_3628 = lean_ctor_get(x_3625, 0);
lean_inc(x_3628);
lean_dec(x_3625);
x_3629 = lean_ctor_get(x_3626, 0);
lean_inc(x_3629);
lean_dec(x_3626);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3595);
x_3630 = lean_infer_type(x_3595, x_3, x_4, x_5, x_6, x_3627);
if (lean_obj_tag(x_3630) == 0)
{
lean_object* x_3631; lean_object* x_3632; lean_object* x_3633; 
x_3631 = lean_ctor_get(x_3630, 0);
lean_inc(x_3631);
x_3632 = lean_ctor_get(x_3630, 1);
lean_inc(x_3632);
lean_dec(x_3630);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3633 = lean_whnf(x_3631, x_3, x_4, x_5, x_6, x_3632);
if (lean_obj_tag(x_3633) == 0)
{
lean_object* x_3634; 
x_3634 = lean_ctor_get(x_3633, 0);
lean_inc(x_3634);
if (lean_obj_tag(x_3634) == 7)
{
lean_object* x_3635; 
x_3635 = lean_ctor_get(x_3634, 1);
lean_inc(x_3635);
if (lean_obj_tag(x_3635) == 3)
{
lean_object* x_3636; 
x_3636 = lean_ctor_get(x_3634, 2);
lean_inc(x_3636);
lean_dec(x_3634);
if (lean_obj_tag(x_3636) == 3)
{
lean_object* x_3637; lean_object* x_3638; lean_object* x_3639; lean_object* x_3640; 
x_3637 = lean_ctor_get(x_3633, 1);
lean_inc(x_3637);
lean_dec(x_3633);
x_3638 = lean_ctor_get(x_3635, 0);
lean_inc(x_3638);
lean_dec(x_3635);
x_3639 = lean_ctor_get(x_3636, 0);
lean_inc(x_3639);
lean_dec(x_3636);
x_3640 = l_Lean_Meta_decLevel(x_3628, x_3, x_4, x_5, x_6, x_3637);
if (lean_obj_tag(x_3640) == 0)
{
lean_object* x_3641; lean_object* x_3642; lean_object* x_3643; lean_object* x_3644; 
x_3641 = lean_ctor_get(x_3640, 0);
lean_inc(x_3641);
x_3642 = lean_ctor_get(x_3640, 1);
lean_inc(x_3642);
if (lean_is_exclusive(x_3640)) {
 lean_ctor_release(x_3640, 0);
 lean_ctor_release(x_3640, 1);
 x_3643 = x_3640;
} else {
 lean_dec_ref(x_3640);
 x_3643 = lean_box(0);
}
x_3644 = l_Lean_Meta_decLevel(x_3638, x_3, x_4, x_5, x_6, x_3642);
if (lean_obj_tag(x_3644) == 0)
{
lean_object* x_3645; lean_object* x_3646; lean_object* x_3647; uint8_t x_3648; lean_object* x_3649; 
x_3645 = lean_ctor_get(x_3644, 0);
lean_inc(x_3645);
x_3646 = lean_ctor_get(x_3644, 1);
lean_inc(x_3646);
if (lean_is_exclusive(x_3644)) {
 lean_ctor_release(x_3644, 0);
 lean_ctor_release(x_3644, 1);
 x_3647 = x_3644;
} else {
 lean_dec_ref(x_3644);
 x_3647 = lean_box(0);
}
x_3648 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3641);
x_3649 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_3641, x_3645, x_3648, x_3, x_4, x_5, x_6, x_3646);
if (lean_obj_tag(x_3649) == 0)
{
lean_object* x_3650; uint8_t x_3651; 
x_3650 = lean_ctor_get(x_3649, 0);
lean_inc(x_3650);
x_3651 = lean_unbox(x_3650);
lean_dec(x_3650);
if (x_3651 == 0)
{
lean_object* x_3652; lean_object* x_3653; lean_object* x_3654; lean_object* x_3655; 
lean_dec(x_3647);
lean_dec(x_3643);
lean_dec(x_3641);
lean_dec(x_3639);
lean_dec(x_3629);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3652 = lean_ctor_get(x_3649, 1);
lean_inc(x_3652);
if (lean_is_exclusive(x_3649)) {
 lean_ctor_release(x_3649, 0);
 lean_ctor_release(x_3649, 1);
 x_3653 = x_3649;
} else {
 lean_dec_ref(x_3649);
 x_3653 = lean_box(0);
}
x_3654 = lean_box(0);
if (lean_is_scalar(x_3653)) {
 x_3655 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3655 = x_3653;
}
lean_ctor_set(x_3655, 0, x_3654);
lean_ctor_set(x_3655, 1, x_3652);
return x_3655;
}
else
{
lean_object* x_3656; lean_object* x_3657; 
x_3656 = lean_ctor_get(x_3649, 1);
lean_inc(x_3656);
lean_dec(x_3649);
x_3657 = l_Lean_Meta_decLevel(x_3629, x_3, x_4, x_5, x_6, x_3656);
if (lean_obj_tag(x_3657) == 0)
{
lean_object* x_3658; lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; 
x_3658 = lean_ctor_get(x_3657, 0);
lean_inc(x_3658);
x_3659 = lean_ctor_get(x_3657, 1);
lean_inc(x_3659);
if (lean_is_exclusive(x_3657)) {
 lean_ctor_release(x_3657, 0);
 lean_ctor_release(x_3657, 1);
 x_3660 = x_3657;
} else {
 lean_dec_ref(x_3657);
 x_3660 = lean_box(0);
}
x_3661 = l_Lean_Meta_decLevel(x_3639, x_3, x_4, x_5, x_6, x_3659);
if (lean_obj_tag(x_3661) == 0)
{
lean_object* x_3662; lean_object* x_3663; lean_object* x_3664; lean_object* x_3665; lean_object* x_3666; lean_object* x_3667; lean_object* x_3668; lean_object* x_3669; lean_object* x_3670; lean_object* x_3671; lean_object* x_3672; lean_object* x_3673; lean_object* x_3674; lean_object* x_3675; lean_object* x_3676; 
x_3662 = lean_ctor_get(x_3661, 0);
lean_inc(x_3662);
x_3663 = lean_ctor_get(x_3661, 1);
lean_inc(x_3663);
if (lean_is_exclusive(x_3661)) {
 lean_ctor_release(x_3661, 0);
 lean_ctor_release(x_3661, 1);
 x_3664 = x_3661;
} else {
 lean_dec_ref(x_3661);
 x_3664 = lean_box(0);
}
x_3665 = lean_box(0);
if (lean_is_scalar(x_3664)) {
 x_3666 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3666 = x_3664;
 lean_ctor_set_tag(x_3666, 1);
}
lean_ctor_set(x_3666, 0, x_3662);
lean_ctor_set(x_3666, 1, x_3665);
if (lean_is_scalar(x_3660)) {
 x_3667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3667 = x_3660;
 lean_ctor_set_tag(x_3667, 1);
}
lean_ctor_set(x_3667, 0, x_3658);
lean_ctor_set(x_3667, 1, x_3666);
if (lean_is_scalar(x_3647)) {
 x_3668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3668 = x_3647;
 lean_ctor_set_tag(x_3668, 1);
}
lean_ctor_set(x_3668, 0, x_3641);
lean_ctor_set(x_3668, 1, x_3667);
x_3669 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_3670 = l_Lean_Expr_const___override(x_3669, x_3668);
lean_inc(x_3595);
if (lean_is_scalar(x_3643)) {
 x_3671 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3671 = x_3643;
 lean_ctor_set_tag(x_3671, 1);
}
lean_ctor_set(x_3671, 0, x_3595);
lean_ctor_set(x_3671, 1, x_3665);
lean_inc(x_3607);
if (lean_is_scalar(x_3609)) {
 x_3672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3672 = x_3609;
 lean_ctor_set_tag(x_3672, 1);
}
lean_ctor_set(x_3672, 0, x_3607);
lean_ctor_set(x_3672, 1, x_3671);
x_3673 = lean_array_mk(x_3672);
x_3674 = l_Lean_mkAppN(x_3670, x_3673);
lean_dec(x_3673);
x_3675 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3676 = l_Lean_Meta_trySynthInstance(x_3674, x_3675, x_3, x_4, x_5, x_6, x_3663);
if (lean_obj_tag(x_3676) == 0)
{
lean_object* x_3677; 
x_3677 = lean_ctor_get(x_3676, 0);
lean_inc(x_3677);
if (lean_obj_tag(x_3677) == 1)
{
lean_object* x_3678; lean_object* x_3679; lean_object* x_3680; 
x_3678 = lean_ctor_get(x_3676, 1);
lean_inc(x_3678);
lean_dec(x_3676);
x_3679 = lean_ctor_get(x_3677, 0);
lean_inc(x_3679);
lean_dec(x_3677);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3608);
x_3680 = l_Lean_Meta_getDecLevel(x_3608, x_3, x_4, x_5, x_6, x_3678);
if (lean_obj_tag(x_3680) == 0)
{
lean_object* x_3681; lean_object* x_3682; lean_object* x_3683; lean_object* x_3684; 
x_3681 = lean_ctor_get(x_3680, 0);
lean_inc(x_3681);
x_3682 = lean_ctor_get(x_3680, 1);
lean_inc(x_3682);
if (lean_is_exclusive(x_3680)) {
 lean_ctor_release(x_3680, 0);
 lean_ctor_release(x_3680, 1);
 x_3683 = x_3680;
} else {
 lean_dec_ref(x_3680);
 x_3683 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3684 = l_Lean_Meta_getDecLevel(x_3583, x_3, x_4, x_5, x_6, x_3682);
if (lean_obj_tag(x_3684) == 0)
{
lean_object* x_3685; lean_object* x_3686; lean_object* x_3687; lean_object* x_3688; 
x_3685 = lean_ctor_get(x_3684, 0);
lean_inc(x_3685);
x_3686 = lean_ctor_get(x_3684, 1);
lean_inc(x_3686);
if (lean_is_exclusive(x_3684)) {
 lean_ctor_release(x_3684, 0);
 lean_ctor_release(x_3684, 1);
 x_3687 = x_3684;
} else {
 lean_dec_ref(x_3684);
 x_3687 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3577);
x_3688 = l_Lean_Meta_getDecLevel(x_3577, x_3, x_4, x_5, x_6, x_3686);
if (lean_obj_tag(x_3688) == 0)
{
lean_object* x_3689; lean_object* x_3690; lean_object* x_3691; lean_object* x_3692; lean_object* x_3693; lean_object* x_3694; lean_object* x_3695; lean_object* x_3696; lean_object* x_3697; lean_object* x_3698; lean_object* x_3699; lean_object* x_3700; lean_object* x_3701; lean_object* x_3702; lean_object* x_3703; lean_object* x_3704; 
x_3689 = lean_ctor_get(x_3688, 0);
lean_inc(x_3689);
x_3690 = lean_ctor_get(x_3688, 1);
lean_inc(x_3690);
if (lean_is_exclusive(x_3688)) {
 lean_ctor_release(x_3688, 0);
 lean_ctor_release(x_3688, 1);
 x_3691 = x_3688;
} else {
 lean_dec_ref(x_3688);
 x_3691 = lean_box(0);
}
if (lean_is_scalar(x_3691)) {
 x_3692 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3692 = x_3691;
 lean_ctor_set_tag(x_3692, 1);
}
lean_ctor_set(x_3692, 0, x_3689);
lean_ctor_set(x_3692, 1, x_3665);
if (lean_is_scalar(x_3687)) {
 x_3693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3693 = x_3687;
 lean_ctor_set_tag(x_3693, 1);
}
lean_ctor_set(x_3693, 0, x_3685);
lean_ctor_set(x_3693, 1, x_3692);
if (lean_is_scalar(x_3683)) {
 x_3694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3694 = x_3683;
 lean_ctor_set_tag(x_3694, 1);
}
lean_ctor_set(x_3694, 0, x_3681);
lean_ctor_set(x_3694, 1, x_3693);
x_3695 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_3694);
x_3696 = l_Lean_Expr_const___override(x_3695, x_3694);
if (lean_is_scalar(x_3597)) {
 x_3697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3697 = x_3597;
 lean_ctor_set_tag(x_3697, 1);
}
lean_ctor_set(x_3697, 0, x_1);
lean_ctor_set(x_3697, 1, x_3665);
lean_inc(x_3697);
lean_inc(x_3608);
if (lean_is_scalar(x_3585)) {
 x_3698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3698 = x_3585;
 lean_ctor_set_tag(x_3698, 1);
}
lean_ctor_set(x_3698, 0, x_3608);
lean_ctor_set(x_3698, 1, x_3697);
lean_inc(x_3679);
x_3699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3699, 0, x_3679);
lean_ctor_set(x_3699, 1, x_3698);
lean_inc(x_3595);
x_3700 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3700, 0, x_3595);
lean_ctor_set(x_3700, 1, x_3699);
lean_inc(x_3607);
x_3701 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3701, 0, x_3607);
lean_ctor_set(x_3701, 1, x_3700);
x_3702 = lean_array_mk(x_3701);
x_3703 = l_Lean_mkAppN(x_3696, x_3702);
lean_dec(x_3702);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3703);
x_3704 = lean_infer_type(x_3703, x_3, x_4, x_5, x_6, x_3690);
if (lean_obj_tag(x_3704) == 0)
{
lean_object* x_3705; lean_object* x_3706; lean_object* x_3707; lean_object* x_3708; 
x_3705 = lean_ctor_get(x_3704, 0);
lean_inc(x_3705);
x_3706 = lean_ctor_get(x_3704, 1);
lean_inc(x_3706);
if (lean_is_exclusive(x_3704)) {
 lean_ctor_release(x_3704, 0);
 lean_ctor_release(x_3704, 1);
 x_3707 = x_3704;
} else {
 lean_dec_ref(x_3704);
 x_3707 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3577);
x_3708 = l_Lean_Meta_isExprDefEq(x_3577, x_3705, x_3, x_4, x_5, x_6, x_3706);
if (lean_obj_tag(x_3708) == 0)
{
lean_object* x_3709; uint8_t x_3710; 
x_3709 = lean_ctor_get(x_3708, 0);
lean_inc(x_3709);
x_3710 = lean_unbox(x_3709);
lean_dec(x_3709);
if (x_3710 == 0)
{
lean_object* x_3711; lean_object* x_3712; 
lean_dec(x_3703);
lean_dec(x_3605);
x_3711 = lean_ctor_get(x_3708, 1);
lean_inc(x_3711);
lean_dec(x_3708);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3595);
x_3712 = l_Lean_Meta_isMonad_x3f(x_3595, x_3, x_4, x_5, x_6, x_3711);
if (lean_obj_tag(x_3712) == 0)
{
lean_object* x_3713; 
x_3713 = lean_ctor_get(x_3712, 0);
lean_inc(x_3713);
if (lean_obj_tag(x_3713) == 0)
{
lean_object* x_3714; lean_object* x_3715; lean_object* x_3716; 
lean_dec(x_3707);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3714 = lean_ctor_get(x_3712, 1);
lean_inc(x_3714);
if (lean_is_exclusive(x_3712)) {
 lean_ctor_release(x_3712, 0);
 lean_ctor_release(x_3712, 1);
 x_3715 = x_3712;
} else {
 lean_dec_ref(x_3712);
 x_3715 = lean_box(0);
}
if (lean_is_scalar(x_3715)) {
 x_3716 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3716 = x_3715;
}
lean_ctor_set(x_3716, 0, x_3675);
lean_ctor_set(x_3716, 1, x_3714);
return x_3716;
}
else
{
lean_object* x_3717; lean_object* x_3718; lean_object* x_3719; 
x_3717 = lean_ctor_get(x_3712, 1);
lean_inc(x_3717);
lean_dec(x_3712);
x_3718 = lean_ctor_get(x_3713, 0);
lean_inc(x_3718);
lean_dec(x_3713);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3608);
x_3719 = l_Lean_Meta_getLevel(x_3608, x_3, x_4, x_5, x_6, x_3717);
if (lean_obj_tag(x_3719) == 0)
{
lean_object* x_3720; lean_object* x_3721; lean_object* x_3722; lean_object* x_3723; 
x_3720 = lean_ctor_get(x_3719, 0);
lean_inc(x_3720);
x_3721 = lean_ctor_get(x_3719, 1);
lean_inc(x_3721);
if (lean_is_exclusive(x_3719)) {
 lean_ctor_release(x_3719, 0);
 lean_ctor_release(x_3719, 1);
 x_3722 = x_3719;
} else {
 lean_dec_ref(x_3719);
 x_3722 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3596);
x_3723 = l_Lean_Meta_getLevel(x_3596, x_3, x_4, x_5, x_6, x_3721);
if (lean_obj_tag(x_3723) == 0)
{
lean_object* x_3724; lean_object* x_3725; lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; lean_object* x_3729; lean_object* x_3730; lean_object* x_3731; lean_object* x_3732; lean_object* x_3733; lean_object* x_3734; lean_object* x_3735; lean_object* x_3736; lean_object* x_3737; uint8_t x_3738; lean_object* x_3739; lean_object* x_3740; 
x_3724 = lean_ctor_get(x_3723, 0);
lean_inc(x_3724);
x_3725 = lean_ctor_get(x_3723, 1);
lean_inc(x_3725);
if (lean_is_exclusive(x_3723)) {
 lean_ctor_release(x_3723, 0);
 lean_ctor_release(x_3723, 1);
 x_3726 = x_3723;
} else {
 lean_dec_ref(x_3723);
 x_3726 = lean_box(0);
}
if (lean_is_scalar(x_3726)) {
 x_3727 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3727 = x_3726;
 lean_ctor_set_tag(x_3727, 1);
}
lean_ctor_set(x_3727, 0, x_3724);
lean_ctor_set(x_3727, 1, x_3665);
if (lean_is_scalar(x_3722)) {
 x_3728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3728 = x_3722;
 lean_ctor_set_tag(x_3728, 1);
}
lean_ctor_set(x_3728, 0, x_3720);
lean_ctor_set(x_3728, 1, x_3727);
x_3729 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_3730 = l_Lean_Expr_const___override(x_3729, x_3728);
lean_inc(x_3596);
if (lean_is_scalar(x_3707)) {
 x_3731 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3731 = x_3707;
 lean_ctor_set_tag(x_3731, 1);
}
lean_ctor_set(x_3731, 0, x_3596);
lean_ctor_set(x_3731, 1, x_3665);
x_3732 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_3733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3733, 0, x_3732);
lean_ctor_set(x_3733, 1, x_3731);
lean_inc(x_3608);
x_3734 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3734, 0, x_3608);
lean_ctor_set(x_3734, 1, x_3733);
x_3735 = lean_array_mk(x_3734);
x_3736 = l_Lean_mkAppN(x_3730, x_3735);
lean_dec(x_3735);
x_3737 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_3738 = 0;
lean_inc(x_3608);
x_3739 = l_Lean_Expr_forallE___override(x_3737, x_3608, x_3736, x_3738);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3740 = l_Lean_Meta_trySynthInstance(x_3739, x_3675, x_3, x_4, x_5, x_6, x_3725);
if (lean_obj_tag(x_3740) == 0)
{
lean_object* x_3741; 
x_3741 = lean_ctor_get(x_3740, 0);
lean_inc(x_3741);
if (lean_obj_tag(x_3741) == 1)
{
lean_object* x_3742; lean_object* x_3743; lean_object* x_3744; lean_object* x_3745; lean_object* x_3746; lean_object* x_3747; lean_object* x_3748; lean_object* x_3749; lean_object* x_3750; lean_object* x_3751; lean_object* x_3752; lean_object* x_3753; lean_object* x_3754; lean_object* x_3755; 
x_3742 = lean_ctor_get(x_3740, 1);
lean_inc(x_3742);
lean_dec(x_3740);
x_3743 = lean_ctor_get(x_3741, 0);
lean_inc(x_3743);
lean_dec(x_3741);
x_3744 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_3745 = l_Lean_Expr_const___override(x_3744, x_3694);
x_3746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3746, 0, x_3718);
lean_ctor_set(x_3746, 1, x_3697);
x_3747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3747, 0, x_3743);
lean_ctor_set(x_3747, 1, x_3746);
x_3748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3748, 0, x_3679);
lean_ctor_set(x_3748, 1, x_3747);
x_3749 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3749, 0, x_3596);
lean_ctor_set(x_3749, 1, x_3748);
x_3750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3750, 0, x_3608);
lean_ctor_set(x_3750, 1, x_3749);
x_3751 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3751, 0, x_3595);
lean_ctor_set(x_3751, 1, x_3750);
x_3752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3752, 0, x_3607);
lean_ctor_set(x_3752, 1, x_3751);
x_3753 = lean_array_mk(x_3752);
x_3754 = l_Lean_mkAppN(x_3745, x_3753);
lean_dec(x_3753);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3755 = l_Lean_Meta_expandCoe(x_3754, x_3, x_4, x_5, x_6, x_3742);
if (lean_obj_tag(x_3755) == 0)
{
lean_object* x_3756; lean_object* x_3757; lean_object* x_3758; 
x_3756 = lean_ctor_get(x_3755, 0);
lean_inc(x_3756);
x_3757 = lean_ctor_get(x_3755, 1);
lean_inc(x_3757);
lean_dec(x_3755);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3756);
x_3758 = lean_infer_type(x_3756, x_3, x_4, x_5, x_6, x_3757);
if (lean_obj_tag(x_3758) == 0)
{
lean_object* x_3759; lean_object* x_3760; lean_object* x_3761; 
x_3759 = lean_ctor_get(x_3758, 0);
lean_inc(x_3759);
x_3760 = lean_ctor_get(x_3758, 1);
lean_inc(x_3760);
lean_dec(x_3758);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3761 = l_Lean_Meta_isExprDefEq(x_3577, x_3759, x_3, x_4, x_5, x_6, x_3760);
if (lean_obj_tag(x_3761) == 0)
{
lean_object* x_3762; uint8_t x_3763; 
x_3762 = lean_ctor_get(x_3761, 0);
lean_inc(x_3762);
x_3763 = lean_unbox(x_3762);
lean_dec(x_3762);
if (x_3763 == 0)
{
lean_object* x_3764; lean_object* x_3765; lean_object* x_3766; 
lean_dec(x_3756);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3764 = lean_ctor_get(x_3761, 1);
lean_inc(x_3764);
if (lean_is_exclusive(x_3761)) {
 lean_ctor_release(x_3761, 0);
 lean_ctor_release(x_3761, 1);
 x_3765 = x_3761;
} else {
 lean_dec_ref(x_3761);
 x_3765 = lean_box(0);
}
if (lean_is_scalar(x_3765)) {
 x_3766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3766 = x_3765;
}
lean_ctor_set(x_3766, 0, x_3675);
lean_ctor_set(x_3766, 1, x_3764);
return x_3766;
}
else
{
lean_object* x_3767; lean_object* x_3768; lean_object* x_3769; lean_object* x_3770; lean_object* x_3771; lean_object* x_3772; lean_object* x_3773; 
x_3767 = lean_ctor_get(x_3761, 1);
lean_inc(x_3767);
lean_dec(x_3761);
x_3768 = lean_box(0);
x_3769 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_3756, x_3768, x_3, x_4, x_5, x_6, x_3767);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3770 = lean_ctor_get(x_3769, 0);
lean_inc(x_3770);
x_3771 = lean_ctor_get(x_3769, 1);
lean_inc(x_3771);
if (lean_is_exclusive(x_3769)) {
 lean_ctor_release(x_3769, 0);
 lean_ctor_release(x_3769, 1);
 x_3772 = x_3769;
} else {
 lean_dec_ref(x_3769);
 x_3772 = lean_box(0);
}
if (lean_is_scalar(x_3772)) {
 x_3773 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3773 = x_3772;
}
lean_ctor_set(x_3773, 0, x_3770);
lean_ctor_set(x_3773, 1, x_3771);
return x_3773;
}
}
else
{
lean_object* x_3774; lean_object* x_3775; 
lean_dec(x_3756);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3774 = lean_ctor_get(x_3761, 0);
lean_inc(x_3774);
x_3775 = lean_ctor_get(x_3761, 1);
lean_inc(x_3775);
lean_dec(x_3761);
x_8 = x_3774;
x_9 = x_3775;
goto block_16;
}
}
else
{
lean_object* x_3776; lean_object* x_3777; 
lean_dec(x_3756);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3776 = lean_ctor_get(x_3758, 0);
lean_inc(x_3776);
x_3777 = lean_ctor_get(x_3758, 1);
lean_inc(x_3777);
lean_dec(x_3758);
x_8 = x_3776;
x_9 = x_3777;
goto block_16;
}
}
else
{
lean_object* x_3778; lean_object* x_3779; 
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3778 = lean_ctor_get(x_3755, 0);
lean_inc(x_3778);
x_3779 = lean_ctor_get(x_3755, 1);
lean_inc(x_3779);
lean_dec(x_3755);
x_8 = x_3778;
x_9 = x_3779;
goto block_16;
}
}
else
{
lean_object* x_3780; lean_object* x_3781; lean_object* x_3782; 
lean_dec(x_3741);
lean_dec(x_3718);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3780 = lean_ctor_get(x_3740, 1);
lean_inc(x_3780);
if (lean_is_exclusive(x_3740)) {
 lean_ctor_release(x_3740, 0);
 lean_ctor_release(x_3740, 1);
 x_3781 = x_3740;
} else {
 lean_dec_ref(x_3740);
 x_3781 = lean_box(0);
}
if (lean_is_scalar(x_3781)) {
 x_3782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3782 = x_3781;
}
lean_ctor_set(x_3782, 0, x_3675);
lean_ctor_set(x_3782, 1, x_3780);
return x_3782;
}
}
else
{
lean_object* x_3783; lean_object* x_3784; 
lean_dec(x_3718);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3783 = lean_ctor_get(x_3740, 0);
lean_inc(x_3783);
x_3784 = lean_ctor_get(x_3740, 1);
lean_inc(x_3784);
lean_dec(x_3740);
x_8 = x_3783;
x_9 = x_3784;
goto block_16;
}
}
else
{
lean_object* x_3785; lean_object* x_3786; 
lean_dec(x_3722);
lean_dec(x_3720);
lean_dec(x_3718);
lean_dec(x_3707);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3785 = lean_ctor_get(x_3723, 0);
lean_inc(x_3785);
x_3786 = lean_ctor_get(x_3723, 1);
lean_inc(x_3786);
lean_dec(x_3723);
x_8 = x_3785;
x_9 = x_3786;
goto block_16;
}
}
else
{
lean_object* x_3787; lean_object* x_3788; 
lean_dec(x_3718);
lean_dec(x_3707);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3787 = lean_ctor_get(x_3719, 0);
lean_inc(x_3787);
x_3788 = lean_ctor_get(x_3719, 1);
lean_inc(x_3788);
lean_dec(x_3719);
x_8 = x_3787;
x_9 = x_3788;
goto block_16;
}
}
}
else
{
lean_object* x_3789; lean_object* x_3790; 
lean_dec(x_3707);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3789 = lean_ctor_get(x_3712, 0);
lean_inc(x_3789);
x_3790 = lean_ctor_get(x_3712, 1);
lean_inc(x_3790);
lean_dec(x_3712);
x_8 = x_3789;
x_9 = x_3790;
goto block_16;
}
}
else
{
lean_object* x_3791; lean_object* x_3792; lean_object* x_3793; lean_object* x_3794; 
lean_dec(x_3707);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3791 = lean_ctor_get(x_3708, 1);
lean_inc(x_3791);
if (lean_is_exclusive(x_3708)) {
 lean_ctor_release(x_3708, 0);
 lean_ctor_release(x_3708, 1);
 x_3792 = x_3708;
} else {
 lean_dec_ref(x_3708);
 x_3792 = lean_box(0);
}
if (lean_is_scalar(x_3605)) {
 x_3793 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3793 = x_3605;
}
lean_ctor_set(x_3793, 0, x_3703);
if (lean_is_scalar(x_3792)) {
 x_3794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3794 = x_3792;
}
lean_ctor_set(x_3794, 0, x_3793);
lean_ctor_set(x_3794, 1, x_3791);
return x_3794;
}
}
else
{
lean_object* x_3795; lean_object* x_3796; 
lean_dec(x_3707);
lean_dec(x_3703);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3795 = lean_ctor_get(x_3708, 0);
lean_inc(x_3795);
x_3796 = lean_ctor_get(x_3708, 1);
lean_inc(x_3796);
lean_dec(x_3708);
x_8 = x_3795;
x_9 = x_3796;
goto block_16;
}
}
else
{
lean_object* x_3797; lean_object* x_3798; 
lean_dec(x_3703);
lean_dec(x_3697);
lean_dec(x_3694);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3797 = lean_ctor_get(x_3704, 0);
lean_inc(x_3797);
x_3798 = lean_ctor_get(x_3704, 1);
lean_inc(x_3798);
lean_dec(x_3704);
x_8 = x_3797;
x_9 = x_3798;
goto block_16;
}
}
else
{
lean_object* x_3799; lean_object* x_3800; 
lean_dec(x_3687);
lean_dec(x_3685);
lean_dec(x_3683);
lean_dec(x_3681);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3799 = lean_ctor_get(x_3688, 0);
lean_inc(x_3799);
x_3800 = lean_ctor_get(x_3688, 1);
lean_inc(x_3800);
lean_dec(x_3688);
x_8 = x_3799;
x_9 = x_3800;
goto block_16;
}
}
else
{
lean_object* x_3801; lean_object* x_3802; 
lean_dec(x_3683);
lean_dec(x_3681);
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3801 = lean_ctor_get(x_3684, 0);
lean_inc(x_3801);
x_3802 = lean_ctor_get(x_3684, 1);
lean_inc(x_3802);
lean_dec(x_3684);
x_8 = x_3801;
x_9 = x_3802;
goto block_16;
}
}
else
{
lean_object* x_3803; lean_object* x_3804; 
lean_dec(x_3679);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3803 = lean_ctor_get(x_3680, 0);
lean_inc(x_3803);
x_3804 = lean_ctor_get(x_3680, 1);
lean_inc(x_3804);
lean_dec(x_3680);
x_8 = x_3803;
x_9 = x_3804;
goto block_16;
}
}
else
{
lean_object* x_3805; lean_object* x_3806; lean_object* x_3807; 
lean_dec(x_3677);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3805 = lean_ctor_get(x_3676, 1);
lean_inc(x_3805);
if (lean_is_exclusive(x_3676)) {
 lean_ctor_release(x_3676, 0);
 lean_ctor_release(x_3676, 1);
 x_3806 = x_3676;
} else {
 lean_dec_ref(x_3676);
 x_3806 = lean_box(0);
}
if (lean_is_scalar(x_3806)) {
 x_3807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3807 = x_3806;
}
lean_ctor_set(x_3807, 0, x_3675);
lean_ctor_set(x_3807, 1, x_3805);
return x_3807;
}
}
else
{
lean_object* x_3808; lean_object* x_3809; 
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3808 = lean_ctor_get(x_3676, 0);
lean_inc(x_3808);
x_3809 = lean_ctor_get(x_3676, 1);
lean_inc(x_3809);
lean_dec(x_3676);
x_8 = x_3808;
x_9 = x_3809;
goto block_16;
}
}
else
{
lean_object* x_3810; lean_object* x_3811; 
lean_dec(x_3660);
lean_dec(x_3658);
lean_dec(x_3647);
lean_dec(x_3643);
lean_dec(x_3641);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3810 = lean_ctor_get(x_3661, 0);
lean_inc(x_3810);
x_3811 = lean_ctor_get(x_3661, 1);
lean_inc(x_3811);
lean_dec(x_3661);
x_8 = x_3810;
x_9 = x_3811;
goto block_16;
}
}
else
{
lean_object* x_3812; lean_object* x_3813; 
lean_dec(x_3647);
lean_dec(x_3643);
lean_dec(x_3641);
lean_dec(x_3639);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3812 = lean_ctor_get(x_3657, 0);
lean_inc(x_3812);
x_3813 = lean_ctor_get(x_3657, 1);
lean_inc(x_3813);
lean_dec(x_3657);
x_8 = x_3812;
x_9 = x_3813;
goto block_16;
}
}
}
else
{
lean_object* x_3814; lean_object* x_3815; 
lean_dec(x_3647);
lean_dec(x_3643);
lean_dec(x_3641);
lean_dec(x_3639);
lean_dec(x_3629);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3814 = lean_ctor_get(x_3649, 0);
lean_inc(x_3814);
x_3815 = lean_ctor_get(x_3649, 1);
lean_inc(x_3815);
lean_dec(x_3649);
x_8 = x_3814;
x_9 = x_3815;
goto block_16;
}
}
else
{
lean_object* x_3816; lean_object* x_3817; 
lean_dec(x_3643);
lean_dec(x_3641);
lean_dec(x_3639);
lean_dec(x_3629);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3816 = lean_ctor_get(x_3644, 0);
lean_inc(x_3816);
x_3817 = lean_ctor_get(x_3644, 1);
lean_inc(x_3817);
lean_dec(x_3644);
x_8 = x_3816;
x_9 = x_3817;
goto block_16;
}
}
else
{
lean_object* x_3818; lean_object* x_3819; 
lean_dec(x_3639);
lean_dec(x_3638);
lean_dec(x_3629);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3818 = lean_ctor_get(x_3640, 0);
lean_inc(x_3818);
x_3819 = lean_ctor_get(x_3640, 1);
lean_inc(x_3819);
lean_dec(x_3640);
x_8 = x_3818;
x_9 = x_3819;
goto block_16;
}
}
else
{
lean_object* x_3820; lean_object* x_3821; lean_object* x_3822; lean_object* x_3823; 
lean_dec(x_3636);
lean_dec(x_3635);
lean_dec(x_3629);
lean_dec(x_3628);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3820 = lean_ctor_get(x_3633, 1);
lean_inc(x_3820);
if (lean_is_exclusive(x_3633)) {
 lean_ctor_release(x_3633, 0);
 lean_ctor_release(x_3633, 1);
 x_3821 = x_3633;
} else {
 lean_dec_ref(x_3633);
 x_3821 = lean_box(0);
}
x_3822 = lean_box(0);
if (lean_is_scalar(x_3821)) {
 x_3823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3823 = x_3821;
}
lean_ctor_set(x_3823, 0, x_3822);
lean_ctor_set(x_3823, 1, x_3820);
return x_3823;
}
}
else
{
lean_object* x_3824; lean_object* x_3825; lean_object* x_3826; lean_object* x_3827; 
lean_dec(x_3635);
lean_dec(x_3634);
lean_dec(x_3629);
lean_dec(x_3628);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3824 = lean_ctor_get(x_3633, 1);
lean_inc(x_3824);
if (lean_is_exclusive(x_3633)) {
 lean_ctor_release(x_3633, 0);
 lean_ctor_release(x_3633, 1);
 x_3825 = x_3633;
} else {
 lean_dec_ref(x_3633);
 x_3825 = lean_box(0);
}
x_3826 = lean_box(0);
if (lean_is_scalar(x_3825)) {
 x_3827 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3827 = x_3825;
}
lean_ctor_set(x_3827, 0, x_3826);
lean_ctor_set(x_3827, 1, x_3824);
return x_3827;
}
}
else
{
lean_object* x_3828; lean_object* x_3829; lean_object* x_3830; lean_object* x_3831; 
lean_dec(x_3634);
lean_dec(x_3629);
lean_dec(x_3628);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3828 = lean_ctor_get(x_3633, 1);
lean_inc(x_3828);
if (lean_is_exclusive(x_3633)) {
 lean_ctor_release(x_3633, 0);
 lean_ctor_release(x_3633, 1);
 x_3829 = x_3633;
} else {
 lean_dec_ref(x_3633);
 x_3829 = lean_box(0);
}
x_3830 = lean_box(0);
if (lean_is_scalar(x_3829)) {
 x_3831 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3831 = x_3829;
}
lean_ctor_set(x_3831, 0, x_3830);
lean_ctor_set(x_3831, 1, x_3828);
return x_3831;
}
}
else
{
lean_object* x_3832; lean_object* x_3833; lean_object* x_3834; uint8_t x_3835; 
lean_dec(x_3629);
lean_dec(x_3628);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3832 = lean_ctor_get(x_3633, 0);
lean_inc(x_3832);
x_3833 = lean_ctor_get(x_3633, 1);
lean_inc(x_3833);
if (lean_is_exclusive(x_3633)) {
 lean_ctor_release(x_3633, 0);
 lean_ctor_release(x_3633, 1);
 x_3834 = x_3633;
} else {
 lean_dec_ref(x_3633);
 x_3834 = lean_box(0);
}
x_3835 = l_Lean_Exception_isInterrupt(x_3832);
if (x_3835 == 0)
{
uint8_t x_3836; 
x_3836 = l_Lean_Exception_isRuntime(x_3832);
if (x_3836 == 0)
{
lean_object* x_3837; lean_object* x_3838; 
lean_dec(x_3832);
x_3837 = lean_box(0);
if (lean_is_scalar(x_3834)) {
 x_3838 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3838 = x_3834;
 lean_ctor_set_tag(x_3838, 0);
}
lean_ctor_set(x_3838, 0, x_3837);
lean_ctor_set(x_3838, 1, x_3833);
return x_3838;
}
else
{
lean_object* x_3839; 
if (lean_is_scalar(x_3834)) {
 x_3839 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3839 = x_3834;
}
lean_ctor_set(x_3839, 0, x_3832);
lean_ctor_set(x_3839, 1, x_3833);
return x_3839;
}
}
else
{
lean_object* x_3840; 
if (lean_is_scalar(x_3834)) {
 x_3840 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3840 = x_3834;
}
lean_ctor_set(x_3840, 0, x_3832);
lean_ctor_set(x_3840, 1, x_3833);
return x_3840;
}
}
}
else
{
lean_object* x_3841; lean_object* x_3842; lean_object* x_3843; uint8_t x_3844; 
lean_dec(x_3629);
lean_dec(x_3628);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3841 = lean_ctor_get(x_3630, 0);
lean_inc(x_3841);
x_3842 = lean_ctor_get(x_3630, 1);
lean_inc(x_3842);
if (lean_is_exclusive(x_3630)) {
 lean_ctor_release(x_3630, 0);
 lean_ctor_release(x_3630, 1);
 x_3843 = x_3630;
} else {
 lean_dec_ref(x_3630);
 x_3843 = lean_box(0);
}
x_3844 = l_Lean_Exception_isInterrupt(x_3841);
if (x_3844 == 0)
{
uint8_t x_3845; 
x_3845 = l_Lean_Exception_isRuntime(x_3841);
if (x_3845 == 0)
{
lean_object* x_3846; lean_object* x_3847; 
lean_dec(x_3841);
x_3846 = lean_box(0);
if (lean_is_scalar(x_3843)) {
 x_3847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3847 = x_3843;
 lean_ctor_set_tag(x_3847, 0);
}
lean_ctor_set(x_3847, 0, x_3846);
lean_ctor_set(x_3847, 1, x_3842);
return x_3847;
}
else
{
lean_object* x_3848; 
if (lean_is_scalar(x_3843)) {
 x_3848 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3848 = x_3843;
}
lean_ctor_set(x_3848, 0, x_3841);
lean_ctor_set(x_3848, 1, x_3842);
return x_3848;
}
}
else
{
lean_object* x_3849; 
if (lean_is_scalar(x_3843)) {
 x_3849 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3849 = x_3843;
}
lean_ctor_set(x_3849, 0, x_3841);
lean_ctor_set(x_3849, 1, x_3842);
return x_3849;
}
}
}
else
{
lean_object* x_3850; lean_object* x_3851; lean_object* x_3852; lean_object* x_3853; 
lean_dec(x_3626);
lean_dec(x_3625);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3850 = lean_ctor_get(x_3623, 1);
lean_inc(x_3850);
if (lean_is_exclusive(x_3623)) {
 lean_ctor_release(x_3623, 0);
 lean_ctor_release(x_3623, 1);
 x_3851 = x_3623;
} else {
 lean_dec_ref(x_3623);
 x_3851 = lean_box(0);
}
x_3852 = lean_box(0);
if (lean_is_scalar(x_3851)) {
 x_3853 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3853 = x_3851;
}
lean_ctor_set(x_3853, 0, x_3852);
lean_ctor_set(x_3853, 1, x_3850);
return x_3853;
}
}
else
{
lean_object* x_3854; lean_object* x_3855; lean_object* x_3856; lean_object* x_3857; 
lean_dec(x_3625);
lean_dec(x_3624);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3854 = lean_ctor_get(x_3623, 1);
lean_inc(x_3854);
if (lean_is_exclusive(x_3623)) {
 lean_ctor_release(x_3623, 0);
 lean_ctor_release(x_3623, 1);
 x_3855 = x_3623;
} else {
 lean_dec_ref(x_3623);
 x_3855 = lean_box(0);
}
x_3856 = lean_box(0);
if (lean_is_scalar(x_3855)) {
 x_3857 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3857 = x_3855;
}
lean_ctor_set(x_3857, 0, x_3856);
lean_ctor_set(x_3857, 1, x_3854);
return x_3857;
}
}
else
{
lean_object* x_3858; lean_object* x_3859; lean_object* x_3860; lean_object* x_3861; 
lean_dec(x_3624);
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3858 = lean_ctor_get(x_3623, 1);
lean_inc(x_3858);
if (lean_is_exclusive(x_3623)) {
 lean_ctor_release(x_3623, 0);
 lean_ctor_release(x_3623, 1);
 x_3859 = x_3623;
} else {
 lean_dec_ref(x_3623);
 x_3859 = lean_box(0);
}
x_3860 = lean_box(0);
if (lean_is_scalar(x_3859)) {
 x_3861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3861 = x_3859;
}
lean_ctor_set(x_3861, 0, x_3860);
lean_ctor_set(x_3861, 1, x_3858);
return x_3861;
}
}
else
{
lean_object* x_3862; lean_object* x_3863; lean_object* x_3864; uint8_t x_3865; 
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3862 = lean_ctor_get(x_3623, 0);
lean_inc(x_3862);
x_3863 = lean_ctor_get(x_3623, 1);
lean_inc(x_3863);
if (lean_is_exclusive(x_3623)) {
 lean_ctor_release(x_3623, 0);
 lean_ctor_release(x_3623, 1);
 x_3864 = x_3623;
} else {
 lean_dec_ref(x_3623);
 x_3864 = lean_box(0);
}
x_3865 = l_Lean_Exception_isInterrupt(x_3862);
if (x_3865 == 0)
{
uint8_t x_3866; 
x_3866 = l_Lean_Exception_isRuntime(x_3862);
if (x_3866 == 0)
{
lean_object* x_3867; lean_object* x_3868; 
lean_dec(x_3862);
x_3867 = lean_box(0);
if (lean_is_scalar(x_3864)) {
 x_3868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3868 = x_3864;
 lean_ctor_set_tag(x_3868, 0);
}
lean_ctor_set(x_3868, 0, x_3867);
lean_ctor_set(x_3868, 1, x_3863);
return x_3868;
}
else
{
lean_object* x_3869; 
if (lean_is_scalar(x_3864)) {
 x_3869 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3869 = x_3864;
}
lean_ctor_set(x_3869, 0, x_3862);
lean_ctor_set(x_3869, 1, x_3863);
return x_3869;
}
}
else
{
lean_object* x_3870; 
if (lean_is_scalar(x_3864)) {
 x_3870 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3870 = x_3864;
}
lean_ctor_set(x_3870, 0, x_3862);
lean_ctor_set(x_3870, 1, x_3863);
return x_3870;
}
}
}
else
{
lean_object* x_3871; lean_object* x_3872; lean_object* x_3873; uint8_t x_3874; 
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3871 = lean_ctor_get(x_3620, 0);
lean_inc(x_3871);
x_3872 = lean_ctor_get(x_3620, 1);
lean_inc(x_3872);
if (lean_is_exclusive(x_3620)) {
 lean_ctor_release(x_3620, 0);
 lean_ctor_release(x_3620, 1);
 x_3873 = x_3620;
} else {
 lean_dec_ref(x_3620);
 x_3873 = lean_box(0);
}
x_3874 = l_Lean_Exception_isInterrupt(x_3871);
if (x_3874 == 0)
{
uint8_t x_3875; 
x_3875 = l_Lean_Exception_isRuntime(x_3871);
if (x_3875 == 0)
{
lean_object* x_3876; lean_object* x_3877; 
lean_dec(x_3871);
x_3876 = lean_box(0);
if (lean_is_scalar(x_3873)) {
 x_3877 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3877 = x_3873;
 lean_ctor_set_tag(x_3877, 0);
}
lean_ctor_set(x_3877, 0, x_3876);
lean_ctor_set(x_3877, 1, x_3872);
return x_3877;
}
else
{
lean_object* x_3878; 
if (lean_is_scalar(x_3873)) {
 x_3878 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3878 = x_3873;
}
lean_ctor_set(x_3878, 0, x_3871);
lean_ctor_set(x_3878, 1, x_3872);
return x_3878;
}
}
else
{
lean_object* x_3879; 
if (lean_is_scalar(x_3873)) {
 x_3879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3879 = x_3873;
}
lean_ctor_set(x_3879, 0, x_3871);
lean_ctor_set(x_3879, 1, x_3872);
return x_3879;
}
}
}
}
else
{
lean_object* x_3880; lean_object* x_3881; 
lean_dec(x_3583);
lean_dec(x_3577);
x_3880 = lean_ctor_get(x_3610, 1);
lean_inc(x_3880);
lean_dec(x_3610);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3881 = l_Lean_Meta_isMonad_x3f(x_3595, x_3, x_4, x_5, x_6, x_3880);
if (lean_obj_tag(x_3881) == 0)
{
lean_object* x_3882; 
x_3882 = lean_ctor_get(x_3881, 0);
lean_inc(x_3882);
if (lean_obj_tag(x_3882) == 0)
{
lean_object* x_3883; lean_object* x_3884; lean_object* x_3885; lean_object* x_3886; 
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3593);
lean_dec(x_3585);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3883 = lean_ctor_get(x_3881, 1);
lean_inc(x_3883);
if (lean_is_exclusive(x_3881)) {
 lean_ctor_release(x_3881, 0);
 lean_ctor_release(x_3881, 1);
 x_3884 = x_3881;
} else {
 lean_dec_ref(x_3881);
 x_3884 = lean_box(0);
}
x_3885 = lean_box(0);
if (lean_is_scalar(x_3884)) {
 x_3886 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3886 = x_3884;
}
lean_ctor_set(x_3886, 0, x_3885);
lean_ctor_set(x_3886, 1, x_3883);
return x_3886;
}
else
{
lean_object* x_3887; lean_object* x_3888; lean_object* x_3889; lean_object* x_3890; lean_object* x_3891; lean_object* x_3892; lean_object* x_3893; lean_object* x_3894; lean_object* x_3895; lean_object* x_3896; lean_object* x_3897; lean_object* x_3898; lean_object* x_3899; lean_object* x_3900; lean_object* x_3901; lean_object* x_3902; lean_object* x_3903; lean_object* x_3904; lean_object* x_3905; 
x_3887 = lean_ctor_get(x_3881, 1);
lean_inc(x_3887);
lean_dec(x_3881);
x_3888 = lean_ctor_get(x_3882, 0);
lean_inc(x_3888);
if (lean_is_exclusive(x_3882)) {
 lean_ctor_release(x_3882, 0);
 x_3889 = x_3882;
} else {
 lean_dec_ref(x_3882);
 x_3889 = lean_box(0);
}
if (lean_is_scalar(x_3889)) {
 x_3890 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3890 = x_3889;
}
lean_ctor_set(x_3890, 0, x_3607);
if (lean_is_scalar(x_3605)) {
 x_3891 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3891 = x_3605;
}
lean_ctor_set(x_3891, 0, x_3608);
if (lean_is_scalar(x_3593)) {
 x_3892 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3892 = x_3593;
}
lean_ctor_set(x_3892, 0, x_3596);
x_3893 = lean_box(0);
x_3894 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3894, 0, x_3888);
x_3895 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3895, 0, x_1);
x_3896 = lean_box(0);
if (lean_is_scalar(x_3609)) {
 x_3897 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3897 = x_3609;
 lean_ctor_set_tag(x_3897, 1);
}
lean_ctor_set(x_3897, 0, x_3895);
lean_ctor_set(x_3897, 1, x_3896);
if (lean_is_scalar(x_3597)) {
 x_3898 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3898 = x_3597;
 lean_ctor_set_tag(x_3898, 1);
}
lean_ctor_set(x_3898, 0, x_3894);
lean_ctor_set(x_3898, 1, x_3897);
if (lean_is_scalar(x_3585)) {
 x_3899 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3899 = x_3585;
 lean_ctor_set_tag(x_3899, 1);
}
lean_ctor_set(x_3899, 0, x_3893);
lean_ctor_set(x_3899, 1, x_3898);
x_3900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3900, 0, x_3892);
lean_ctor_set(x_3900, 1, x_3899);
x_3901 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3901, 0, x_3891);
lean_ctor_set(x_3901, 1, x_3900);
x_3902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3902, 0, x_3890);
lean_ctor_set(x_3902, 1, x_3901);
x_3903 = lean_array_mk(x_3902);
x_3904 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3905 = l_Lean_Meta_mkAppOptM(x_3904, x_3903, x_3, x_4, x_5, x_6, x_3887);
if (lean_obj_tag(x_3905) == 0)
{
lean_object* x_3906; lean_object* x_3907; lean_object* x_3908; 
x_3906 = lean_ctor_get(x_3905, 0);
lean_inc(x_3906);
x_3907 = lean_ctor_get(x_3905, 1);
lean_inc(x_3907);
lean_dec(x_3905);
x_3908 = l_Lean_Meta_expandCoe(x_3906, x_3, x_4, x_5, x_6, x_3907);
if (lean_obj_tag(x_3908) == 0)
{
lean_object* x_3909; lean_object* x_3910; lean_object* x_3911; lean_object* x_3912; 
x_3909 = lean_ctor_get(x_3908, 0);
lean_inc(x_3909);
x_3910 = lean_ctor_get(x_3908, 1);
lean_inc(x_3910);
lean_dec(x_3908);
x_3911 = lean_box(0);
x_3912 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3912, 0, x_3909);
lean_ctor_set(x_3912, 1, x_3911);
x_17 = x_3912;
x_18 = x_3910;
goto block_30;
}
else
{
lean_object* x_3913; lean_object* x_3914; lean_object* x_3915; uint8_t x_3916; 
x_3913 = lean_ctor_get(x_3908, 0);
lean_inc(x_3913);
x_3914 = lean_ctor_get(x_3908, 1);
lean_inc(x_3914);
if (lean_is_exclusive(x_3908)) {
 lean_ctor_release(x_3908, 0);
 lean_ctor_release(x_3908, 1);
 x_3915 = x_3908;
} else {
 lean_dec_ref(x_3908);
 x_3915 = lean_box(0);
}
x_3916 = l_Lean_Exception_isInterrupt(x_3913);
if (x_3916 == 0)
{
uint8_t x_3917; 
x_3917 = l_Lean_Exception_isRuntime(x_3913);
if (x_3917 == 0)
{
lean_object* x_3918; 
lean_dec(x_3915);
lean_dec(x_3913);
x_3918 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_3918;
x_18 = x_3914;
goto block_30;
}
else
{
lean_object* x_3919; 
if (lean_is_scalar(x_3915)) {
 x_3919 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3919 = x_3915;
}
lean_ctor_set(x_3919, 0, x_3913);
lean_ctor_set(x_3919, 1, x_3914);
return x_3919;
}
}
else
{
lean_object* x_3920; 
if (lean_is_scalar(x_3915)) {
 x_3920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3920 = x_3915;
}
lean_ctor_set(x_3920, 0, x_3913);
lean_ctor_set(x_3920, 1, x_3914);
return x_3920;
}
}
}
else
{
lean_object* x_3921; lean_object* x_3922; lean_object* x_3923; uint8_t x_3924; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3921 = lean_ctor_get(x_3905, 0);
lean_inc(x_3921);
x_3922 = lean_ctor_get(x_3905, 1);
lean_inc(x_3922);
if (lean_is_exclusive(x_3905)) {
 lean_ctor_release(x_3905, 0);
 lean_ctor_release(x_3905, 1);
 x_3923 = x_3905;
} else {
 lean_dec_ref(x_3905);
 x_3923 = lean_box(0);
}
x_3924 = l_Lean_Exception_isInterrupt(x_3921);
if (x_3924 == 0)
{
uint8_t x_3925; 
x_3925 = l_Lean_Exception_isRuntime(x_3921);
if (x_3925 == 0)
{
lean_object* x_3926; 
lean_dec(x_3923);
lean_dec(x_3921);
x_3926 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_17 = x_3926;
x_18 = x_3922;
goto block_30;
}
else
{
lean_object* x_3927; 
if (lean_is_scalar(x_3923)) {
 x_3927 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3927 = x_3923;
}
lean_ctor_set(x_3927, 0, x_3921);
lean_ctor_set(x_3927, 1, x_3922);
return x_3927;
}
}
else
{
lean_object* x_3928; 
if (lean_is_scalar(x_3923)) {
 x_3928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3928 = x_3923;
}
lean_ctor_set(x_3928, 0, x_3921);
lean_ctor_set(x_3928, 1, x_3922);
return x_3928;
}
}
}
}
else
{
lean_object* x_3929; lean_object* x_3930; lean_object* x_3931; lean_object* x_3932; 
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3593);
lean_dec(x_3585);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3929 = lean_ctor_get(x_3881, 0);
lean_inc(x_3929);
x_3930 = lean_ctor_get(x_3881, 1);
lean_inc(x_3930);
if (lean_is_exclusive(x_3881)) {
 lean_ctor_release(x_3881, 0);
 lean_ctor_release(x_3881, 1);
 x_3931 = x_3881;
} else {
 lean_dec_ref(x_3881);
 x_3931 = lean_box(0);
}
if (lean_is_scalar(x_3931)) {
 x_3932 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3932 = x_3931;
}
lean_ctor_set(x_3932, 0, x_3929);
lean_ctor_set(x_3932, 1, x_3930);
return x_3932;
}
}
}
else
{
lean_object* x_3933; lean_object* x_3934; lean_object* x_3935; lean_object* x_3936; 
lean_dec(x_3609);
lean_dec(x_3608);
lean_dec(x_3607);
lean_dec(x_3605);
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3593);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3933 = lean_ctor_get(x_3610, 0);
lean_inc(x_3933);
x_3934 = lean_ctor_get(x_3610, 1);
lean_inc(x_3934);
if (lean_is_exclusive(x_3610)) {
 lean_ctor_release(x_3610, 0);
 lean_ctor_release(x_3610, 1);
 x_3935 = x_3610;
} else {
 lean_dec_ref(x_3610);
 x_3935 = lean_box(0);
}
if (lean_is_scalar(x_3935)) {
 x_3936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3936 = x_3935;
}
lean_ctor_set(x_3936, 0, x_3933);
lean_ctor_set(x_3936, 1, x_3934);
return x_3936;
}
}
}
else
{
lean_object* x_3937; lean_object* x_3938; lean_object* x_3939; lean_object* x_3940; 
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3593);
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3937 = lean_ctor_get(x_3598, 0);
lean_inc(x_3937);
x_3938 = lean_ctor_get(x_3598, 1);
lean_inc(x_3938);
if (lean_is_exclusive(x_3598)) {
 lean_ctor_release(x_3598, 0);
 lean_ctor_release(x_3598, 1);
 x_3939 = x_3598;
} else {
 lean_dec_ref(x_3598);
 x_3939 = lean_box(0);
}
if (lean_is_scalar(x_3939)) {
 x_3940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3940 = x_3939;
}
lean_ctor_set(x_3940, 0, x_3937);
lean_ctor_set(x_3940, 1, x_3938);
return x_3940;
}
}
}
else
{
lean_object* x_3941; lean_object* x_3942; lean_object* x_3943; lean_object* x_3944; 
lean_dec(x_3585);
lean_dec(x_3583);
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3941 = lean_ctor_get(x_3586, 0);
lean_inc(x_3941);
x_3942 = lean_ctor_get(x_3586, 1);
lean_inc(x_3942);
if (lean_is_exclusive(x_3586)) {
 lean_ctor_release(x_3586, 0);
 lean_ctor_release(x_3586, 1);
 x_3943 = x_3586;
} else {
 lean_dec_ref(x_3586);
 x_3943 = lean_box(0);
}
if (lean_is_scalar(x_3943)) {
 x_3944 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3944 = x_3943;
}
lean_ctor_set(x_3944, 0, x_3941);
lean_ctor_set(x_3944, 1, x_3942);
return x_3944;
}
}
else
{
lean_object* x_3945; lean_object* x_3946; lean_object* x_3947; lean_object* x_3948; 
lean_dec(x_3577);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3945 = lean_ctor_get(x_3579, 0);
lean_inc(x_3945);
x_3946 = lean_ctor_get(x_3579, 1);
lean_inc(x_3946);
if (lean_is_exclusive(x_3579)) {
 lean_ctor_release(x_3579, 0);
 lean_ctor_release(x_3579, 1);
 x_3947 = x_3579;
} else {
 lean_dec_ref(x_3579);
 x_3947 = lean_box(0);
}
if (lean_is_scalar(x_3947)) {
 x_3948 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3948 = x_3947;
}
lean_ctor_set(x_3948, 0, x_3945);
lean_ctor_set(x_3948, 1, x_3946);
return x_3948;
}
}
block_16:
{
uint8_t x_10; 
x_10 = l_Lean_Exception_isInterrupt(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Exception_isRuntime(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
block_30:
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_17, 1, x_18);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_17, 1);
lean_dec(x_27);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 1, x_18);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
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
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_20);
x_21 = lean_infer_type(x_20, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l_Lean_Meta_isExprDefEq(x_22, x_1, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_15);
lean_dec(x_20);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_Meta_coerceSimple_x3f(x_2, x_1, x_4, x_5, x_6, x_7, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
lean_ctor_set(x_24, 0, x_15);
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_15);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_15);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_15, 0);
lean_inc(x_41);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_41);
x_42 = lean_infer_type(x_41, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_45 = l_Lean_Meta_isExprDefEq(x_43, x_1, x_4, x_5, x_6, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_41);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Meta_coerceSimple_x3f(x_2, x_1, x_4, x_5, x_6, x_7, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_41);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_56 = x_45;
} else {
 lean_dec_ref(x_45);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_42, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_60 = x_42;
} else {
 lean_dec_ref(x_42);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
return x_14;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_14, 0);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_14);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_9);
if (x_66 == 0)
{
return x_9;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_9, 0);
x_68 = lean_ctor_get(x_9, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_9);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
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
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_20 = x_9;
} else {
 lean_dec_ref(x_9);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
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
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Coe(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_219_(lean_io_mk_world());
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
