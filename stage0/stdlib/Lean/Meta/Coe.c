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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3_(lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__7;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__3;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__2;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__11;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__4;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__9;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__5;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__7;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__6;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__8;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__10;
uint8_t l_Lean_Expr_isSort(lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__3;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__6;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__8;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__1;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3;
lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__2;
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__6;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__7;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__5;
static lean_object* l_Lean_Meta_expandCoe___closed__1;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__10;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__4;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__5;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__6;
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__1;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__4;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_expandCoe___lambda__2___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__12;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__6;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__3;
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__2;
static lean_object* l_Lean_Meta_expandCoe___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__4;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("coe_decl", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("coeDeclAttr", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("auxiliary definition used to implement coercion (unfolded during elaboration)", 77, 77);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__7;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__8;
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__6;
x_6 = 0;
x_7 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____lambda__1(x_1, x_2, x_3, x_4);
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("autoLift", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("insert monadic lifts (i.e., `liftM` and coercions) when needed", 62, 62);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__3;
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3;
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3;
x_2 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_3 = l_Lean_Meta_coerceMonadLift_x3f___closed__12;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_22, x_3, x_4, x_5, x_6, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_28 = l_Lean_Meta_isTypeApp_x3f(x_19, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_42 = l_Lean_Meta_isTypeApp_x3f(x_26, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
x_56 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_52);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
lean_inc(x_54);
x_60 = l_Lean_Meta_isExprDefEq(x_54, x_40, x_3, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_dec(x_58);
lean_free_object(x_29);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_60, 1);
x_65 = lean_ctor_get(x_60, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_5, 2);
lean_inc(x_66);
x_67 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_68 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; 
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = lean_box(0);
lean_ctor_set(x_60, 0, x_69);
return x_60;
}
else
{
lean_object* x_70; 
lean_free_object(x_60);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_70 = lean_infer_type(x_54, x_3, x_4, x_5, x_6, x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_73 = lean_whnf(x_71, x_3, x_4, x_5, x_6, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 7)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 3)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 2);
lean_inc(x_76);
lean_dec(x_74);
if (lean_obj_tag(x_76) == 3)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_80 = lean_infer_type(x_40, x_3, x_4, x_5, x_6, x_77);
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
x_90 = l_Lean_Meta_decLevel(x_78, x_3, x_4, x_5, x_6, x_87);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = l_Lean_Meta_decLevel(x_88, x_3, x_4, x_5, x_6, x_93);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_92);
x_99 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_92, x_96, x_98, x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
uint8_t x_102; 
lean_free_object(x_94);
lean_free_object(x_90);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_99, 0);
lean_dec(x_103);
x_104 = lean_box(0);
lean_ctor_set(x_99, 0, x_104);
return x_99;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_dec(x_99);
x_109 = l_Lean_Meta_decLevel(x_79, x_3, x_4, x_5, x_6, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
x_113 = l_Lean_Meta_decLevel(x_89, x_3, x_4, x_5, x_6, x_112);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_113, 1);
x_116 = lean_box(0);
lean_ctor_set_tag(x_113, 1);
lean_ctor_set(x_113, 1, x_116);
lean_ctor_set_tag(x_109, 1);
lean_ctor_set(x_109, 1, x_113);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 1, x_109);
lean_ctor_set(x_94, 0, x_92);
x_117 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_118 = l_Lean_Expr_const___override(x_117, x_94);
lean_inc(x_40);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 1, x_116);
lean_ctor_set(x_90, 0, x_40);
lean_inc(x_54);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_90);
lean_ctor_set(x_56, 0, x_54);
x_119 = lean_array_mk(x_56);
x_120 = l_Lean_mkAppN(x_118, x_119);
lean_dec(x_119);
x_121 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_122 = l_Lean_Meta_trySynthInstance(x_120, x_121, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 1)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_126 = l_Lean_Meta_getDecLevel(x_55, x_3, x_4, x_5, x_6, x_124);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_130 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_129);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_134 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_133);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_136 = lean_ctor_get(x_134, 1);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_116);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 1, x_134);
lean_ctor_set_tag(x_126, 1);
lean_ctor_set(x_126, 1, x_130);
x_137 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_126);
x_138 = l_Lean_Expr_const___override(x_137, x_126);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_116);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_125);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_125);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_54);
lean_ctor_set(x_139, 1, x_17);
x_140 = lean_array_mk(x_139);
x_141 = l_Lean_mkAppN(x_138, x_140);
lean_dec(x_140);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_141);
x_142 = lean_infer_type(x_141, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_146 = l_Lean_Meta_isExprDefEq(x_19, x_144, x_3, x_4, x_5, x_6, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_141);
lean_free_object(x_43);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_150 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
uint8_t x_152; 
lean_free_object(x_142);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_150);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_150, 0);
lean_dec(x_153);
lean_ctor_set(x_150, 0, x_121);
return x_150;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec(x_150);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_121);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_150, 1);
lean_inc(x_156);
lean_dec(x_150);
x_157 = lean_ctor_get(x_151, 0);
lean_inc(x_157);
lean_dec(x_151);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_158 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_156);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_162 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_161);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; 
x_164 = lean_ctor_get(x_162, 1);
lean_ctor_set_tag(x_162, 1);
lean_ctor_set(x_162, 1, x_116);
lean_ctor_set_tag(x_158, 1);
lean_ctor_set(x_158, 1, x_162);
x_165 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_166 = l_Lean_Expr_const___override(x_165, x_158);
lean_inc(x_41);
lean_ctor_set_tag(x_142, 1);
lean_ctor_set(x_142, 1, x_116);
lean_ctor_set(x_142, 0, x_41);
x_167 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_142);
lean_inc(x_55);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_55);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_mk(x_169);
x_171 = l_Lean_mkAppN(x_166, x_170);
lean_dec(x_170);
x_172 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_173 = 0;
lean_inc(x_55);
x_174 = l_Lean_Expr_forallE___override(x_172, x_55, x_171, x_173);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_175 = l_Lean_Meta_trySynthInstance(x_174, x_121, x_3, x_4, x_5, x_6, x_164);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 1)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_180 = l_Lean_Expr_const___override(x_179, x_126);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_157);
lean_ctor_set(x_181, 1, x_51);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_125);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_41);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_55);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_40);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_54);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_array_mk(x_187);
x_189 = l_Lean_mkAppN(x_180, x_188);
lean_dec(x_188);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_190 = l_Lean_Meta_expandCoe(x_189, x_3, x_4, x_5, x_6, x_177);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_191);
x_193 = lean_infer_type(x_191, x_3, x_4, x_5, x_6, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_196 = l_Lean_Meta_isExprDefEq(x_19, x_194, x_3, x_4, x_5, x_6, x_195);
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
lean_dec(x_191);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_196);
if (x_199 == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_196, 0);
lean_dec(x_200);
lean_ctor_set(x_196, 0, x_121);
return x_196;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_196, 1);
lean_inc(x_201);
lean_dec(x_196);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_121);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_203 = lean_ctor_get(x_196, 1);
lean_inc(x_203);
lean_dec(x_196);
x_204 = lean_box(0);
x_205 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_191, x_204, x_3, x_4, x_5, x_6, x_203);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
return x_205;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_205);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_191);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_210 = lean_ctor_get(x_196, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_196, 1);
lean_inc(x_211);
lean_dec(x_196);
x_8 = x_210;
x_9 = x_211;
goto block_16;
}
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_191);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_212 = lean_ctor_get(x_193, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_193, 1);
lean_inc(x_213);
lean_dec(x_193);
x_8 = x_212;
x_9 = x_213;
goto block_16;
}
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_214 = lean_ctor_get(x_190, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_190, 1);
lean_inc(x_215);
lean_dec(x_190);
x_8 = x_214;
x_9 = x_215;
goto block_16;
}
}
else
{
uint8_t x_216; 
lean_dec(x_176);
lean_dec(x_157);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_175);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_175, 0);
lean_dec(x_217);
lean_ctor_set(x_175, 0, x_121);
return x_175;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_175, 1);
lean_inc(x_218);
lean_dec(x_175);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_121);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_157);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_220 = lean_ctor_get(x_175, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_175, 1);
lean_inc(x_221);
lean_dec(x_175);
x_8 = x_220;
x_9 = x_221;
goto block_16;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; 
x_222 = lean_ctor_get(x_162, 0);
x_223 = lean_ctor_get(x_162, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_162);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_116);
lean_ctor_set_tag(x_158, 1);
lean_ctor_set(x_158, 1, x_224);
x_225 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_226 = l_Lean_Expr_const___override(x_225, x_158);
lean_inc(x_41);
lean_ctor_set_tag(x_142, 1);
lean_ctor_set(x_142, 1, x_116);
lean_ctor_set(x_142, 0, x_41);
x_227 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_142);
lean_inc(x_55);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_55);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_array_mk(x_229);
x_231 = l_Lean_mkAppN(x_226, x_230);
lean_dec(x_230);
x_232 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_233 = 0;
lean_inc(x_55);
x_234 = l_Lean_Expr_forallE___override(x_232, x_55, x_231, x_233);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_235 = l_Lean_Meta_trySynthInstance(x_234, x_121, x_3, x_4, x_5, x_6, x_223);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 1)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_ctor_get(x_236, 0);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_240 = l_Lean_Expr_const___override(x_239, x_126);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_157);
lean_ctor_set(x_241, 1, x_51);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_238);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_125);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_41);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_55);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_40);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_54);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_array_mk(x_247);
x_249 = l_Lean_mkAppN(x_240, x_248);
lean_dec(x_248);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_250 = l_Lean_Meta_expandCoe(x_249, x_3, x_4, x_5, x_6, x_237);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_251);
x_253 = lean_infer_type(x_251, x_3, x_4, x_5, x_6, x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_256 = l_Lean_Meta_isExprDefEq(x_19, x_254, x_3, x_4, x_5, x_6, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_unbox(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_251);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_260 = x_256;
} else {
 lean_dec_ref(x_256);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_121);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_262 = lean_ctor_get(x_256, 1);
lean_inc(x_262);
lean_dec(x_256);
x_263 = lean_box(0);
x_264 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_251, x_263, x_3, x_4, x_5, x_6, x_262);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_251);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_269 = lean_ctor_get(x_256, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_256, 1);
lean_inc(x_270);
lean_dec(x_256);
x_8 = x_269;
x_9 = x_270;
goto block_16;
}
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_251);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_271 = lean_ctor_get(x_253, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_253, 1);
lean_inc(x_272);
lean_dec(x_253);
x_8 = x_271;
x_9 = x_272;
goto block_16;
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_273 = lean_ctor_get(x_250, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_250, 1);
lean_inc(x_274);
lean_dec(x_250);
x_8 = x_273;
x_9 = x_274;
goto block_16;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_236);
lean_dec(x_157);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_275 = lean_ctor_get(x_235, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_276 = x_235;
} else {
 lean_dec_ref(x_235);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_121);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_157);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_278 = lean_ctor_get(x_235, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_235, 1);
lean_inc(x_279);
lean_dec(x_235);
x_8 = x_278;
x_9 = x_279;
goto block_16;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_free_object(x_158);
lean_dec(x_160);
lean_dec(x_157);
lean_free_object(x_142);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_280 = lean_ctor_get(x_162, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_162, 1);
lean_inc(x_281);
lean_dec(x_162);
x_8 = x_280;
x_9 = x_281;
goto block_16;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_158, 0);
x_283 = lean_ctor_get(x_158, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_158);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_284 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_283);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
 lean_ctor_set_tag(x_288, 1);
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_116);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_282);
lean_ctor_set(x_289, 1, x_288);
x_290 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_291 = l_Lean_Expr_const___override(x_290, x_289);
lean_inc(x_41);
lean_ctor_set_tag(x_142, 1);
lean_ctor_set(x_142, 1, x_116);
lean_ctor_set(x_142, 0, x_41);
x_292 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_142);
lean_inc(x_55);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_55);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_array_mk(x_294);
x_296 = l_Lean_mkAppN(x_291, x_295);
lean_dec(x_295);
x_297 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_298 = 0;
lean_inc(x_55);
x_299 = l_Lean_Expr_forallE___override(x_297, x_55, x_296, x_298);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_300 = l_Lean_Meta_trySynthInstance(x_299, x_121, x_3, x_4, x_5, x_6, x_286);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
if (lean_obj_tag(x_301) == 1)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
lean_dec(x_301);
x_304 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_305 = l_Lean_Expr_const___override(x_304, x_126);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_157);
lean_ctor_set(x_306, 1, x_51);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_125);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_41);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_55);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_40);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_54);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_array_mk(x_312);
x_314 = l_Lean_mkAppN(x_305, x_313);
lean_dec(x_313);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_315 = l_Lean_Meta_expandCoe(x_314, x_3, x_4, x_5, x_6, x_302);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_316);
x_318 = lean_infer_type(x_316, x_3, x_4, x_5, x_6, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_321 = l_Lean_Meta_isExprDefEq(x_19, x_319, x_3, x_4, x_5, x_6, x_320);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; uint8_t x_323; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_unbox(x_322);
lean_dec(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_316);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_325 = x_321;
} else {
 lean_dec_ref(x_321);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_121);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_327 = lean_ctor_get(x_321, 1);
lean_inc(x_327);
lean_dec(x_321);
x_328 = lean_box(0);
x_329 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_316, x_328, x_3, x_4, x_5, x_6, x_327);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_332 = x_329;
} else {
 lean_dec_ref(x_329);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_316);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_334 = lean_ctor_get(x_321, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_321, 1);
lean_inc(x_335);
lean_dec(x_321);
x_8 = x_334;
x_9 = x_335;
goto block_16;
}
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_316);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_336 = lean_ctor_get(x_318, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_318, 1);
lean_inc(x_337);
lean_dec(x_318);
x_8 = x_336;
x_9 = x_337;
goto block_16;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_338 = lean_ctor_get(x_315, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_315, 1);
lean_inc(x_339);
lean_dec(x_315);
x_8 = x_338;
x_9 = x_339;
goto block_16;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_301);
lean_dec(x_157);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_340 = lean_ctor_get(x_300, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_341 = x_300;
} else {
 lean_dec_ref(x_300);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_121);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_157);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_343 = lean_ctor_get(x_300, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_300, 1);
lean_inc(x_344);
lean_dec(x_300);
x_8 = x_343;
x_9 = x_344;
goto block_16;
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_282);
lean_dec(x_157);
lean_free_object(x_142);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_345 = lean_ctor_get(x_284, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_284, 1);
lean_inc(x_346);
lean_dec(x_284);
x_8 = x_345;
x_9 = x_346;
goto block_16;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_157);
lean_free_object(x_142);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_347 = lean_ctor_get(x_158, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_158, 1);
lean_inc(x_348);
lean_dec(x_158);
x_8 = x_347;
x_9 = x_348;
goto block_16;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_free_object(x_142);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_349 = lean_ctor_get(x_150, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_150, 1);
lean_inc(x_350);
lean_dec(x_150);
x_8 = x_349;
x_9 = x_350;
goto block_16;
}
}
else
{
uint8_t x_351; 
lean_free_object(x_142);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_351 = !lean_is_exclusive(x_146);
if (x_351 == 0)
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_146, 0);
lean_dec(x_352);
lean_ctor_set(x_43, 0, x_141);
lean_ctor_set(x_146, 0, x_43);
return x_146;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_146, 1);
lean_inc(x_353);
lean_dec(x_146);
lean_ctor_set(x_43, 0, x_141);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_43);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; 
lean_free_object(x_142);
lean_dec(x_141);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_355 = lean_ctor_get(x_146, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_146, 1);
lean_inc(x_356);
lean_dec(x_146);
x_8 = x_355;
x_9 = x_356;
goto block_16;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_142, 0);
x_358 = lean_ctor_get(x_142, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_142);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_359 = l_Lean_Meta_isExprDefEq(x_19, x_357, x_3, x_4, x_5, x_6, x_358);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_unbox(x_360);
lean_dec(x_360);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_141);
lean_free_object(x_43);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
lean_dec(x_359);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_363 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_362);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_366 = x_363;
} else {
 lean_dec_ref(x_363);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_121);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_363, 1);
lean_inc(x_368);
lean_dec(x_363);
x_369 = lean_ctor_get(x_364, 0);
lean_inc(x_369);
lean_dec(x_364);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_370 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_368);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_374 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_372);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
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
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_377;
 lean_ctor_set_tag(x_378, 1);
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_116);
if (lean_is_scalar(x_373)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_373;
 lean_ctor_set_tag(x_379, 1);
}
lean_ctor_set(x_379, 0, x_371);
lean_ctor_set(x_379, 1, x_378);
x_380 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_381 = l_Lean_Expr_const___override(x_380, x_379);
lean_inc(x_41);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_41);
lean_ctor_set(x_382, 1, x_116);
x_383 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
lean_inc(x_55);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_55);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_array_mk(x_385);
x_387 = l_Lean_mkAppN(x_381, x_386);
lean_dec(x_386);
x_388 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_389 = 0;
lean_inc(x_55);
x_390 = l_Lean_Expr_forallE___override(x_388, x_55, x_387, x_389);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_391 = l_Lean_Meta_trySynthInstance(x_390, x_121, x_3, x_4, x_5, x_6, x_376);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 1)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_ctor_get(x_392, 0);
lean_inc(x_394);
lean_dec(x_392);
x_395 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_396 = l_Lean_Expr_const___override(x_395, x_126);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_369);
lean_ctor_set(x_397, 1, x_51);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_394);
lean_ctor_set(x_398, 1, x_397);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_125);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_41);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_55);
lean_ctor_set(x_401, 1, x_400);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_40);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_54);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_array_mk(x_403);
x_405 = l_Lean_mkAppN(x_396, x_404);
lean_dec(x_404);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_406 = l_Lean_Meta_expandCoe(x_405, x_3, x_4, x_5, x_6, x_393);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_407);
x_409 = lean_infer_type(x_407, x_3, x_4, x_5, x_6, x_408);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_412 = l_Lean_Meta_isExprDefEq(x_19, x_410, x_3, x_4, x_5, x_6, x_411);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; uint8_t x_414; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_unbox(x_413);
lean_dec(x_413);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_407);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_416 = x_412;
} else {
 lean_dec_ref(x_412);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_121);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_412, 1);
lean_inc(x_418);
lean_dec(x_412);
x_419 = lean_box(0);
x_420 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_407, x_419, x_3, x_4, x_5, x_6, x_418);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_423 = x_420;
} else {
 lean_dec_ref(x_420);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_421);
lean_ctor_set(x_424, 1, x_422);
return x_424;
}
}
else
{
lean_object* x_425; lean_object* x_426; 
lean_dec(x_407);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_425 = lean_ctor_get(x_412, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_412, 1);
lean_inc(x_426);
lean_dec(x_412);
x_8 = x_425;
x_9 = x_426;
goto block_16;
}
}
else
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_407);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_427 = lean_ctor_get(x_409, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_409, 1);
lean_inc(x_428);
lean_dec(x_409);
x_8 = x_427;
x_9 = x_428;
goto block_16;
}
}
else
{
lean_object* x_429; lean_object* x_430; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_429 = lean_ctor_get(x_406, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_406, 1);
lean_inc(x_430);
lean_dec(x_406);
x_8 = x_429;
x_9 = x_430;
goto block_16;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_392);
lean_dec(x_369);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_431 = lean_ctor_get(x_391, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_432 = x_391;
} else {
 lean_dec_ref(x_391);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_121);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
else
{
lean_object* x_434; lean_object* x_435; 
lean_dec(x_369);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_434 = lean_ctor_get(x_391, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_391, 1);
lean_inc(x_435);
lean_dec(x_391);
x_8 = x_434;
x_9 = x_435;
goto block_16;
}
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_436 = lean_ctor_get(x_374, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_374, 1);
lean_inc(x_437);
lean_dec(x_374);
x_8 = x_436;
x_9 = x_437;
goto block_16;
}
}
else
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_369);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_438 = lean_ctor_get(x_370, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_370, 1);
lean_inc(x_439);
lean_dec(x_370);
x_8 = x_438;
x_9 = x_439;
goto block_16;
}
}
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_440 = lean_ctor_get(x_363, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_363, 1);
lean_inc(x_441);
lean_dec(x_363);
x_8 = x_440;
x_9 = x_441;
goto block_16;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_442 = lean_ctor_get(x_359, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_443 = x_359;
} else {
 lean_dec_ref(x_359);
 x_443 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_141);
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_43);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_141);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_445 = lean_ctor_get(x_359, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_359, 1);
lean_inc(x_446);
lean_dec(x_359);
x_8 = x_445;
x_9 = x_446;
goto block_16;
}
}
}
else
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_141);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_447 = lean_ctor_get(x_142, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_142, 1);
lean_inc(x_448);
lean_dec(x_142);
x_8 = x_447;
x_9 = x_448;
goto block_16;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_449 = lean_ctor_get(x_134, 0);
x_450 = lean_ctor_get(x_134, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_134);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_116);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 1, x_451);
lean_ctor_set_tag(x_126, 1);
lean_ctor_set(x_126, 1, x_130);
x_452 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_126);
x_453 = l_Lean_Expr_const___override(x_452, x_126);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_116);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_125);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_125);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_54);
lean_ctor_set(x_454, 1, x_17);
x_455 = lean_array_mk(x_454);
x_456 = l_Lean_mkAppN(x_453, x_455);
lean_dec(x_455);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_456);
x_457 = lean_infer_type(x_456, x_3, x_4, x_5, x_6, x_450);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_460 = x_457;
} else {
 lean_dec_ref(x_457);
 x_460 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_461 = l_Lean_Meta_isExprDefEq(x_19, x_458, x_3, x_4, x_5, x_6, x_459);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; uint8_t x_463; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_unbox(x_462);
lean_dec(x_462);
if (x_463 == 0)
{
lean_object* x_464; lean_object* x_465; 
lean_dec(x_456);
lean_free_object(x_43);
x_464 = lean_ctor_get(x_461, 1);
lean_inc(x_464);
lean_dec(x_461);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_465 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_464);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_460);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_468 = x_465;
} else {
 lean_dec_ref(x_465);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_121);
lean_ctor_set(x_469, 1, x_467);
return x_469;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_465, 1);
lean_inc(x_470);
lean_dec(x_465);
x_471 = lean_ctor_get(x_466, 0);
lean_inc(x_471);
lean_dec(x_466);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_472 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_470);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_475 = x_472;
} else {
 lean_dec_ref(x_472);
 x_475 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_476 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_474);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_479 = x_476;
} else {
 lean_dec_ref(x_476);
 x_479 = lean_box(0);
}
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_480 = x_479;
 lean_ctor_set_tag(x_480, 1);
}
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_116);
if (lean_is_scalar(x_475)) {
 x_481 = lean_alloc_ctor(1, 2, 0);
} else {
 x_481 = x_475;
 lean_ctor_set_tag(x_481, 1);
}
lean_ctor_set(x_481, 0, x_473);
lean_ctor_set(x_481, 1, x_480);
x_482 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_483 = l_Lean_Expr_const___override(x_482, x_481);
lean_inc(x_41);
if (lean_is_scalar(x_460)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_460;
 lean_ctor_set_tag(x_484, 1);
}
lean_ctor_set(x_484, 0, x_41);
lean_ctor_set(x_484, 1, x_116);
x_485 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_484);
lean_inc(x_55);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_55);
lean_ctor_set(x_487, 1, x_486);
x_488 = lean_array_mk(x_487);
x_489 = l_Lean_mkAppN(x_483, x_488);
lean_dec(x_488);
x_490 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_491 = 0;
lean_inc(x_55);
x_492 = l_Lean_Expr_forallE___override(x_490, x_55, x_489, x_491);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_493 = l_Lean_Meta_trySynthInstance(x_492, x_121, x_3, x_4, x_5, x_6, x_478);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
if (lean_obj_tag(x_494) == 1)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
lean_dec(x_494);
x_497 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_498 = l_Lean_Expr_const___override(x_497, x_126);
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_471);
lean_ctor_set(x_499, 1, x_51);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_496);
lean_ctor_set(x_500, 1, x_499);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_125);
lean_ctor_set(x_501, 1, x_500);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_41);
lean_ctor_set(x_502, 1, x_501);
x_503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_503, 0, x_55);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_40);
lean_ctor_set(x_504, 1, x_503);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_54);
lean_ctor_set(x_505, 1, x_504);
x_506 = lean_array_mk(x_505);
x_507 = l_Lean_mkAppN(x_498, x_506);
lean_dec(x_506);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_508 = l_Lean_Meta_expandCoe(x_507, x_3, x_4, x_5, x_6, x_495);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_509);
x_511 = lean_infer_type(x_509, x_3, x_4, x_5, x_6, x_510);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_514 = l_Lean_Meta_isExprDefEq(x_19, x_512, x_3, x_4, x_5, x_6, x_513);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; uint8_t x_516; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_unbox(x_515);
lean_dec(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_509);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_517 = lean_ctor_get(x_514, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 x_518 = x_514;
} else {
 lean_dec_ref(x_514);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_121);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_520 = lean_ctor_get(x_514, 1);
lean_inc(x_520);
lean_dec(x_514);
x_521 = lean_box(0);
x_522 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_509, x_521, x_3, x_4, x_5, x_6, x_520);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_525 = x_522;
} else {
 lean_dec_ref(x_522);
 x_525 = lean_box(0);
}
if (lean_is_scalar(x_525)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_525;
}
lean_ctor_set(x_526, 0, x_523);
lean_ctor_set(x_526, 1, x_524);
return x_526;
}
}
else
{
lean_object* x_527; lean_object* x_528; 
lean_dec(x_509);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_527 = lean_ctor_get(x_514, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_514, 1);
lean_inc(x_528);
lean_dec(x_514);
x_8 = x_527;
x_9 = x_528;
goto block_16;
}
}
else
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_509);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_529 = lean_ctor_get(x_511, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_511, 1);
lean_inc(x_530);
lean_dec(x_511);
x_8 = x_529;
x_9 = x_530;
goto block_16;
}
}
else
{
lean_object* x_531; lean_object* x_532; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_531 = lean_ctor_get(x_508, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_508, 1);
lean_inc(x_532);
lean_dec(x_508);
x_8 = x_531;
x_9 = x_532;
goto block_16;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_494);
lean_dec(x_471);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_533 = lean_ctor_get(x_493, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_534 = x_493;
} else {
 lean_dec_ref(x_493);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_121);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; 
lean_dec(x_471);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_536 = lean_ctor_get(x_493, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_493, 1);
lean_inc(x_537);
lean_dec(x_493);
x_8 = x_536;
x_9 = x_537;
goto block_16;
}
}
else
{
lean_object* x_538; lean_object* x_539; 
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_471);
lean_dec(x_460);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_538 = lean_ctor_get(x_476, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_476, 1);
lean_inc(x_539);
lean_dec(x_476);
x_8 = x_538;
x_9 = x_539;
goto block_16;
}
}
else
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_471);
lean_dec(x_460);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_540 = lean_ctor_get(x_472, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_472, 1);
lean_inc(x_541);
lean_dec(x_472);
x_8 = x_540;
x_9 = x_541;
goto block_16;
}
}
}
else
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_460);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_542 = lean_ctor_get(x_465, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_465, 1);
lean_inc(x_543);
lean_dec(x_465);
x_8 = x_542;
x_9 = x_543;
goto block_16;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_460);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_544 = lean_ctor_get(x_461, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_545 = x_461;
} else {
 lean_dec_ref(x_461);
 x_545 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_456);
if (lean_is_scalar(x_545)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_545;
}
lean_ctor_set(x_546, 0, x_43);
lean_ctor_set(x_546, 1, x_544);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; 
lean_dec(x_460);
lean_dec(x_456);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_547 = lean_ctor_get(x_461, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_461, 1);
lean_inc(x_548);
lean_dec(x_461);
x_8 = x_547;
x_9 = x_548;
goto block_16;
}
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_456);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_549 = lean_ctor_get(x_457, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_457, 1);
lean_inc(x_550);
lean_dec(x_457);
x_8 = x_549;
x_9 = x_550;
goto block_16;
}
}
}
else
{
lean_object* x_551; lean_object* x_552; 
lean_free_object(x_130);
lean_dec(x_132);
lean_free_object(x_126);
lean_dec(x_128);
lean_dec(x_125);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_551 = lean_ctor_get(x_134, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_134, 1);
lean_inc(x_552);
lean_dec(x_134);
x_8 = x_551;
x_9 = x_552;
goto block_16;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_130, 0);
x_554 = lean_ctor_get(x_130, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_130);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_555 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_554);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_558 = x_555;
} else {
 lean_dec_ref(x_555);
 x_558 = lean_box(0);
}
if (lean_is_scalar(x_558)) {
 x_559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_559 = x_558;
 lean_ctor_set_tag(x_559, 1);
}
lean_ctor_set(x_559, 0, x_556);
lean_ctor_set(x_559, 1, x_116);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_553);
lean_ctor_set(x_560, 1, x_559);
lean_ctor_set_tag(x_126, 1);
lean_ctor_set(x_126, 1, x_560);
x_561 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_126);
x_562 = l_Lean_Expr_const___override(x_561, x_126);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_116);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_125);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_125);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_54);
lean_ctor_set(x_563, 1, x_17);
x_564 = lean_array_mk(x_563);
x_565 = l_Lean_mkAppN(x_562, x_564);
lean_dec(x_564);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_565);
x_566 = lean_infer_type(x_565, x_3, x_4, x_5, x_6, x_557);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_569 = x_566;
} else {
 lean_dec_ref(x_566);
 x_569 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_570 = l_Lean_Meta_isExprDefEq(x_19, x_567, x_3, x_4, x_5, x_6, x_568);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; uint8_t x_572; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_unbox(x_571);
lean_dec(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; 
lean_dec(x_565);
lean_free_object(x_43);
x_573 = lean_ctor_get(x_570, 1);
lean_inc(x_573);
lean_dec(x_570);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_574 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_573);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_569);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_577 = x_574;
} else {
 lean_dec_ref(x_574);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_121);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_574, 1);
lean_inc(x_579);
lean_dec(x_574);
x_580 = lean_ctor_get(x_575, 0);
lean_inc(x_580);
lean_dec(x_575);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_581 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_579);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_584 = x_581;
} else {
 lean_dec_ref(x_581);
 x_584 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_585 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_583);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; uint8_t x_600; lean_object* x_601; lean_object* x_602; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_588 = x_585;
} else {
 lean_dec_ref(x_585);
 x_588 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_589 = lean_alloc_ctor(1, 2, 0);
} else {
 x_589 = x_588;
 lean_ctor_set_tag(x_589, 1);
}
lean_ctor_set(x_589, 0, x_586);
lean_ctor_set(x_589, 1, x_116);
if (lean_is_scalar(x_584)) {
 x_590 = lean_alloc_ctor(1, 2, 0);
} else {
 x_590 = x_584;
 lean_ctor_set_tag(x_590, 1);
}
lean_ctor_set(x_590, 0, x_582);
lean_ctor_set(x_590, 1, x_589);
x_591 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_592 = l_Lean_Expr_const___override(x_591, x_590);
lean_inc(x_41);
if (lean_is_scalar(x_569)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_569;
 lean_ctor_set_tag(x_593, 1);
}
lean_ctor_set(x_593, 0, x_41);
lean_ctor_set(x_593, 1, x_116);
x_594 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_593);
lean_inc(x_55);
x_596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_596, 0, x_55);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_array_mk(x_596);
x_598 = l_Lean_mkAppN(x_592, x_597);
lean_dec(x_597);
x_599 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_600 = 0;
lean_inc(x_55);
x_601 = l_Lean_Expr_forallE___override(x_599, x_55, x_598, x_600);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_602 = l_Lean_Meta_trySynthInstance(x_601, x_121, x_3, x_4, x_5, x_6, x_587);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
if (lean_obj_tag(x_603) == 1)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = lean_ctor_get(x_603, 0);
lean_inc(x_605);
lean_dec(x_603);
x_606 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_607 = l_Lean_Expr_const___override(x_606, x_126);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_580);
lean_ctor_set(x_608, 1, x_51);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_605);
lean_ctor_set(x_609, 1, x_608);
x_610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_610, 0, x_125);
lean_ctor_set(x_610, 1, x_609);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_41);
lean_ctor_set(x_611, 1, x_610);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_55);
lean_ctor_set(x_612, 1, x_611);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_40);
lean_ctor_set(x_613, 1, x_612);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_54);
lean_ctor_set(x_614, 1, x_613);
x_615 = lean_array_mk(x_614);
x_616 = l_Lean_mkAppN(x_607, x_615);
lean_dec(x_615);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_617 = l_Lean_Meta_expandCoe(x_616, x_3, x_4, x_5, x_6, x_604);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_618);
x_620 = lean_infer_type(x_618, x_3, x_4, x_5, x_6, x_619);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_623 = l_Lean_Meta_isExprDefEq(x_19, x_621, x_3, x_4, x_5, x_6, x_622);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; uint8_t x_625; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_unbox(x_624);
lean_dec(x_624);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_618);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_626 = lean_ctor_get(x_623, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_627 = x_623;
} else {
 lean_dec_ref(x_623);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(0, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_121);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_629 = lean_ctor_get(x_623, 1);
lean_inc(x_629);
lean_dec(x_623);
x_630 = lean_box(0);
x_631 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_618, x_630, x_3, x_4, x_5, x_6, x_629);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_634 = x_631;
} else {
 lean_dec_ref(x_631);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_635 = lean_alloc_ctor(0, 2, 0);
} else {
 x_635 = x_634;
}
lean_ctor_set(x_635, 0, x_632);
lean_ctor_set(x_635, 1, x_633);
return x_635;
}
}
else
{
lean_object* x_636; lean_object* x_637; 
lean_dec(x_618);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_636 = lean_ctor_get(x_623, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_623, 1);
lean_inc(x_637);
lean_dec(x_623);
x_8 = x_636;
x_9 = x_637;
goto block_16;
}
}
else
{
lean_object* x_638; lean_object* x_639; 
lean_dec(x_618);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_638 = lean_ctor_get(x_620, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_620, 1);
lean_inc(x_639);
lean_dec(x_620);
x_8 = x_638;
x_9 = x_639;
goto block_16;
}
}
else
{
lean_object* x_640; lean_object* x_641; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_640 = lean_ctor_get(x_617, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_617, 1);
lean_inc(x_641);
lean_dec(x_617);
x_8 = x_640;
x_9 = x_641;
goto block_16;
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_603);
lean_dec(x_580);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_642 = lean_ctor_get(x_602, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_643 = x_602;
} else {
 lean_dec_ref(x_602);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_121);
lean_ctor_set(x_644, 1, x_642);
return x_644;
}
}
else
{
lean_object* x_645; lean_object* x_646; 
lean_dec(x_580);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_645 = lean_ctor_get(x_602, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_602, 1);
lean_inc(x_646);
lean_dec(x_602);
x_8 = x_645;
x_9 = x_646;
goto block_16;
}
}
else
{
lean_object* x_647; lean_object* x_648; 
lean_dec(x_584);
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_569);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_647 = lean_ctor_get(x_585, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_585, 1);
lean_inc(x_648);
lean_dec(x_585);
x_8 = x_647;
x_9 = x_648;
goto block_16;
}
}
else
{
lean_object* x_649; lean_object* x_650; 
lean_dec(x_580);
lean_dec(x_569);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_649 = lean_ctor_get(x_581, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_581, 1);
lean_inc(x_650);
lean_dec(x_581);
x_8 = x_649;
x_9 = x_650;
goto block_16;
}
}
}
else
{
lean_object* x_651; lean_object* x_652; 
lean_dec(x_569);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_651 = lean_ctor_get(x_574, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_574, 1);
lean_inc(x_652);
lean_dec(x_574);
x_8 = x_651;
x_9 = x_652;
goto block_16;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_569);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_653 = lean_ctor_get(x_570, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_654 = x_570;
} else {
 lean_dec_ref(x_570);
 x_654 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_565);
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(0, 2, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_43);
lean_ctor_set(x_655, 1, x_653);
return x_655;
}
}
else
{
lean_object* x_656; lean_object* x_657; 
lean_dec(x_569);
lean_dec(x_565);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_656 = lean_ctor_get(x_570, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_570, 1);
lean_inc(x_657);
lean_dec(x_570);
x_8 = x_656;
x_9 = x_657;
goto block_16;
}
}
else
{
lean_object* x_658; lean_object* x_659; 
lean_dec(x_565);
lean_dec(x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_658 = lean_ctor_get(x_566, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_566, 1);
lean_inc(x_659);
lean_dec(x_566);
x_8 = x_658;
x_9 = x_659;
goto block_16;
}
}
else
{
lean_object* x_660; lean_object* x_661; 
lean_dec(x_553);
lean_free_object(x_126);
lean_dec(x_128);
lean_dec(x_125);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_660 = lean_ctor_get(x_555, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_555, 1);
lean_inc(x_661);
lean_dec(x_555);
x_8 = x_660;
x_9 = x_661;
goto block_16;
}
}
}
else
{
lean_object* x_662; lean_object* x_663; 
lean_free_object(x_126);
lean_dec(x_128);
lean_dec(x_125);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_662 = lean_ctor_get(x_130, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_130, 1);
lean_inc(x_663);
lean_dec(x_130);
x_8 = x_662;
x_9 = x_663;
goto block_16;
}
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_664 = lean_ctor_get(x_126, 0);
x_665 = lean_ctor_get(x_126, 1);
lean_inc(x_665);
lean_inc(x_664);
lean_dec(x_126);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_666 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_665);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_670 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_668);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 x_673 = x_670;
} else {
 lean_dec_ref(x_670);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(1, 2, 0);
} else {
 x_674 = x_673;
 lean_ctor_set_tag(x_674, 1);
}
lean_ctor_set(x_674, 0, x_671);
lean_ctor_set(x_674, 1, x_116);
if (lean_is_scalar(x_669)) {
 x_675 = lean_alloc_ctor(1, 2, 0);
} else {
 x_675 = x_669;
 lean_ctor_set_tag(x_675, 1);
}
lean_ctor_set(x_675, 0, x_667);
lean_ctor_set(x_675, 1, x_674);
x_676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_676, 0, x_664);
lean_ctor_set(x_676, 1, x_675);
x_677 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_676);
x_678 = l_Lean_Expr_const___override(x_677, x_676);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_116);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_125);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_125);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_54);
lean_ctor_set(x_679, 1, x_17);
x_680 = lean_array_mk(x_679);
x_681 = l_Lean_mkAppN(x_678, x_680);
lean_dec(x_680);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_681);
x_682 = lean_infer_type(x_681, x_3, x_4, x_5, x_6, x_672);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_685 = x_682;
} else {
 lean_dec_ref(x_682);
 x_685 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_686 = l_Lean_Meta_isExprDefEq(x_19, x_683, x_3, x_4, x_5, x_6, x_684);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; uint8_t x_688; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_unbox(x_687);
lean_dec(x_687);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; 
lean_dec(x_681);
lean_free_object(x_43);
x_689 = lean_ctor_get(x_686, 1);
lean_inc(x_689);
lean_dec(x_686);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_690 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_689);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_685);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_693 = x_690;
} else {
 lean_dec_ref(x_690);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_121);
lean_ctor_set(x_694, 1, x_692);
return x_694;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_690, 1);
lean_inc(x_695);
lean_dec(x_690);
x_696 = lean_ctor_get(x_691, 0);
lean_inc(x_696);
lean_dec(x_691);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_697 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_695);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_700 = x_697;
} else {
 lean_dec_ref(x_697);
 x_700 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_701 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_699);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_704 = x_701;
} else {
 lean_dec_ref(x_701);
 x_704 = lean_box(0);
}
if (lean_is_scalar(x_704)) {
 x_705 = lean_alloc_ctor(1, 2, 0);
} else {
 x_705 = x_704;
 lean_ctor_set_tag(x_705, 1);
}
lean_ctor_set(x_705, 0, x_702);
lean_ctor_set(x_705, 1, x_116);
if (lean_is_scalar(x_700)) {
 x_706 = lean_alloc_ctor(1, 2, 0);
} else {
 x_706 = x_700;
 lean_ctor_set_tag(x_706, 1);
}
lean_ctor_set(x_706, 0, x_698);
lean_ctor_set(x_706, 1, x_705);
x_707 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_708 = l_Lean_Expr_const___override(x_707, x_706);
lean_inc(x_41);
if (lean_is_scalar(x_685)) {
 x_709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_709 = x_685;
 lean_ctor_set_tag(x_709, 1);
}
lean_ctor_set(x_709, 0, x_41);
lean_ctor_set(x_709, 1, x_116);
x_710 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_709);
lean_inc(x_55);
x_712 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_712, 0, x_55);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_array_mk(x_712);
x_714 = l_Lean_mkAppN(x_708, x_713);
lean_dec(x_713);
x_715 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_716 = 0;
lean_inc(x_55);
x_717 = l_Lean_Expr_forallE___override(x_715, x_55, x_714, x_716);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_718 = l_Lean_Meta_trySynthInstance(x_717, x_121, x_3, x_4, x_5, x_6, x_703);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
if (lean_obj_tag(x_719) == 1)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
x_721 = lean_ctor_get(x_719, 0);
lean_inc(x_721);
lean_dec(x_719);
x_722 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_723 = l_Lean_Expr_const___override(x_722, x_676);
x_724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_724, 0, x_696);
lean_ctor_set(x_724, 1, x_51);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_721);
lean_ctor_set(x_725, 1, x_724);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_125);
lean_ctor_set(x_726, 1, x_725);
x_727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_727, 0, x_41);
lean_ctor_set(x_727, 1, x_726);
x_728 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_728, 0, x_55);
lean_ctor_set(x_728, 1, x_727);
x_729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_729, 0, x_40);
lean_ctor_set(x_729, 1, x_728);
x_730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_730, 0, x_54);
lean_ctor_set(x_730, 1, x_729);
x_731 = lean_array_mk(x_730);
x_732 = l_Lean_mkAppN(x_723, x_731);
lean_dec(x_731);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_733 = l_Lean_Meta_expandCoe(x_732, x_3, x_4, x_5, x_6, x_720);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec(x_733);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_734);
x_736 = lean_infer_type(x_734, x_3, x_4, x_5, x_6, x_735);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
lean_dec(x_736);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_739 = l_Lean_Meta_isExprDefEq(x_19, x_737, x_3, x_4, x_5, x_6, x_738);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; uint8_t x_741; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_unbox(x_740);
lean_dec(x_740);
if (x_741 == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_734);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_742 = lean_ctor_get(x_739, 1);
lean_inc(x_742);
if (lean_is_exclusive(x_739)) {
 lean_ctor_release(x_739, 0);
 lean_ctor_release(x_739, 1);
 x_743 = x_739;
} else {
 lean_dec_ref(x_739);
 x_743 = lean_box(0);
}
if (lean_is_scalar(x_743)) {
 x_744 = lean_alloc_ctor(0, 2, 0);
} else {
 x_744 = x_743;
}
lean_ctor_set(x_744, 0, x_121);
lean_ctor_set(x_744, 1, x_742);
return x_744;
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_745 = lean_ctor_get(x_739, 1);
lean_inc(x_745);
lean_dec(x_739);
x_746 = lean_box(0);
x_747 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_734, x_746, x_3, x_4, x_5, x_6, x_745);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_750 = x_747;
} else {
 lean_dec_ref(x_747);
 x_750 = lean_box(0);
}
if (lean_is_scalar(x_750)) {
 x_751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_751 = x_750;
}
lean_ctor_set(x_751, 0, x_748);
lean_ctor_set(x_751, 1, x_749);
return x_751;
}
}
else
{
lean_object* x_752; lean_object* x_753; 
lean_dec(x_734);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_752 = lean_ctor_get(x_739, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_739, 1);
lean_inc(x_753);
lean_dec(x_739);
x_8 = x_752;
x_9 = x_753;
goto block_16;
}
}
else
{
lean_object* x_754; lean_object* x_755; 
lean_dec(x_734);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_754 = lean_ctor_get(x_736, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_736, 1);
lean_inc(x_755);
lean_dec(x_736);
x_8 = x_754;
x_9 = x_755;
goto block_16;
}
}
else
{
lean_object* x_756; lean_object* x_757; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_756 = lean_ctor_get(x_733, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_733, 1);
lean_inc(x_757);
lean_dec(x_733);
x_8 = x_756;
x_9 = x_757;
goto block_16;
}
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_719);
lean_dec(x_696);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_758 = lean_ctor_get(x_718, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_759 = x_718;
} else {
 lean_dec_ref(x_718);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_121);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
}
else
{
lean_object* x_761; lean_object* x_762; 
lean_dec(x_696);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_761 = lean_ctor_get(x_718, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_718, 1);
lean_inc(x_762);
lean_dec(x_718);
x_8 = x_761;
x_9 = x_762;
goto block_16;
}
}
else
{
lean_object* x_763; lean_object* x_764; 
lean_dec(x_700);
lean_dec(x_698);
lean_dec(x_696);
lean_dec(x_685);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_763 = lean_ctor_get(x_701, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_701, 1);
lean_inc(x_764);
lean_dec(x_701);
x_8 = x_763;
x_9 = x_764;
goto block_16;
}
}
else
{
lean_object* x_765; lean_object* x_766; 
lean_dec(x_696);
lean_dec(x_685);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_765 = lean_ctor_get(x_697, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_697, 1);
lean_inc(x_766);
lean_dec(x_697);
x_8 = x_765;
x_9 = x_766;
goto block_16;
}
}
}
else
{
lean_object* x_767; lean_object* x_768; 
lean_dec(x_685);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_767 = lean_ctor_get(x_690, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_690, 1);
lean_inc(x_768);
lean_dec(x_690);
x_8 = x_767;
x_9 = x_768;
goto block_16;
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_685);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_769 = lean_ctor_get(x_686, 1);
lean_inc(x_769);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_770 = x_686;
} else {
 lean_dec_ref(x_686);
 x_770 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_681);
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(0, 2, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_43);
lean_ctor_set(x_771, 1, x_769);
return x_771;
}
}
else
{
lean_object* x_772; lean_object* x_773; 
lean_dec(x_685);
lean_dec(x_681);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_772 = lean_ctor_get(x_686, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_686, 1);
lean_inc(x_773);
lean_dec(x_686);
x_8 = x_772;
x_9 = x_773;
goto block_16;
}
}
else
{
lean_object* x_774; lean_object* x_775; 
lean_dec(x_681);
lean_dec(x_51);
lean_dec(x_676);
lean_dec(x_125);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_774 = lean_ctor_get(x_682, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_682, 1);
lean_inc(x_775);
lean_dec(x_682);
x_8 = x_774;
x_9 = x_775;
goto block_16;
}
}
else
{
lean_object* x_776; lean_object* x_777; 
lean_dec(x_669);
lean_dec(x_667);
lean_dec(x_664);
lean_dec(x_125);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_776 = lean_ctor_get(x_670, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_670, 1);
lean_inc(x_777);
lean_dec(x_670);
x_8 = x_776;
x_9 = x_777;
goto block_16;
}
}
else
{
lean_object* x_778; lean_object* x_779; 
lean_dec(x_664);
lean_dec(x_125);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_778 = lean_ctor_get(x_666, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_666, 1);
lean_inc(x_779);
lean_dec(x_666);
x_8 = x_778;
x_9 = x_779;
goto block_16;
}
}
}
else
{
lean_object* x_780; lean_object* x_781; 
lean_dec(x_125);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_780 = lean_ctor_get(x_126, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_126, 1);
lean_inc(x_781);
lean_dec(x_126);
x_8 = x_780;
x_9 = x_781;
goto block_16;
}
}
else
{
uint8_t x_782; 
lean_dec(x_123);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_782 = !lean_is_exclusive(x_122);
if (x_782 == 0)
{
lean_object* x_783; 
x_783 = lean_ctor_get(x_122, 0);
lean_dec(x_783);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
else
{
lean_object* x_784; lean_object* x_785; 
x_784 = lean_ctor_get(x_122, 1);
lean_inc(x_784);
lean_dec(x_122);
x_785 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_785, 0, x_121);
lean_ctor_set(x_785, 1, x_784);
return x_785;
}
}
}
else
{
lean_object* x_786; lean_object* x_787; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_786 = lean_ctor_get(x_122, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_122, 1);
lean_inc(x_787);
lean_dec(x_122);
x_8 = x_786;
x_9 = x_787;
goto block_16;
}
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_788 = lean_ctor_get(x_113, 0);
x_789 = lean_ctor_get(x_113, 1);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_113);
x_790 = lean_box(0);
x_791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_791, 0, x_788);
lean_ctor_set(x_791, 1, x_790);
lean_ctor_set_tag(x_109, 1);
lean_ctor_set(x_109, 1, x_791);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 1, x_109);
lean_ctor_set(x_94, 0, x_92);
x_792 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_793 = l_Lean_Expr_const___override(x_792, x_94);
lean_inc(x_40);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 1, x_790);
lean_ctor_set(x_90, 0, x_40);
lean_inc(x_54);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_90);
lean_ctor_set(x_56, 0, x_54);
x_794 = lean_array_mk(x_56);
x_795 = l_Lean_mkAppN(x_793, x_794);
lean_dec(x_794);
x_796 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_797 = l_Lean_Meta_trySynthInstance(x_795, x_796, x_3, x_4, x_5, x_6, x_789);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; 
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
if (lean_obj_tag(x_798) == 1)
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
lean_dec(x_797);
x_800 = lean_ctor_get(x_798, 0);
lean_inc(x_800);
lean_dec(x_798);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_801 = l_Lean_Meta_getDecLevel(x_55, x_3, x_4, x_5, x_6, x_799);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_804 = x_801;
} else {
 lean_dec_ref(x_801);
 x_804 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_805 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_803);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_808 = x_805;
} else {
 lean_dec_ref(x_805);
 x_808 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_809 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_807);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 x_812 = x_809;
} else {
 lean_dec_ref(x_809);
 x_812 = lean_box(0);
}
if (lean_is_scalar(x_812)) {
 x_813 = lean_alloc_ctor(1, 2, 0);
} else {
 x_813 = x_812;
 lean_ctor_set_tag(x_813, 1);
}
lean_ctor_set(x_813, 0, x_810);
lean_ctor_set(x_813, 1, x_790);
if (lean_is_scalar(x_808)) {
 x_814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_814 = x_808;
 lean_ctor_set_tag(x_814, 1);
}
lean_ctor_set(x_814, 0, x_806);
lean_ctor_set(x_814, 1, x_813);
if (lean_is_scalar(x_804)) {
 x_815 = lean_alloc_ctor(1, 2, 0);
} else {
 x_815 = x_804;
 lean_ctor_set_tag(x_815, 1);
}
lean_ctor_set(x_815, 0, x_802);
lean_ctor_set(x_815, 1, x_814);
x_816 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_815);
x_817 = l_Lean_Expr_const___override(x_816, x_815);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_790);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_800);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_800);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_818, 0, x_54);
lean_ctor_set(x_818, 1, x_17);
x_819 = lean_array_mk(x_818);
x_820 = l_Lean_mkAppN(x_817, x_819);
lean_dec(x_819);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_820);
x_821 = lean_infer_type(x_820, x_3, x_4, x_5, x_6, x_811);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_824 = x_821;
} else {
 lean_dec_ref(x_821);
 x_824 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_825 = l_Lean_Meta_isExprDefEq(x_19, x_822, x_3, x_4, x_5, x_6, x_823);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; uint8_t x_827; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_unbox(x_826);
lean_dec(x_826);
if (x_827 == 0)
{
lean_object* x_828; lean_object* x_829; 
lean_dec(x_820);
lean_free_object(x_43);
x_828 = lean_ctor_get(x_825, 1);
lean_inc(x_828);
lean_dec(x_825);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_829 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_828);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; 
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
lean_dec(x_824);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_832 = x_829;
} else {
 lean_dec_ref(x_829);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 2, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_796);
lean_ctor_set(x_833, 1, x_831);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_834 = lean_ctor_get(x_829, 1);
lean_inc(x_834);
lean_dec(x_829);
x_835 = lean_ctor_get(x_830, 0);
lean_inc(x_835);
lean_dec(x_830);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_836 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_834);
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
lean_inc(x_41);
x_840 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_838);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; uint8_t x_855; lean_object* x_856; lean_object* x_857; 
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 lean_ctor_release(x_840, 1);
 x_843 = x_840;
} else {
 lean_dec_ref(x_840);
 x_843 = lean_box(0);
}
if (lean_is_scalar(x_843)) {
 x_844 = lean_alloc_ctor(1, 2, 0);
} else {
 x_844 = x_843;
 lean_ctor_set_tag(x_844, 1);
}
lean_ctor_set(x_844, 0, x_841);
lean_ctor_set(x_844, 1, x_790);
if (lean_is_scalar(x_839)) {
 x_845 = lean_alloc_ctor(1, 2, 0);
} else {
 x_845 = x_839;
 lean_ctor_set_tag(x_845, 1);
}
lean_ctor_set(x_845, 0, x_837);
lean_ctor_set(x_845, 1, x_844);
x_846 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_847 = l_Lean_Expr_const___override(x_846, x_845);
lean_inc(x_41);
if (lean_is_scalar(x_824)) {
 x_848 = lean_alloc_ctor(1, 2, 0);
} else {
 x_848 = x_824;
 lean_ctor_set_tag(x_848, 1);
}
lean_ctor_set(x_848, 0, x_41);
lean_ctor_set(x_848, 1, x_790);
x_849 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_850, 0, x_849);
lean_ctor_set(x_850, 1, x_848);
lean_inc(x_55);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_55);
lean_ctor_set(x_851, 1, x_850);
x_852 = lean_array_mk(x_851);
x_853 = l_Lean_mkAppN(x_847, x_852);
lean_dec(x_852);
x_854 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_855 = 0;
lean_inc(x_55);
x_856 = l_Lean_Expr_forallE___override(x_854, x_55, x_853, x_855);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_857 = l_Lean_Meta_trySynthInstance(x_856, x_796, x_3, x_4, x_5, x_6, x_842);
if (lean_obj_tag(x_857) == 0)
{
lean_object* x_858; 
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
if (lean_obj_tag(x_858) == 1)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
x_860 = lean_ctor_get(x_858, 0);
lean_inc(x_860);
lean_dec(x_858);
x_861 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_862 = l_Lean_Expr_const___override(x_861, x_815);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_835);
lean_ctor_set(x_863, 1, x_51);
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_860);
lean_ctor_set(x_864, 1, x_863);
x_865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_865, 0, x_800);
lean_ctor_set(x_865, 1, x_864);
x_866 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_866, 0, x_41);
lean_ctor_set(x_866, 1, x_865);
x_867 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_867, 0, x_55);
lean_ctor_set(x_867, 1, x_866);
x_868 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_868, 0, x_40);
lean_ctor_set(x_868, 1, x_867);
x_869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_869, 0, x_54);
lean_ctor_set(x_869, 1, x_868);
x_870 = lean_array_mk(x_869);
x_871 = l_Lean_mkAppN(x_862, x_870);
lean_dec(x_870);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_872 = l_Lean_Meta_expandCoe(x_871, x_3, x_4, x_5, x_6, x_859);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_873);
x_875 = lean_infer_type(x_873, x_3, x_4, x_5, x_6, x_874);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_878 = l_Lean_Meta_isExprDefEq(x_19, x_876, x_3, x_4, x_5, x_6, x_877);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; uint8_t x_880; 
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_unbox(x_879);
lean_dec(x_879);
if (x_880 == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_873);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_881 = lean_ctor_get(x_878, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_882 = x_878;
} else {
 lean_dec_ref(x_878);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_796);
lean_ctor_set(x_883, 1, x_881);
return x_883;
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_884 = lean_ctor_get(x_878, 1);
lean_inc(x_884);
lean_dec(x_878);
x_885 = lean_box(0);
x_886 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_873, x_885, x_3, x_4, x_5, x_6, x_884);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_889 = x_886;
} else {
 lean_dec_ref(x_886);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
else
{
lean_object* x_891; lean_object* x_892; 
lean_dec(x_873);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_891 = lean_ctor_get(x_878, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_878, 1);
lean_inc(x_892);
lean_dec(x_878);
x_8 = x_891;
x_9 = x_892;
goto block_16;
}
}
else
{
lean_object* x_893; lean_object* x_894; 
lean_dec(x_873);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_893 = lean_ctor_get(x_875, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_875, 1);
lean_inc(x_894);
lean_dec(x_875);
x_8 = x_893;
x_9 = x_894;
goto block_16;
}
}
else
{
lean_object* x_895; lean_object* x_896; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_895 = lean_ctor_get(x_872, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_872, 1);
lean_inc(x_896);
lean_dec(x_872);
x_8 = x_895;
x_9 = x_896;
goto block_16;
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
lean_dec(x_858);
lean_dec(x_835);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_897 = lean_ctor_get(x_857, 1);
lean_inc(x_897);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_898 = x_857;
} else {
 lean_dec_ref(x_857);
 x_898 = lean_box(0);
}
if (lean_is_scalar(x_898)) {
 x_899 = lean_alloc_ctor(0, 2, 0);
} else {
 x_899 = x_898;
}
lean_ctor_set(x_899, 0, x_796);
lean_ctor_set(x_899, 1, x_897);
return x_899;
}
}
else
{
lean_object* x_900; lean_object* x_901; 
lean_dec(x_835);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_900 = lean_ctor_get(x_857, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_857, 1);
lean_inc(x_901);
lean_dec(x_857);
x_8 = x_900;
x_9 = x_901;
goto block_16;
}
}
else
{
lean_object* x_902; lean_object* x_903; 
lean_dec(x_839);
lean_dec(x_837);
lean_dec(x_835);
lean_dec(x_824);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_902 = lean_ctor_get(x_840, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_840, 1);
lean_inc(x_903);
lean_dec(x_840);
x_8 = x_902;
x_9 = x_903;
goto block_16;
}
}
else
{
lean_object* x_904; lean_object* x_905; 
lean_dec(x_835);
lean_dec(x_824);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_904 = lean_ctor_get(x_836, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_836, 1);
lean_inc(x_905);
lean_dec(x_836);
x_8 = x_904;
x_9 = x_905;
goto block_16;
}
}
}
else
{
lean_object* x_906; lean_object* x_907; 
lean_dec(x_824);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_906 = lean_ctor_get(x_829, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_829, 1);
lean_inc(x_907);
lean_dec(x_829);
x_8 = x_906;
x_9 = x_907;
goto block_16;
}
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_824);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_908 = lean_ctor_get(x_825, 1);
lean_inc(x_908);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_909 = x_825;
} else {
 lean_dec_ref(x_825);
 x_909 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_820);
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_43);
lean_ctor_set(x_910, 1, x_908);
return x_910;
}
}
else
{
lean_object* x_911; lean_object* x_912; 
lean_dec(x_824);
lean_dec(x_820);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_911 = lean_ctor_get(x_825, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_825, 1);
lean_inc(x_912);
lean_dec(x_825);
x_8 = x_911;
x_9 = x_912;
goto block_16;
}
}
else
{
lean_object* x_913; lean_object* x_914; 
lean_dec(x_820);
lean_dec(x_51);
lean_dec(x_815);
lean_dec(x_800);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_913 = lean_ctor_get(x_821, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_821, 1);
lean_inc(x_914);
lean_dec(x_821);
x_8 = x_913;
x_9 = x_914;
goto block_16;
}
}
else
{
lean_object* x_915; lean_object* x_916; 
lean_dec(x_808);
lean_dec(x_806);
lean_dec(x_804);
lean_dec(x_802);
lean_dec(x_800);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_915 = lean_ctor_get(x_809, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_809, 1);
lean_inc(x_916);
lean_dec(x_809);
x_8 = x_915;
x_9 = x_916;
goto block_16;
}
}
else
{
lean_object* x_917; lean_object* x_918; 
lean_dec(x_804);
lean_dec(x_802);
lean_dec(x_800);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_917 = lean_ctor_get(x_805, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_805, 1);
lean_inc(x_918);
lean_dec(x_805);
x_8 = x_917;
x_9 = x_918;
goto block_16;
}
}
else
{
lean_object* x_919; lean_object* x_920; 
lean_dec(x_800);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_919 = lean_ctor_get(x_801, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_801, 1);
lean_inc(x_920);
lean_dec(x_801);
x_8 = x_919;
x_9 = x_920;
goto block_16;
}
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
lean_dec(x_798);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_921 = lean_ctor_get(x_797, 1);
lean_inc(x_921);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_922 = x_797;
} else {
 lean_dec_ref(x_797);
 x_922 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_923 = lean_alloc_ctor(0, 2, 0);
} else {
 x_923 = x_922;
}
lean_ctor_set(x_923, 0, x_796);
lean_ctor_set(x_923, 1, x_921);
return x_923;
}
}
else
{
lean_object* x_924; lean_object* x_925; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_924 = lean_ctor_get(x_797, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_797, 1);
lean_inc(x_925);
lean_dec(x_797);
x_8 = x_924;
x_9 = x_925;
goto block_16;
}
}
}
else
{
lean_object* x_926; lean_object* x_927; 
lean_free_object(x_109);
lean_dec(x_111);
lean_free_object(x_94);
lean_free_object(x_90);
lean_dec(x_92);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_926 = lean_ctor_get(x_113, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_113, 1);
lean_inc(x_927);
lean_dec(x_113);
x_8 = x_926;
x_9 = x_927;
goto block_16;
}
}
else
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_928 = lean_ctor_get(x_109, 0);
x_929 = lean_ctor_get(x_109, 1);
lean_inc(x_929);
lean_inc(x_928);
lean_dec(x_109);
x_930 = l_Lean_Meta_decLevel(x_89, x_3, x_4, x_5, x_6, x_929);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_930)) {
 lean_ctor_release(x_930, 0);
 lean_ctor_release(x_930, 1);
 x_933 = x_930;
} else {
 lean_dec_ref(x_930);
 x_933 = lean_box(0);
}
x_934 = lean_box(0);
if (lean_is_scalar(x_933)) {
 x_935 = lean_alloc_ctor(1, 2, 0);
} else {
 x_935 = x_933;
 lean_ctor_set_tag(x_935, 1);
}
lean_ctor_set(x_935, 0, x_931);
lean_ctor_set(x_935, 1, x_934);
x_936 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_936, 0, x_928);
lean_ctor_set(x_936, 1, x_935);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 1, x_936);
lean_ctor_set(x_94, 0, x_92);
x_937 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_938 = l_Lean_Expr_const___override(x_937, x_94);
lean_inc(x_40);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 1, x_934);
lean_ctor_set(x_90, 0, x_40);
lean_inc(x_54);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_90);
lean_ctor_set(x_56, 0, x_54);
x_939 = lean_array_mk(x_56);
x_940 = l_Lean_mkAppN(x_938, x_939);
lean_dec(x_939);
x_941 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_942 = l_Lean_Meta_trySynthInstance(x_940, x_941, x_3, x_4, x_5, x_6, x_932);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; 
x_943 = lean_ctor_get(x_942, 0);
lean_inc(x_943);
if (lean_obj_tag(x_943) == 1)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_944 = lean_ctor_get(x_942, 1);
lean_inc(x_944);
lean_dec(x_942);
x_945 = lean_ctor_get(x_943, 0);
lean_inc(x_945);
lean_dec(x_943);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_946 = l_Lean_Meta_getDecLevel(x_55, x_3, x_4, x_5, x_6, x_944);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_946, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_946)) {
 lean_ctor_release(x_946, 0);
 lean_ctor_release(x_946, 1);
 x_949 = x_946;
} else {
 lean_dec_ref(x_946);
 x_949 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_950 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_948);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_953 = x_950;
} else {
 lean_dec_ref(x_950);
 x_953 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_954 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_952);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_957 = x_954;
} else {
 lean_dec_ref(x_954);
 x_957 = lean_box(0);
}
if (lean_is_scalar(x_957)) {
 x_958 = lean_alloc_ctor(1, 2, 0);
} else {
 x_958 = x_957;
 lean_ctor_set_tag(x_958, 1);
}
lean_ctor_set(x_958, 0, x_955);
lean_ctor_set(x_958, 1, x_934);
if (lean_is_scalar(x_953)) {
 x_959 = lean_alloc_ctor(1, 2, 0);
} else {
 x_959 = x_953;
 lean_ctor_set_tag(x_959, 1);
}
lean_ctor_set(x_959, 0, x_951);
lean_ctor_set(x_959, 1, x_958);
if (lean_is_scalar(x_949)) {
 x_960 = lean_alloc_ctor(1, 2, 0);
} else {
 x_960 = x_949;
 lean_ctor_set_tag(x_960, 1);
}
lean_ctor_set(x_960, 0, x_947);
lean_ctor_set(x_960, 1, x_959);
x_961 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_960);
x_962 = l_Lean_Expr_const___override(x_961, x_960);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_934);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_945);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_945);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_963 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_963, 0, x_54);
lean_ctor_set(x_963, 1, x_17);
x_964 = lean_array_mk(x_963);
x_965 = l_Lean_mkAppN(x_962, x_964);
lean_dec(x_964);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_965);
x_966 = lean_infer_type(x_965, x_3, x_4, x_5, x_6, x_956);
if (lean_obj_tag(x_966) == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_967 = lean_ctor_get(x_966, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_966, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 lean_ctor_release(x_966, 1);
 x_969 = x_966;
} else {
 lean_dec_ref(x_966);
 x_969 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_970 = l_Lean_Meta_isExprDefEq(x_19, x_967, x_3, x_4, x_5, x_6, x_968);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; uint8_t x_972; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_unbox(x_971);
lean_dec(x_971);
if (x_972 == 0)
{
lean_object* x_973; lean_object* x_974; 
lean_dec(x_965);
lean_free_object(x_43);
x_973 = lean_ctor_get(x_970, 1);
lean_inc(x_973);
lean_dec(x_970);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_974 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_973);
if (lean_obj_tag(x_974) == 0)
{
lean_object* x_975; 
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; 
lean_dec(x_969);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_977 = x_974;
} else {
 lean_dec_ref(x_974);
 x_977 = lean_box(0);
}
if (lean_is_scalar(x_977)) {
 x_978 = lean_alloc_ctor(0, 2, 0);
} else {
 x_978 = x_977;
}
lean_ctor_set(x_978, 0, x_941);
lean_ctor_set(x_978, 1, x_976);
return x_978;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_979 = lean_ctor_get(x_974, 1);
lean_inc(x_979);
lean_dec(x_974);
x_980 = lean_ctor_get(x_975, 0);
lean_inc(x_980);
lean_dec(x_975);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_981 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_979);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_984 = x_981;
} else {
 lean_dec_ref(x_981);
 x_984 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_985 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_983);
if (lean_obj_tag(x_985) == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; uint8_t x_1000; lean_object* x_1001; lean_object* x_1002; 
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_985)) {
 lean_ctor_release(x_985, 0);
 lean_ctor_release(x_985, 1);
 x_988 = x_985;
} else {
 lean_dec_ref(x_985);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_989 = x_988;
 lean_ctor_set_tag(x_989, 1);
}
lean_ctor_set(x_989, 0, x_986);
lean_ctor_set(x_989, 1, x_934);
if (lean_is_scalar(x_984)) {
 x_990 = lean_alloc_ctor(1, 2, 0);
} else {
 x_990 = x_984;
 lean_ctor_set_tag(x_990, 1);
}
lean_ctor_set(x_990, 0, x_982);
lean_ctor_set(x_990, 1, x_989);
x_991 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_992 = l_Lean_Expr_const___override(x_991, x_990);
lean_inc(x_41);
if (lean_is_scalar(x_969)) {
 x_993 = lean_alloc_ctor(1, 2, 0);
} else {
 x_993 = x_969;
 lean_ctor_set_tag(x_993, 1);
}
lean_ctor_set(x_993, 0, x_41);
lean_ctor_set(x_993, 1, x_934);
x_994 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_995 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_995, 0, x_994);
lean_ctor_set(x_995, 1, x_993);
lean_inc(x_55);
x_996 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_996, 0, x_55);
lean_ctor_set(x_996, 1, x_995);
x_997 = lean_array_mk(x_996);
x_998 = l_Lean_mkAppN(x_992, x_997);
lean_dec(x_997);
x_999 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1000 = 0;
lean_inc(x_55);
x_1001 = l_Lean_Expr_forallE___override(x_999, x_55, x_998, x_1000);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1002 = l_Lean_Meta_trySynthInstance(x_1001, x_941, x_3, x_4, x_5, x_6, x_987);
if (lean_obj_tag(x_1002) == 0)
{
lean_object* x_1003; 
x_1003 = lean_ctor_get(x_1002, 0);
lean_inc(x_1003);
if (lean_obj_tag(x_1003) == 1)
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1004 = lean_ctor_get(x_1002, 1);
lean_inc(x_1004);
lean_dec(x_1002);
x_1005 = lean_ctor_get(x_1003, 0);
lean_inc(x_1005);
lean_dec(x_1003);
x_1006 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1007 = l_Lean_Expr_const___override(x_1006, x_960);
x_1008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1008, 0, x_980);
lean_ctor_set(x_1008, 1, x_51);
x_1009 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1009, 0, x_1005);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1010, 0, x_945);
lean_ctor_set(x_1010, 1, x_1009);
x_1011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1011, 0, x_41);
lean_ctor_set(x_1011, 1, x_1010);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_55);
lean_ctor_set(x_1012, 1, x_1011);
x_1013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1013, 0, x_40);
lean_ctor_set(x_1013, 1, x_1012);
x_1014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1014, 0, x_54);
lean_ctor_set(x_1014, 1, x_1013);
x_1015 = lean_array_mk(x_1014);
x_1016 = l_Lean_mkAppN(x_1007, x_1015);
lean_dec(x_1015);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1017 = l_Lean_Meta_expandCoe(x_1016, x_3, x_4, x_5, x_6, x_1004);
if (lean_obj_tag(x_1017) == 0)
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1017, 1);
lean_inc(x_1019);
lean_dec(x_1017);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1018);
x_1020 = lean_infer_type(x_1018, x_3, x_4, x_5, x_6, x_1019);
if (lean_obj_tag(x_1020) == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1021 = lean_ctor_get(x_1020, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1020, 1);
lean_inc(x_1022);
lean_dec(x_1020);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1023 = l_Lean_Meta_isExprDefEq(x_19, x_1021, x_3, x_4, x_5, x_6, x_1022);
if (lean_obj_tag(x_1023) == 0)
{
lean_object* x_1024; uint8_t x_1025; 
x_1024 = lean_ctor_get(x_1023, 0);
lean_inc(x_1024);
x_1025 = lean_unbox(x_1024);
lean_dec(x_1024);
if (x_1025 == 0)
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
lean_dec(x_1018);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1026 = lean_ctor_get(x_1023, 1);
lean_inc(x_1026);
if (lean_is_exclusive(x_1023)) {
 lean_ctor_release(x_1023, 0);
 lean_ctor_release(x_1023, 1);
 x_1027 = x_1023;
} else {
 lean_dec_ref(x_1023);
 x_1027 = lean_box(0);
}
if (lean_is_scalar(x_1027)) {
 x_1028 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1028 = x_1027;
}
lean_ctor_set(x_1028, 0, x_941);
lean_ctor_set(x_1028, 1, x_1026);
return x_1028;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1029 = lean_ctor_get(x_1023, 1);
lean_inc(x_1029);
lean_dec(x_1023);
x_1030 = lean_box(0);
x_1031 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1018, x_1030, x_3, x_4, x_5, x_6, x_1029);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1034 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1034 = lean_box(0);
}
if (lean_is_scalar(x_1034)) {
 x_1035 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1035 = x_1034;
}
lean_ctor_set(x_1035, 0, x_1032);
lean_ctor_set(x_1035, 1, x_1033);
return x_1035;
}
}
else
{
lean_object* x_1036; lean_object* x_1037; 
lean_dec(x_1018);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1036 = lean_ctor_get(x_1023, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1023, 1);
lean_inc(x_1037);
lean_dec(x_1023);
x_8 = x_1036;
x_9 = x_1037;
goto block_16;
}
}
else
{
lean_object* x_1038; lean_object* x_1039; 
lean_dec(x_1018);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1038 = lean_ctor_get(x_1020, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1020, 1);
lean_inc(x_1039);
lean_dec(x_1020);
x_8 = x_1038;
x_9 = x_1039;
goto block_16;
}
}
else
{
lean_object* x_1040; lean_object* x_1041; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1040 = lean_ctor_get(x_1017, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1017, 1);
lean_inc(x_1041);
lean_dec(x_1017);
x_8 = x_1040;
x_9 = x_1041;
goto block_16;
}
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_1003);
lean_dec(x_980);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1042 = lean_ctor_get(x_1002, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_1002)) {
 lean_ctor_release(x_1002, 0);
 lean_ctor_release(x_1002, 1);
 x_1043 = x_1002;
} else {
 lean_dec_ref(x_1002);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1043)) {
 x_1044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1044 = x_1043;
}
lean_ctor_set(x_1044, 0, x_941);
lean_ctor_set(x_1044, 1, x_1042);
return x_1044;
}
}
else
{
lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_980);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1045 = lean_ctor_get(x_1002, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1002, 1);
lean_inc(x_1046);
lean_dec(x_1002);
x_8 = x_1045;
x_9 = x_1046;
goto block_16;
}
}
else
{
lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_984);
lean_dec(x_982);
lean_dec(x_980);
lean_dec(x_969);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1047 = lean_ctor_get(x_985, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_985, 1);
lean_inc(x_1048);
lean_dec(x_985);
x_8 = x_1047;
x_9 = x_1048;
goto block_16;
}
}
else
{
lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_980);
lean_dec(x_969);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1049 = lean_ctor_get(x_981, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_981, 1);
lean_inc(x_1050);
lean_dec(x_981);
x_8 = x_1049;
x_9 = x_1050;
goto block_16;
}
}
}
else
{
lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_969);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1051 = lean_ctor_get(x_974, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_974, 1);
lean_inc(x_1052);
lean_dec(x_974);
x_8 = x_1051;
x_9 = x_1052;
goto block_16;
}
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_969);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1053 = lean_ctor_get(x_970, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 lean_ctor_release(x_970, 1);
 x_1054 = x_970;
} else {
 lean_dec_ref(x_970);
 x_1054 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_965);
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_43);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_969);
lean_dec(x_965);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1056 = lean_ctor_get(x_970, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_970, 1);
lean_inc(x_1057);
lean_dec(x_970);
x_8 = x_1056;
x_9 = x_1057;
goto block_16;
}
}
else
{
lean_object* x_1058; lean_object* x_1059; 
lean_dec(x_965);
lean_dec(x_51);
lean_dec(x_960);
lean_dec(x_945);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1058 = lean_ctor_get(x_966, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_966, 1);
lean_inc(x_1059);
lean_dec(x_966);
x_8 = x_1058;
x_9 = x_1059;
goto block_16;
}
}
else
{
lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_953);
lean_dec(x_951);
lean_dec(x_949);
lean_dec(x_947);
lean_dec(x_945);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1060 = lean_ctor_get(x_954, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_954, 1);
lean_inc(x_1061);
lean_dec(x_954);
x_8 = x_1060;
x_9 = x_1061;
goto block_16;
}
}
else
{
lean_object* x_1062; lean_object* x_1063; 
lean_dec(x_949);
lean_dec(x_947);
lean_dec(x_945);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1062 = lean_ctor_get(x_950, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_950, 1);
lean_inc(x_1063);
lean_dec(x_950);
x_8 = x_1062;
x_9 = x_1063;
goto block_16;
}
}
else
{
lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_945);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1064 = lean_ctor_get(x_946, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_946, 1);
lean_inc(x_1065);
lean_dec(x_946);
x_8 = x_1064;
x_9 = x_1065;
goto block_16;
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_943);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1066 = lean_ctor_get(x_942, 1);
lean_inc(x_1066);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_1067 = x_942;
} else {
 lean_dec_ref(x_942);
 x_1067 = lean_box(0);
}
if (lean_is_scalar(x_1067)) {
 x_1068 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1068 = x_1067;
}
lean_ctor_set(x_1068, 0, x_941);
lean_ctor_set(x_1068, 1, x_1066);
return x_1068;
}
}
else
{
lean_object* x_1069; lean_object* x_1070; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1069 = lean_ctor_get(x_942, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_942, 1);
lean_inc(x_1070);
lean_dec(x_942);
x_8 = x_1069;
x_9 = x_1070;
goto block_16;
}
}
else
{
lean_object* x_1071; lean_object* x_1072; 
lean_dec(x_928);
lean_free_object(x_94);
lean_free_object(x_90);
lean_dec(x_92);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1071 = lean_ctor_get(x_930, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_930, 1);
lean_inc(x_1072);
lean_dec(x_930);
x_8 = x_1071;
x_9 = x_1072;
goto block_16;
}
}
}
else
{
lean_object* x_1073; lean_object* x_1074; 
lean_free_object(x_94);
lean_free_object(x_90);
lean_dec(x_92);
lean_dec(x_89);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1073 = lean_ctor_get(x_109, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_109, 1);
lean_inc(x_1074);
lean_dec(x_109);
x_8 = x_1073;
x_9 = x_1074;
goto block_16;
}
}
}
else
{
lean_object* x_1075; lean_object* x_1076; 
lean_free_object(x_94);
lean_free_object(x_90);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1075 = lean_ctor_get(x_99, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_99, 1);
lean_inc(x_1076);
lean_dec(x_99);
x_8 = x_1075;
x_9 = x_1076;
goto block_16;
}
}
else
{
lean_object* x_1077; lean_object* x_1078; uint8_t x_1079; lean_object* x_1080; 
x_1077 = lean_ctor_get(x_94, 0);
x_1078 = lean_ctor_get(x_94, 1);
lean_inc(x_1078);
lean_inc(x_1077);
lean_dec(x_94);
x_1079 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_92);
x_1080 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_92, x_1077, x_1079, x_3, x_4, x_5, x_6, x_1078);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; uint8_t x_1082; 
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_unbox(x_1081);
lean_dec(x_1081);
if (x_1082 == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
lean_free_object(x_90);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1083 = lean_ctor_get(x_1080, 1);
lean_inc(x_1083);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 lean_ctor_release(x_1080, 1);
 x_1084 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1084 = lean_box(0);
}
x_1085 = lean_box(0);
if (lean_is_scalar(x_1084)) {
 x_1086 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1086 = x_1084;
}
lean_ctor_set(x_1086, 0, x_1085);
lean_ctor_set(x_1086, 1, x_1083);
return x_1086;
}
else
{
lean_object* x_1087; lean_object* x_1088; 
x_1087 = lean_ctor_get(x_1080, 1);
lean_inc(x_1087);
lean_dec(x_1080);
x_1088 = l_Lean_Meta_decLevel(x_79, x_3, x_4, x_5, x_6, x_1087);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1091 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1091 = lean_box(0);
}
x_1092 = l_Lean_Meta_decLevel(x_89, x_3, x_4, x_5, x_6, x_1090);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1092, 1);
lean_inc(x_1094);
if (lean_is_exclusive(x_1092)) {
 lean_ctor_release(x_1092, 0);
 lean_ctor_release(x_1092, 1);
 x_1095 = x_1092;
} else {
 lean_dec_ref(x_1092);
 x_1095 = lean_box(0);
}
x_1096 = lean_box(0);
if (lean_is_scalar(x_1095)) {
 x_1097 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1097 = x_1095;
 lean_ctor_set_tag(x_1097, 1);
}
lean_ctor_set(x_1097, 0, x_1093);
lean_ctor_set(x_1097, 1, x_1096);
if (lean_is_scalar(x_1091)) {
 x_1098 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1098 = x_1091;
 lean_ctor_set_tag(x_1098, 1);
}
lean_ctor_set(x_1098, 0, x_1089);
lean_ctor_set(x_1098, 1, x_1097);
x_1099 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1099, 0, x_92);
lean_ctor_set(x_1099, 1, x_1098);
x_1100 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1101 = l_Lean_Expr_const___override(x_1100, x_1099);
lean_inc(x_40);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 1, x_1096);
lean_ctor_set(x_90, 0, x_40);
lean_inc(x_54);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_90);
lean_ctor_set(x_56, 0, x_54);
x_1102 = lean_array_mk(x_56);
x_1103 = l_Lean_mkAppN(x_1101, x_1102);
lean_dec(x_1102);
x_1104 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1105 = l_Lean_Meta_trySynthInstance(x_1103, x_1104, x_3, x_4, x_5, x_6, x_1094);
if (lean_obj_tag(x_1105) == 0)
{
lean_object* x_1106; 
x_1106 = lean_ctor_get(x_1105, 0);
lean_inc(x_1106);
if (lean_obj_tag(x_1106) == 1)
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1105, 1);
lean_inc(x_1107);
lean_dec(x_1105);
x_1108 = lean_ctor_get(x_1106, 0);
lean_inc(x_1108);
lean_dec(x_1106);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1109 = l_Lean_Meta_getDecLevel(x_55, x_3, x_4, x_5, x_6, x_1107);
if (lean_obj_tag(x_1109) == 0)
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
x_1110 = lean_ctor_get(x_1109, 0);
lean_inc(x_1110);
x_1111 = lean_ctor_get(x_1109, 1);
lean_inc(x_1111);
if (lean_is_exclusive(x_1109)) {
 lean_ctor_release(x_1109, 0);
 lean_ctor_release(x_1109, 1);
 x_1112 = x_1109;
} else {
 lean_dec_ref(x_1109);
 x_1112 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1113 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_1111);
if (lean_obj_tag(x_1113) == 0)
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1114 = lean_ctor_get(x_1113, 0);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1113, 1);
lean_inc(x_1115);
if (lean_is_exclusive(x_1113)) {
 lean_ctor_release(x_1113, 0);
 lean_ctor_release(x_1113, 1);
 x_1116 = x_1113;
} else {
 lean_dec_ref(x_1113);
 x_1116 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_1117 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_1115);
if (lean_obj_tag(x_1117) == 0)
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1118 = lean_ctor_get(x_1117, 0);
lean_inc(x_1118);
x_1119 = lean_ctor_get(x_1117, 1);
lean_inc(x_1119);
if (lean_is_exclusive(x_1117)) {
 lean_ctor_release(x_1117, 0);
 lean_ctor_release(x_1117, 1);
 x_1120 = x_1117;
} else {
 lean_dec_ref(x_1117);
 x_1120 = lean_box(0);
}
if (lean_is_scalar(x_1120)) {
 x_1121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1121 = x_1120;
 lean_ctor_set_tag(x_1121, 1);
}
lean_ctor_set(x_1121, 0, x_1118);
lean_ctor_set(x_1121, 1, x_1096);
if (lean_is_scalar(x_1116)) {
 x_1122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1122 = x_1116;
 lean_ctor_set_tag(x_1122, 1);
}
lean_ctor_set(x_1122, 0, x_1114);
lean_ctor_set(x_1122, 1, x_1121);
if (lean_is_scalar(x_1112)) {
 x_1123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1123 = x_1112;
 lean_ctor_set_tag(x_1123, 1);
}
lean_ctor_set(x_1123, 0, x_1110);
lean_ctor_set(x_1123, 1, x_1122);
x_1124 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_1123);
x_1125 = l_Lean_Expr_const___override(x_1124, x_1123);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_1096);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_1108);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_1108);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_1126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1126, 0, x_54);
lean_ctor_set(x_1126, 1, x_17);
x_1127 = lean_array_mk(x_1126);
x_1128 = l_Lean_mkAppN(x_1125, x_1127);
lean_dec(x_1127);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1128);
x_1129 = lean_infer_type(x_1128, x_3, x_4, x_5, x_6, x_1119);
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
lean_inc(x_19);
x_1133 = l_Lean_Meta_isExprDefEq(x_19, x_1130, x_3, x_4, x_5, x_6, x_1131);
if (lean_obj_tag(x_1133) == 0)
{
lean_object* x_1134; uint8_t x_1135; 
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
x_1135 = lean_unbox(x_1134);
lean_dec(x_1134);
if (x_1135 == 0)
{
lean_object* x_1136; lean_object* x_1137; 
lean_dec(x_1128);
lean_free_object(x_43);
x_1136 = lean_ctor_get(x_1133, 1);
lean_inc(x_1136);
lean_dec(x_1133);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_1137 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_1136);
if (lean_obj_tag(x_1137) == 0)
{
lean_object* x_1138; 
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
if (lean_obj_tag(x_1138) == 0)
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
lean_dec(x_1132);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 lean_ctor_release(x_1137, 1);
 x_1140 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1140 = lean_box(0);
}
if (lean_is_scalar(x_1140)) {
 x_1141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1141 = x_1140;
}
lean_ctor_set(x_1141, 0, x_1104);
lean_ctor_set(x_1141, 1, x_1139);
return x_1141;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1142 = lean_ctor_get(x_1137, 1);
lean_inc(x_1142);
lean_dec(x_1137);
x_1143 = lean_ctor_get(x_1138, 0);
lean_inc(x_1143);
lean_dec(x_1138);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1144 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_1142);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
if (lean_is_exclusive(x_1144)) {
 lean_ctor_release(x_1144, 0);
 lean_ctor_release(x_1144, 1);
 x_1147 = x_1144;
} else {
 lean_dec_ref(x_1144);
 x_1147 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_1148 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_1146);
if (lean_obj_tag(x_1148) == 0)
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; uint8_t x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1149 = lean_ctor_get(x_1148, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1148, 1);
lean_inc(x_1150);
if (lean_is_exclusive(x_1148)) {
 lean_ctor_release(x_1148, 0);
 lean_ctor_release(x_1148, 1);
 x_1151 = x_1148;
} else {
 lean_dec_ref(x_1148);
 x_1151 = lean_box(0);
}
if (lean_is_scalar(x_1151)) {
 x_1152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1152 = x_1151;
 lean_ctor_set_tag(x_1152, 1);
}
lean_ctor_set(x_1152, 0, x_1149);
lean_ctor_set(x_1152, 1, x_1096);
if (lean_is_scalar(x_1147)) {
 x_1153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1153 = x_1147;
 lean_ctor_set_tag(x_1153, 1);
}
lean_ctor_set(x_1153, 0, x_1145);
lean_ctor_set(x_1153, 1, x_1152);
x_1154 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1155 = l_Lean_Expr_const___override(x_1154, x_1153);
lean_inc(x_41);
if (lean_is_scalar(x_1132)) {
 x_1156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1156 = x_1132;
 lean_ctor_set_tag(x_1156, 1);
}
lean_ctor_set(x_1156, 0, x_41);
lean_ctor_set(x_1156, 1, x_1096);
x_1157 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1158, 0, x_1157);
lean_ctor_set(x_1158, 1, x_1156);
lean_inc(x_55);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_55);
lean_ctor_set(x_1159, 1, x_1158);
x_1160 = lean_array_mk(x_1159);
x_1161 = l_Lean_mkAppN(x_1155, x_1160);
lean_dec(x_1160);
x_1162 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1163 = 0;
lean_inc(x_55);
x_1164 = l_Lean_Expr_forallE___override(x_1162, x_55, x_1161, x_1163);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1165 = l_Lean_Meta_trySynthInstance(x_1164, x_1104, x_3, x_4, x_5, x_6, x_1150);
if (lean_obj_tag(x_1165) == 0)
{
lean_object* x_1166; 
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
if (lean_obj_tag(x_1166) == 1)
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
x_1168 = lean_ctor_get(x_1166, 0);
lean_inc(x_1168);
lean_dec(x_1166);
x_1169 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1170 = l_Lean_Expr_const___override(x_1169, x_1123);
x_1171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1171, 0, x_1143);
lean_ctor_set(x_1171, 1, x_51);
x_1172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1172, 0, x_1168);
lean_ctor_set(x_1172, 1, x_1171);
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1108);
lean_ctor_set(x_1173, 1, x_1172);
x_1174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1174, 0, x_41);
lean_ctor_set(x_1174, 1, x_1173);
x_1175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1175, 0, x_55);
lean_ctor_set(x_1175, 1, x_1174);
x_1176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1176, 0, x_40);
lean_ctor_set(x_1176, 1, x_1175);
x_1177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1177, 0, x_54);
lean_ctor_set(x_1177, 1, x_1176);
x_1178 = lean_array_mk(x_1177);
x_1179 = l_Lean_mkAppN(x_1170, x_1178);
lean_dec(x_1178);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1180 = l_Lean_Meta_expandCoe(x_1179, x_3, x_4, x_5, x_6, x_1167);
if (lean_obj_tag(x_1180) == 0)
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1181 = lean_ctor_get(x_1180, 0);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1180, 1);
lean_inc(x_1182);
lean_dec(x_1180);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1181);
x_1183 = lean_infer_type(x_1181, x_3, x_4, x_5, x_6, x_1182);
if (lean_obj_tag(x_1183) == 0)
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1183, 0);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_1183, 1);
lean_inc(x_1185);
lean_dec(x_1183);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1186 = l_Lean_Meta_isExprDefEq(x_19, x_1184, x_3, x_4, x_5, x_6, x_1185);
if (lean_obj_tag(x_1186) == 0)
{
lean_object* x_1187; uint8_t x_1188; 
x_1187 = lean_ctor_get(x_1186, 0);
lean_inc(x_1187);
x_1188 = lean_unbox(x_1187);
lean_dec(x_1187);
if (x_1188 == 0)
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
lean_dec(x_1181);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1189 = lean_ctor_get(x_1186, 1);
lean_inc(x_1189);
if (lean_is_exclusive(x_1186)) {
 lean_ctor_release(x_1186, 0);
 lean_ctor_release(x_1186, 1);
 x_1190 = x_1186;
} else {
 lean_dec_ref(x_1186);
 x_1190 = lean_box(0);
}
if (lean_is_scalar(x_1190)) {
 x_1191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1191 = x_1190;
}
lean_ctor_set(x_1191, 0, x_1104);
lean_ctor_set(x_1191, 1, x_1189);
return x_1191;
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
x_1192 = lean_ctor_get(x_1186, 1);
lean_inc(x_1192);
lean_dec(x_1186);
x_1193 = lean_box(0);
x_1194 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1181, x_1193, x_3, x_4, x_5, x_6, x_1192);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1195 = lean_ctor_get(x_1194, 0);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1194, 1);
lean_inc(x_1196);
if (lean_is_exclusive(x_1194)) {
 lean_ctor_release(x_1194, 0);
 lean_ctor_release(x_1194, 1);
 x_1197 = x_1194;
} else {
 lean_dec_ref(x_1194);
 x_1197 = lean_box(0);
}
if (lean_is_scalar(x_1197)) {
 x_1198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1198 = x_1197;
}
lean_ctor_set(x_1198, 0, x_1195);
lean_ctor_set(x_1198, 1, x_1196);
return x_1198;
}
}
else
{
lean_object* x_1199; lean_object* x_1200; 
lean_dec(x_1181);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1199 = lean_ctor_get(x_1186, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1186, 1);
lean_inc(x_1200);
lean_dec(x_1186);
x_8 = x_1199;
x_9 = x_1200;
goto block_16;
}
}
else
{
lean_object* x_1201; lean_object* x_1202; 
lean_dec(x_1181);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1201 = lean_ctor_get(x_1183, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1183, 1);
lean_inc(x_1202);
lean_dec(x_1183);
x_8 = x_1201;
x_9 = x_1202;
goto block_16;
}
}
else
{
lean_object* x_1203; lean_object* x_1204; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1203 = lean_ctor_get(x_1180, 0);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1180, 1);
lean_inc(x_1204);
lean_dec(x_1180);
x_8 = x_1203;
x_9 = x_1204;
goto block_16;
}
}
else
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
lean_dec(x_1166);
lean_dec(x_1143);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1205 = lean_ctor_get(x_1165, 1);
lean_inc(x_1205);
if (lean_is_exclusive(x_1165)) {
 lean_ctor_release(x_1165, 0);
 lean_ctor_release(x_1165, 1);
 x_1206 = x_1165;
} else {
 lean_dec_ref(x_1165);
 x_1206 = lean_box(0);
}
if (lean_is_scalar(x_1206)) {
 x_1207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1207 = x_1206;
}
lean_ctor_set(x_1207, 0, x_1104);
lean_ctor_set(x_1207, 1, x_1205);
return x_1207;
}
}
else
{
lean_object* x_1208; lean_object* x_1209; 
lean_dec(x_1143);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1208 = lean_ctor_get(x_1165, 0);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_1165, 1);
lean_inc(x_1209);
lean_dec(x_1165);
x_8 = x_1208;
x_9 = x_1209;
goto block_16;
}
}
else
{
lean_object* x_1210; lean_object* x_1211; 
lean_dec(x_1147);
lean_dec(x_1145);
lean_dec(x_1143);
lean_dec(x_1132);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1210 = lean_ctor_get(x_1148, 0);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1148, 1);
lean_inc(x_1211);
lean_dec(x_1148);
x_8 = x_1210;
x_9 = x_1211;
goto block_16;
}
}
else
{
lean_object* x_1212; lean_object* x_1213; 
lean_dec(x_1143);
lean_dec(x_1132);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1212 = lean_ctor_get(x_1144, 0);
lean_inc(x_1212);
x_1213 = lean_ctor_get(x_1144, 1);
lean_inc(x_1213);
lean_dec(x_1144);
x_8 = x_1212;
x_9 = x_1213;
goto block_16;
}
}
}
else
{
lean_object* x_1214; lean_object* x_1215; 
lean_dec(x_1132);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1214 = lean_ctor_get(x_1137, 0);
lean_inc(x_1214);
x_1215 = lean_ctor_get(x_1137, 1);
lean_inc(x_1215);
lean_dec(x_1137);
x_8 = x_1214;
x_9 = x_1215;
goto block_16;
}
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
lean_dec(x_1132);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1216 = lean_ctor_get(x_1133, 1);
lean_inc(x_1216);
if (lean_is_exclusive(x_1133)) {
 lean_ctor_release(x_1133, 0);
 lean_ctor_release(x_1133, 1);
 x_1217 = x_1133;
} else {
 lean_dec_ref(x_1133);
 x_1217 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_1128);
if (lean_is_scalar(x_1217)) {
 x_1218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1218 = x_1217;
}
lean_ctor_set(x_1218, 0, x_43);
lean_ctor_set(x_1218, 1, x_1216);
return x_1218;
}
}
else
{
lean_object* x_1219; lean_object* x_1220; 
lean_dec(x_1132);
lean_dec(x_1128);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1219 = lean_ctor_get(x_1133, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1133, 1);
lean_inc(x_1220);
lean_dec(x_1133);
x_8 = x_1219;
x_9 = x_1220;
goto block_16;
}
}
else
{
lean_object* x_1221; lean_object* x_1222; 
lean_dec(x_1128);
lean_dec(x_51);
lean_dec(x_1123);
lean_dec(x_1108);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1221 = lean_ctor_get(x_1129, 0);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1129, 1);
lean_inc(x_1222);
lean_dec(x_1129);
x_8 = x_1221;
x_9 = x_1222;
goto block_16;
}
}
else
{
lean_object* x_1223; lean_object* x_1224; 
lean_dec(x_1116);
lean_dec(x_1114);
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_1108);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1223 = lean_ctor_get(x_1117, 0);
lean_inc(x_1223);
x_1224 = lean_ctor_get(x_1117, 1);
lean_inc(x_1224);
lean_dec(x_1117);
x_8 = x_1223;
x_9 = x_1224;
goto block_16;
}
}
else
{
lean_object* x_1225; lean_object* x_1226; 
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_1108);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1225 = lean_ctor_get(x_1113, 0);
lean_inc(x_1225);
x_1226 = lean_ctor_get(x_1113, 1);
lean_inc(x_1226);
lean_dec(x_1113);
x_8 = x_1225;
x_9 = x_1226;
goto block_16;
}
}
else
{
lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1108);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1227 = lean_ctor_get(x_1109, 0);
lean_inc(x_1227);
x_1228 = lean_ctor_get(x_1109, 1);
lean_inc(x_1228);
lean_dec(x_1109);
x_8 = x_1227;
x_9 = x_1228;
goto block_16;
}
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
lean_dec(x_1106);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1229 = lean_ctor_get(x_1105, 1);
lean_inc(x_1229);
if (lean_is_exclusive(x_1105)) {
 lean_ctor_release(x_1105, 0);
 lean_ctor_release(x_1105, 1);
 x_1230 = x_1105;
} else {
 lean_dec_ref(x_1105);
 x_1230 = lean_box(0);
}
if (lean_is_scalar(x_1230)) {
 x_1231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1231 = x_1230;
}
lean_ctor_set(x_1231, 0, x_1104);
lean_ctor_set(x_1231, 1, x_1229);
return x_1231;
}
}
else
{
lean_object* x_1232; lean_object* x_1233; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1232 = lean_ctor_get(x_1105, 0);
lean_inc(x_1232);
x_1233 = lean_ctor_get(x_1105, 1);
lean_inc(x_1233);
lean_dec(x_1105);
x_8 = x_1232;
x_9 = x_1233;
goto block_16;
}
}
else
{
lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1091);
lean_dec(x_1089);
lean_free_object(x_90);
lean_dec(x_92);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1234 = lean_ctor_get(x_1092, 0);
lean_inc(x_1234);
x_1235 = lean_ctor_get(x_1092, 1);
lean_inc(x_1235);
lean_dec(x_1092);
x_8 = x_1234;
x_9 = x_1235;
goto block_16;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; 
lean_free_object(x_90);
lean_dec(x_92);
lean_dec(x_89);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1236 = lean_ctor_get(x_1088, 0);
lean_inc(x_1236);
x_1237 = lean_ctor_get(x_1088, 1);
lean_inc(x_1237);
lean_dec(x_1088);
x_8 = x_1236;
x_9 = x_1237;
goto block_16;
}
}
}
else
{
lean_object* x_1238; lean_object* x_1239; 
lean_free_object(x_90);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1238 = lean_ctor_get(x_1080, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1080, 1);
lean_inc(x_1239);
lean_dec(x_1080);
x_8 = x_1238;
x_9 = x_1239;
goto block_16;
}
}
}
else
{
lean_object* x_1240; lean_object* x_1241; 
lean_free_object(x_90);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1240 = lean_ctor_get(x_94, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_94, 1);
lean_inc(x_1241);
lean_dec(x_94);
x_8 = x_1240;
x_9 = x_1241;
goto block_16;
}
}
else
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
x_1242 = lean_ctor_get(x_90, 0);
x_1243 = lean_ctor_get(x_90, 1);
lean_inc(x_1243);
lean_inc(x_1242);
lean_dec(x_90);
x_1244 = l_Lean_Meta_decLevel(x_88, x_3, x_4, x_5, x_6, x_1243);
if (lean_obj_tag(x_1244) == 0)
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; uint8_t x_1248; lean_object* x_1249; 
x_1245 = lean_ctor_get(x_1244, 0);
lean_inc(x_1245);
x_1246 = lean_ctor_get(x_1244, 1);
lean_inc(x_1246);
if (lean_is_exclusive(x_1244)) {
 lean_ctor_release(x_1244, 0);
 lean_ctor_release(x_1244, 1);
 x_1247 = x_1244;
} else {
 lean_dec_ref(x_1244);
 x_1247 = lean_box(0);
}
x_1248 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1242);
x_1249 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1242, x_1245, x_1248, x_3, x_4, x_5, x_6, x_1246);
if (lean_obj_tag(x_1249) == 0)
{
lean_object* x_1250; uint8_t x_1251; 
x_1250 = lean_ctor_get(x_1249, 0);
lean_inc(x_1250);
x_1251 = lean_unbox(x_1250);
lean_dec(x_1250);
if (x_1251 == 0)
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
lean_dec(x_1247);
lean_dec(x_1242);
lean_dec(x_89);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1252 = lean_ctor_get(x_1249, 1);
lean_inc(x_1252);
if (lean_is_exclusive(x_1249)) {
 lean_ctor_release(x_1249, 0);
 lean_ctor_release(x_1249, 1);
 x_1253 = x_1249;
} else {
 lean_dec_ref(x_1249);
 x_1253 = lean_box(0);
}
x_1254 = lean_box(0);
if (lean_is_scalar(x_1253)) {
 x_1255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1255 = x_1253;
}
lean_ctor_set(x_1255, 0, x_1254);
lean_ctor_set(x_1255, 1, x_1252);
return x_1255;
}
else
{
lean_object* x_1256; lean_object* x_1257; 
x_1256 = lean_ctor_get(x_1249, 1);
lean_inc(x_1256);
lean_dec(x_1249);
x_1257 = l_Lean_Meta_decLevel(x_79, x_3, x_4, x_5, x_6, x_1256);
if (lean_obj_tag(x_1257) == 0)
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1258 = lean_ctor_get(x_1257, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1257, 1);
lean_inc(x_1259);
if (lean_is_exclusive(x_1257)) {
 lean_ctor_release(x_1257, 0);
 lean_ctor_release(x_1257, 1);
 x_1260 = x_1257;
} else {
 lean_dec_ref(x_1257);
 x_1260 = lean_box(0);
}
x_1261 = l_Lean_Meta_decLevel(x_89, x_3, x_4, x_5, x_6, x_1259);
if (lean_obj_tag(x_1261) == 0)
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
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
x_1265 = lean_box(0);
if (lean_is_scalar(x_1264)) {
 x_1266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1266 = x_1264;
 lean_ctor_set_tag(x_1266, 1);
}
lean_ctor_set(x_1266, 0, x_1262);
lean_ctor_set(x_1266, 1, x_1265);
if (lean_is_scalar(x_1260)) {
 x_1267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1267 = x_1260;
 lean_ctor_set_tag(x_1267, 1);
}
lean_ctor_set(x_1267, 0, x_1258);
lean_ctor_set(x_1267, 1, x_1266);
if (lean_is_scalar(x_1247)) {
 x_1268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1268 = x_1247;
 lean_ctor_set_tag(x_1268, 1);
}
lean_ctor_set(x_1268, 0, x_1242);
lean_ctor_set(x_1268, 1, x_1267);
x_1269 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1270 = l_Lean_Expr_const___override(x_1269, x_1268);
lean_inc(x_40);
x_1271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1271, 0, x_40);
lean_ctor_set(x_1271, 1, x_1265);
lean_inc(x_54);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_1271);
lean_ctor_set(x_56, 0, x_54);
x_1272 = lean_array_mk(x_56);
x_1273 = l_Lean_mkAppN(x_1270, x_1272);
lean_dec(x_1272);
x_1274 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1275 = l_Lean_Meta_trySynthInstance(x_1273, x_1274, x_3, x_4, x_5, x_6, x_1263);
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; 
x_1276 = lean_ctor_get(x_1275, 0);
lean_inc(x_1276);
if (lean_obj_tag(x_1276) == 1)
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
x_1277 = lean_ctor_get(x_1275, 1);
lean_inc(x_1277);
lean_dec(x_1275);
x_1278 = lean_ctor_get(x_1276, 0);
lean_inc(x_1278);
lean_dec(x_1276);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1279 = l_Lean_Meta_getDecLevel(x_55, x_3, x_4, x_5, x_6, x_1277);
if (lean_obj_tag(x_1279) == 0)
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
x_1280 = lean_ctor_get(x_1279, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1279, 1);
lean_inc(x_1281);
if (lean_is_exclusive(x_1279)) {
 lean_ctor_release(x_1279, 0);
 lean_ctor_release(x_1279, 1);
 x_1282 = x_1279;
} else {
 lean_dec_ref(x_1279);
 x_1282 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1283 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_1281);
if (lean_obj_tag(x_1283) == 0)
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1284 = lean_ctor_get(x_1283, 0);
lean_inc(x_1284);
x_1285 = lean_ctor_get(x_1283, 1);
lean_inc(x_1285);
if (lean_is_exclusive(x_1283)) {
 lean_ctor_release(x_1283, 0);
 lean_ctor_release(x_1283, 1);
 x_1286 = x_1283;
} else {
 lean_dec_ref(x_1283);
 x_1286 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_1287 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_1285);
if (lean_obj_tag(x_1287) == 0)
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
x_1288 = lean_ctor_get(x_1287, 0);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1287, 1);
lean_inc(x_1289);
if (lean_is_exclusive(x_1287)) {
 lean_ctor_release(x_1287, 0);
 lean_ctor_release(x_1287, 1);
 x_1290 = x_1287;
} else {
 lean_dec_ref(x_1287);
 x_1290 = lean_box(0);
}
if (lean_is_scalar(x_1290)) {
 x_1291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1291 = x_1290;
 lean_ctor_set_tag(x_1291, 1);
}
lean_ctor_set(x_1291, 0, x_1288);
lean_ctor_set(x_1291, 1, x_1265);
if (lean_is_scalar(x_1286)) {
 x_1292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1292 = x_1286;
 lean_ctor_set_tag(x_1292, 1);
}
lean_ctor_set(x_1292, 0, x_1284);
lean_ctor_set(x_1292, 1, x_1291);
if (lean_is_scalar(x_1282)) {
 x_1293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1293 = x_1282;
 lean_ctor_set_tag(x_1293, 1);
}
lean_ctor_set(x_1293, 0, x_1280);
lean_ctor_set(x_1293, 1, x_1292);
x_1294 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_1293);
x_1295 = l_Lean_Expr_const___override(x_1294, x_1293);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_1265);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_1278);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_1278);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_1296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1296, 0, x_54);
lean_ctor_set(x_1296, 1, x_17);
x_1297 = lean_array_mk(x_1296);
x_1298 = l_Lean_mkAppN(x_1295, x_1297);
lean_dec(x_1297);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1298);
x_1299 = lean_infer_type(x_1298, x_3, x_4, x_5, x_6, x_1289);
if (lean_obj_tag(x_1299) == 0)
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1300 = lean_ctor_get(x_1299, 0);
lean_inc(x_1300);
x_1301 = lean_ctor_get(x_1299, 1);
lean_inc(x_1301);
if (lean_is_exclusive(x_1299)) {
 lean_ctor_release(x_1299, 0);
 lean_ctor_release(x_1299, 1);
 x_1302 = x_1299;
} else {
 lean_dec_ref(x_1299);
 x_1302 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_1303 = l_Lean_Meta_isExprDefEq(x_19, x_1300, x_3, x_4, x_5, x_6, x_1301);
if (lean_obj_tag(x_1303) == 0)
{
lean_object* x_1304; uint8_t x_1305; 
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = lean_unbox(x_1304);
lean_dec(x_1304);
if (x_1305 == 0)
{
lean_object* x_1306; lean_object* x_1307; 
lean_dec(x_1298);
lean_free_object(x_43);
x_1306 = lean_ctor_get(x_1303, 1);
lean_inc(x_1306);
lean_dec(x_1303);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_1307 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_1306);
if (lean_obj_tag(x_1307) == 0)
{
lean_object* x_1308; 
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
if (lean_obj_tag(x_1308) == 0)
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
lean_dec(x_1302);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1309 = lean_ctor_get(x_1307, 1);
lean_inc(x_1309);
if (lean_is_exclusive(x_1307)) {
 lean_ctor_release(x_1307, 0);
 lean_ctor_release(x_1307, 1);
 x_1310 = x_1307;
} else {
 lean_dec_ref(x_1307);
 x_1310 = lean_box(0);
}
if (lean_is_scalar(x_1310)) {
 x_1311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1311 = x_1310;
}
lean_ctor_set(x_1311, 0, x_1274);
lean_ctor_set(x_1311, 1, x_1309);
return x_1311;
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1312 = lean_ctor_get(x_1307, 1);
lean_inc(x_1312);
lean_dec(x_1307);
x_1313 = lean_ctor_get(x_1308, 0);
lean_inc(x_1313);
lean_dec(x_1308);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1314 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_1312);
if (lean_obj_tag(x_1314) == 0)
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
x_1315 = lean_ctor_get(x_1314, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1314, 1);
lean_inc(x_1316);
if (lean_is_exclusive(x_1314)) {
 lean_ctor_release(x_1314, 0);
 lean_ctor_release(x_1314, 1);
 x_1317 = x_1314;
} else {
 lean_dec_ref(x_1314);
 x_1317 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_1318 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_1316);
if (lean_obj_tag(x_1318) == 0)
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; uint8_t x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1319 = lean_ctor_get(x_1318, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1318, 1);
lean_inc(x_1320);
if (lean_is_exclusive(x_1318)) {
 lean_ctor_release(x_1318, 0);
 lean_ctor_release(x_1318, 1);
 x_1321 = x_1318;
} else {
 lean_dec_ref(x_1318);
 x_1321 = lean_box(0);
}
if (lean_is_scalar(x_1321)) {
 x_1322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1322 = x_1321;
 lean_ctor_set_tag(x_1322, 1);
}
lean_ctor_set(x_1322, 0, x_1319);
lean_ctor_set(x_1322, 1, x_1265);
if (lean_is_scalar(x_1317)) {
 x_1323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1323 = x_1317;
 lean_ctor_set_tag(x_1323, 1);
}
lean_ctor_set(x_1323, 0, x_1315);
lean_ctor_set(x_1323, 1, x_1322);
x_1324 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1325 = l_Lean_Expr_const___override(x_1324, x_1323);
lean_inc(x_41);
if (lean_is_scalar(x_1302)) {
 x_1326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1326 = x_1302;
 lean_ctor_set_tag(x_1326, 1);
}
lean_ctor_set(x_1326, 0, x_41);
lean_ctor_set(x_1326, 1, x_1265);
x_1327 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1328, 0, x_1327);
lean_ctor_set(x_1328, 1, x_1326);
lean_inc(x_55);
x_1329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1329, 0, x_55);
lean_ctor_set(x_1329, 1, x_1328);
x_1330 = lean_array_mk(x_1329);
x_1331 = l_Lean_mkAppN(x_1325, x_1330);
lean_dec(x_1330);
x_1332 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1333 = 0;
lean_inc(x_55);
x_1334 = l_Lean_Expr_forallE___override(x_1332, x_55, x_1331, x_1333);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1335 = l_Lean_Meta_trySynthInstance(x_1334, x_1274, x_3, x_4, x_5, x_6, x_1320);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; 
x_1336 = lean_ctor_get(x_1335, 0);
lean_inc(x_1336);
if (lean_obj_tag(x_1336) == 1)
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1337 = lean_ctor_get(x_1335, 1);
lean_inc(x_1337);
lean_dec(x_1335);
x_1338 = lean_ctor_get(x_1336, 0);
lean_inc(x_1338);
lean_dec(x_1336);
x_1339 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1340 = l_Lean_Expr_const___override(x_1339, x_1293);
x_1341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1341, 0, x_1313);
lean_ctor_set(x_1341, 1, x_51);
x_1342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1342, 0, x_1338);
lean_ctor_set(x_1342, 1, x_1341);
x_1343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1343, 0, x_1278);
lean_ctor_set(x_1343, 1, x_1342);
x_1344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1344, 0, x_41);
lean_ctor_set(x_1344, 1, x_1343);
x_1345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1345, 0, x_55);
lean_ctor_set(x_1345, 1, x_1344);
x_1346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1346, 0, x_40);
lean_ctor_set(x_1346, 1, x_1345);
x_1347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1347, 0, x_54);
lean_ctor_set(x_1347, 1, x_1346);
x_1348 = lean_array_mk(x_1347);
x_1349 = l_Lean_mkAppN(x_1340, x_1348);
lean_dec(x_1348);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1350 = l_Lean_Meta_expandCoe(x_1349, x_3, x_4, x_5, x_6, x_1337);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
x_1351 = lean_ctor_get(x_1350, 0);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1350, 1);
lean_inc(x_1352);
lean_dec(x_1350);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1351);
x_1353 = lean_infer_type(x_1351, x_3, x_4, x_5, x_6, x_1352);
if (lean_obj_tag(x_1353) == 0)
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
x_1354 = lean_ctor_get(x_1353, 0);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1353, 1);
lean_inc(x_1355);
lean_dec(x_1353);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1356 = l_Lean_Meta_isExprDefEq(x_19, x_1354, x_3, x_4, x_5, x_6, x_1355);
if (lean_obj_tag(x_1356) == 0)
{
lean_object* x_1357; uint8_t x_1358; 
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
x_1358 = lean_unbox(x_1357);
lean_dec(x_1357);
if (x_1358 == 0)
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
lean_dec(x_1351);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1359 = lean_ctor_get(x_1356, 1);
lean_inc(x_1359);
if (lean_is_exclusive(x_1356)) {
 lean_ctor_release(x_1356, 0);
 lean_ctor_release(x_1356, 1);
 x_1360 = x_1356;
} else {
 lean_dec_ref(x_1356);
 x_1360 = lean_box(0);
}
if (lean_is_scalar(x_1360)) {
 x_1361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1361 = x_1360;
}
lean_ctor_set(x_1361, 0, x_1274);
lean_ctor_set(x_1361, 1, x_1359);
return x_1361;
}
else
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; 
x_1362 = lean_ctor_get(x_1356, 1);
lean_inc(x_1362);
lean_dec(x_1356);
x_1363 = lean_box(0);
x_1364 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1351, x_1363, x_3, x_4, x_5, x_6, x_1362);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1365 = lean_ctor_get(x_1364, 0);
lean_inc(x_1365);
x_1366 = lean_ctor_get(x_1364, 1);
lean_inc(x_1366);
if (lean_is_exclusive(x_1364)) {
 lean_ctor_release(x_1364, 0);
 lean_ctor_release(x_1364, 1);
 x_1367 = x_1364;
} else {
 lean_dec_ref(x_1364);
 x_1367 = lean_box(0);
}
if (lean_is_scalar(x_1367)) {
 x_1368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1368 = x_1367;
}
lean_ctor_set(x_1368, 0, x_1365);
lean_ctor_set(x_1368, 1, x_1366);
return x_1368;
}
}
else
{
lean_object* x_1369; lean_object* x_1370; 
lean_dec(x_1351);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1369 = lean_ctor_get(x_1356, 0);
lean_inc(x_1369);
x_1370 = lean_ctor_get(x_1356, 1);
lean_inc(x_1370);
lean_dec(x_1356);
x_8 = x_1369;
x_9 = x_1370;
goto block_16;
}
}
else
{
lean_object* x_1371; lean_object* x_1372; 
lean_dec(x_1351);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1371 = lean_ctor_get(x_1353, 0);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1353, 1);
lean_inc(x_1372);
lean_dec(x_1353);
x_8 = x_1371;
x_9 = x_1372;
goto block_16;
}
}
else
{
lean_object* x_1373; lean_object* x_1374; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1373 = lean_ctor_get(x_1350, 0);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_1350, 1);
lean_inc(x_1374);
lean_dec(x_1350);
x_8 = x_1373;
x_9 = x_1374;
goto block_16;
}
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
lean_dec(x_1336);
lean_dec(x_1313);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1375 = lean_ctor_get(x_1335, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 x_1376 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1376 = lean_box(0);
}
if (lean_is_scalar(x_1376)) {
 x_1377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1377 = x_1376;
}
lean_ctor_set(x_1377, 0, x_1274);
lean_ctor_set(x_1377, 1, x_1375);
return x_1377;
}
}
else
{
lean_object* x_1378; lean_object* x_1379; 
lean_dec(x_1313);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1378 = lean_ctor_get(x_1335, 0);
lean_inc(x_1378);
x_1379 = lean_ctor_get(x_1335, 1);
lean_inc(x_1379);
lean_dec(x_1335);
x_8 = x_1378;
x_9 = x_1379;
goto block_16;
}
}
else
{
lean_object* x_1380; lean_object* x_1381; 
lean_dec(x_1317);
lean_dec(x_1315);
lean_dec(x_1313);
lean_dec(x_1302);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1380 = lean_ctor_get(x_1318, 0);
lean_inc(x_1380);
x_1381 = lean_ctor_get(x_1318, 1);
lean_inc(x_1381);
lean_dec(x_1318);
x_8 = x_1380;
x_9 = x_1381;
goto block_16;
}
}
else
{
lean_object* x_1382; lean_object* x_1383; 
lean_dec(x_1313);
lean_dec(x_1302);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1382 = lean_ctor_get(x_1314, 0);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1314, 1);
lean_inc(x_1383);
lean_dec(x_1314);
x_8 = x_1382;
x_9 = x_1383;
goto block_16;
}
}
}
else
{
lean_object* x_1384; lean_object* x_1385; 
lean_dec(x_1302);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1384 = lean_ctor_get(x_1307, 0);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_1307, 1);
lean_inc(x_1385);
lean_dec(x_1307);
x_8 = x_1384;
x_9 = x_1385;
goto block_16;
}
}
else
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
lean_dec(x_1302);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1386 = lean_ctor_get(x_1303, 1);
lean_inc(x_1386);
if (lean_is_exclusive(x_1303)) {
 lean_ctor_release(x_1303, 0);
 lean_ctor_release(x_1303, 1);
 x_1387 = x_1303;
} else {
 lean_dec_ref(x_1303);
 x_1387 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_1298);
if (lean_is_scalar(x_1387)) {
 x_1388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1388 = x_1387;
}
lean_ctor_set(x_1388, 0, x_43);
lean_ctor_set(x_1388, 1, x_1386);
return x_1388;
}
}
else
{
lean_object* x_1389; lean_object* x_1390; 
lean_dec(x_1302);
lean_dec(x_1298);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1389 = lean_ctor_get(x_1303, 0);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_1303, 1);
lean_inc(x_1390);
lean_dec(x_1303);
x_8 = x_1389;
x_9 = x_1390;
goto block_16;
}
}
else
{
lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_1298);
lean_dec(x_51);
lean_dec(x_1293);
lean_dec(x_1278);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1391 = lean_ctor_get(x_1299, 0);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_1299, 1);
lean_inc(x_1392);
lean_dec(x_1299);
x_8 = x_1391;
x_9 = x_1392;
goto block_16;
}
}
else
{
lean_object* x_1393; lean_object* x_1394; 
lean_dec(x_1286);
lean_dec(x_1284);
lean_dec(x_1282);
lean_dec(x_1280);
lean_dec(x_1278);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1393 = lean_ctor_get(x_1287, 0);
lean_inc(x_1393);
x_1394 = lean_ctor_get(x_1287, 1);
lean_inc(x_1394);
lean_dec(x_1287);
x_8 = x_1393;
x_9 = x_1394;
goto block_16;
}
}
else
{
lean_object* x_1395; lean_object* x_1396; 
lean_dec(x_1282);
lean_dec(x_1280);
lean_dec(x_1278);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1395 = lean_ctor_get(x_1283, 0);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1283, 1);
lean_inc(x_1396);
lean_dec(x_1283);
x_8 = x_1395;
x_9 = x_1396;
goto block_16;
}
}
else
{
lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_1278);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1397 = lean_ctor_get(x_1279, 0);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1279, 1);
lean_inc(x_1398);
lean_dec(x_1279);
x_8 = x_1397;
x_9 = x_1398;
goto block_16;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1276);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1399 = lean_ctor_get(x_1275, 1);
lean_inc(x_1399);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 x_1400 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1400 = lean_box(0);
}
if (lean_is_scalar(x_1400)) {
 x_1401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1401 = x_1400;
}
lean_ctor_set(x_1401, 0, x_1274);
lean_ctor_set(x_1401, 1, x_1399);
return x_1401;
}
}
else
{
lean_object* x_1402; lean_object* x_1403; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1402 = lean_ctor_get(x_1275, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1275, 1);
lean_inc(x_1403);
lean_dec(x_1275);
x_8 = x_1402;
x_9 = x_1403;
goto block_16;
}
}
else
{
lean_object* x_1404; lean_object* x_1405; 
lean_dec(x_1260);
lean_dec(x_1258);
lean_dec(x_1247);
lean_dec(x_1242);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1404 = lean_ctor_get(x_1261, 0);
lean_inc(x_1404);
x_1405 = lean_ctor_get(x_1261, 1);
lean_inc(x_1405);
lean_dec(x_1261);
x_8 = x_1404;
x_9 = x_1405;
goto block_16;
}
}
else
{
lean_object* x_1406; lean_object* x_1407; 
lean_dec(x_1247);
lean_dec(x_1242);
lean_dec(x_89);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1406 = lean_ctor_get(x_1257, 0);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1257, 1);
lean_inc(x_1407);
lean_dec(x_1257);
x_8 = x_1406;
x_9 = x_1407;
goto block_16;
}
}
}
else
{
lean_object* x_1408; lean_object* x_1409; 
lean_dec(x_1247);
lean_dec(x_1242);
lean_dec(x_89);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1408 = lean_ctor_get(x_1249, 0);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1249, 1);
lean_inc(x_1409);
lean_dec(x_1249);
x_8 = x_1408;
x_9 = x_1409;
goto block_16;
}
}
else
{
lean_object* x_1410; lean_object* x_1411; 
lean_dec(x_1242);
lean_dec(x_89);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1410 = lean_ctor_get(x_1244, 0);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1244, 1);
lean_inc(x_1411);
lean_dec(x_1244);
x_8 = x_1410;
x_9 = x_1411;
goto block_16;
}
}
}
else
{
lean_object* x_1412; lean_object* x_1413; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_79);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1412 = lean_ctor_get(x_90, 0);
lean_inc(x_1412);
x_1413 = lean_ctor_get(x_90, 1);
lean_inc(x_1413);
lean_dec(x_90);
x_8 = x_1412;
x_9 = x_1413;
goto block_16;
}
}
else
{
uint8_t x_1414; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_79);
lean_dec(x_78);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1414 = !lean_is_exclusive(x_83);
if (x_1414 == 0)
{
lean_object* x_1415; lean_object* x_1416; 
x_1415 = lean_ctor_get(x_83, 0);
lean_dec(x_1415);
x_1416 = lean_box(0);
lean_ctor_set(x_83, 0, x_1416);
return x_83;
}
else
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1417 = lean_ctor_get(x_83, 1);
lean_inc(x_1417);
lean_dec(x_83);
x_1418 = lean_box(0);
x_1419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1419, 0, x_1418);
lean_ctor_set(x_1419, 1, x_1417);
return x_1419;
}
}
}
else
{
uint8_t x_1420; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_79);
lean_dec(x_78);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1420 = !lean_is_exclusive(x_83);
if (x_1420 == 0)
{
lean_object* x_1421; lean_object* x_1422; 
x_1421 = lean_ctor_get(x_83, 0);
lean_dec(x_1421);
x_1422 = lean_box(0);
lean_ctor_set(x_83, 0, x_1422);
return x_83;
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
x_1423 = lean_ctor_get(x_83, 1);
lean_inc(x_1423);
lean_dec(x_83);
x_1424 = lean_box(0);
x_1425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1425, 0, x_1424);
lean_ctor_set(x_1425, 1, x_1423);
return x_1425;
}
}
}
else
{
uint8_t x_1426; 
lean_dec(x_84);
lean_dec(x_79);
lean_dec(x_78);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1426 = !lean_is_exclusive(x_83);
if (x_1426 == 0)
{
lean_object* x_1427; lean_object* x_1428; 
x_1427 = lean_ctor_get(x_83, 0);
lean_dec(x_1427);
x_1428 = lean_box(0);
lean_ctor_set(x_83, 0, x_1428);
return x_83;
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; 
x_1429 = lean_ctor_get(x_83, 1);
lean_inc(x_1429);
lean_dec(x_83);
x_1430 = lean_box(0);
x_1431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1431, 0, x_1430);
lean_ctor_set(x_1431, 1, x_1429);
return x_1431;
}
}
}
else
{
uint8_t x_1432; 
lean_dec(x_79);
lean_dec(x_78);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1432 = !lean_is_exclusive(x_83);
if (x_1432 == 0)
{
lean_object* x_1433; uint8_t x_1434; 
x_1433 = lean_ctor_get(x_83, 0);
x_1434 = l_Lean_Exception_isInterrupt(x_1433);
if (x_1434 == 0)
{
uint8_t x_1435; 
x_1435 = l_Lean_Exception_isRuntime(x_1433);
if (x_1435 == 0)
{
lean_object* x_1436; 
lean_dec(x_1433);
x_1436 = lean_box(0);
lean_ctor_set_tag(x_83, 0);
lean_ctor_set(x_83, 0, x_1436);
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
lean_object* x_1437; lean_object* x_1438; uint8_t x_1439; 
x_1437 = lean_ctor_get(x_83, 0);
x_1438 = lean_ctor_get(x_83, 1);
lean_inc(x_1438);
lean_inc(x_1437);
lean_dec(x_83);
x_1439 = l_Lean_Exception_isInterrupt(x_1437);
if (x_1439 == 0)
{
uint8_t x_1440; 
x_1440 = l_Lean_Exception_isRuntime(x_1437);
if (x_1440 == 0)
{
lean_object* x_1441; lean_object* x_1442; 
lean_dec(x_1437);
x_1441 = lean_box(0);
x_1442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1442, 0, x_1441);
lean_ctor_set(x_1442, 1, x_1438);
return x_1442;
}
else
{
lean_object* x_1443; 
x_1443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1443, 0, x_1437);
lean_ctor_set(x_1443, 1, x_1438);
return x_1443;
}
}
else
{
lean_object* x_1444; 
x_1444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1444, 0, x_1437);
lean_ctor_set(x_1444, 1, x_1438);
return x_1444;
}
}
}
}
else
{
uint8_t x_1445; 
lean_dec(x_79);
lean_dec(x_78);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1445 = !lean_is_exclusive(x_80);
if (x_1445 == 0)
{
lean_object* x_1446; uint8_t x_1447; 
x_1446 = lean_ctor_get(x_80, 0);
x_1447 = l_Lean_Exception_isInterrupt(x_1446);
if (x_1447 == 0)
{
uint8_t x_1448; 
x_1448 = l_Lean_Exception_isRuntime(x_1446);
if (x_1448 == 0)
{
lean_object* x_1449; 
lean_dec(x_1446);
x_1449 = lean_box(0);
lean_ctor_set_tag(x_80, 0);
lean_ctor_set(x_80, 0, x_1449);
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
lean_object* x_1450; lean_object* x_1451; uint8_t x_1452; 
x_1450 = lean_ctor_get(x_80, 0);
x_1451 = lean_ctor_get(x_80, 1);
lean_inc(x_1451);
lean_inc(x_1450);
lean_dec(x_80);
x_1452 = l_Lean_Exception_isInterrupt(x_1450);
if (x_1452 == 0)
{
uint8_t x_1453; 
x_1453 = l_Lean_Exception_isRuntime(x_1450);
if (x_1453 == 0)
{
lean_object* x_1454; lean_object* x_1455; 
lean_dec(x_1450);
x_1454 = lean_box(0);
x_1455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1455, 0, x_1454);
lean_ctor_set(x_1455, 1, x_1451);
return x_1455;
}
else
{
lean_object* x_1456; 
x_1456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1456, 0, x_1450);
lean_ctor_set(x_1456, 1, x_1451);
return x_1456;
}
}
else
{
lean_object* x_1457; 
x_1457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1457, 0, x_1450);
lean_ctor_set(x_1457, 1, x_1451);
return x_1457;
}
}
}
}
else
{
uint8_t x_1458; 
lean_dec(x_76);
lean_dec(x_75);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1458 = !lean_is_exclusive(x_73);
if (x_1458 == 0)
{
lean_object* x_1459; lean_object* x_1460; 
x_1459 = lean_ctor_get(x_73, 0);
lean_dec(x_1459);
x_1460 = lean_box(0);
lean_ctor_set(x_73, 0, x_1460);
return x_73;
}
else
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
x_1461 = lean_ctor_get(x_73, 1);
lean_inc(x_1461);
lean_dec(x_73);
x_1462 = lean_box(0);
x_1463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1463, 0, x_1462);
lean_ctor_set(x_1463, 1, x_1461);
return x_1463;
}
}
}
else
{
uint8_t x_1464; 
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1464 = !lean_is_exclusive(x_73);
if (x_1464 == 0)
{
lean_object* x_1465; lean_object* x_1466; 
x_1465 = lean_ctor_get(x_73, 0);
lean_dec(x_1465);
x_1466 = lean_box(0);
lean_ctor_set(x_73, 0, x_1466);
return x_73;
}
else
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; 
x_1467 = lean_ctor_get(x_73, 1);
lean_inc(x_1467);
lean_dec(x_73);
x_1468 = lean_box(0);
x_1469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1469, 0, x_1468);
lean_ctor_set(x_1469, 1, x_1467);
return x_1469;
}
}
}
else
{
uint8_t x_1470; 
lean_dec(x_74);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1470 = !lean_is_exclusive(x_73);
if (x_1470 == 0)
{
lean_object* x_1471; lean_object* x_1472; 
x_1471 = lean_ctor_get(x_73, 0);
lean_dec(x_1471);
x_1472 = lean_box(0);
lean_ctor_set(x_73, 0, x_1472);
return x_73;
}
else
{
lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
x_1473 = lean_ctor_get(x_73, 1);
lean_inc(x_1473);
lean_dec(x_73);
x_1474 = lean_box(0);
x_1475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1475, 0, x_1474);
lean_ctor_set(x_1475, 1, x_1473);
return x_1475;
}
}
}
else
{
uint8_t x_1476; 
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1476 = !lean_is_exclusive(x_73);
if (x_1476 == 0)
{
lean_object* x_1477; uint8_t x_1478; 
x_1477 = lean_ctor_get(x_73, 0);
x_1478 = l_Lean_Exception_isInterrupt(x_1477);
if (x_1478 == 0)
{
uint8_t x_1479; 
x_1479 = l_Lean_Exception_isRuntime(x_1477);
if (x_1479 == 0)
{
lean_object* x_1480; 
lean_dec(x_1477);
x_1480 = lean_box(0);
lean_ctor_set_tag(x_73, 0);
lean_ctor_set(x_73, 0, x_1480);
return x_73;
}
else
{
return x_73;
}
}
else
{
return x_73;
}
}
else
{
lean_object* x_1481; lean_object* x_1482; uint8_t x_1483; 
x_1481 = lean_ctor_get(x_73, 0);
x_1482 = lean_ctor_get(x_73, 1);
lean_inc(x_1482);
lean_inc(x_1481);
lean_dec(x_73);
x_1483 = l_Lean_Exception_isInterrupt(x_1481);
if (x_1483 == 0)
{
uint8_t x_1484; 
x_1484 = l_Lean_Exception_isRuntime(x_1481);
if (x_1484 == 0)
{
lean_object* x_1485; lean_object* x_1486; 
lean_dec(x_1481);
x_1485 = lean_box(0);
x_1486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1486, 0, x_1485);
lean_ctor_set(x_1486, 1, x_1482);
return x_1486;
}
else
{
lean_object* x_1487; 
x_1487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1487, 0, x_1481);
lean_ctor_set(x_1487, 1, x_1482);
return x_1487;
}
}
else
{
lean_object* x_1488; 
x_1488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1488, 0, x_1481);
lean_ctor_set(x_1488, 1, x_1482);
return x_1488;
}
}
}
}
else
{
uint8_t x_1489; 
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1489 = !lean_is_exclusive(x_70);
if (x_1489 == 0)
{
lean_object* x_1490; uint8_t x_1491; 
x_1490 = lean_ctor_get(x_70, 0);
x_1491 = l_Lean_Exception_isInterrupt(x_1490);
if (x_1491 == 0)
{
uint8_t x_1492; 
x_1492 = l_Lean_Exception_isRuntime(x_1490);
if (x_1492 == 0)
{
lean_object* x_1493; 
lean_dec(x_1490);
x_1493 = lean_box(0);
lean_ctor_set_tag(x_70, 0);
lean_ctor_set(x_70, 0, x_1493);
return x_70;
}
else
{
return x_70;
}
}
else
{
return x_70;
}
}
else
{
lean_object* x_1494; lean_object* x_1495; uint8_t x_1496; 
x_1494 = lean_ctor_get(x_70, 0);
x_1495 = lean_ctor_get(x_70, 1);
lean_inc(x_1495);
lean_inc(x_1494);
lean_dec(x_70);
x_1496 = l_Lean_Exception_isInterrupt(x_1494);
if (x_1496 == 0)
{
uint8_t x_1497; 
x_1497 = l_Lean_Exception_isRuntime(x_1494);
if (x_1497 == 0)
{
lean_object* x_1498; lean_object* x_1499; 
lean_dec(x_1494);
x_1498 = lean_box(0);
x_1499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1499, 0, x_1498);
lean_ctor_set(x_1499, 1, x_1495);
return x_1499;
}
else
{
lean_object* x_1500; 
x_1500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1500, 0, x_1494);
lean_ctor_set(x_1500, 1, x_1495);
return x_1500;
}
}
else
{
lean_object* x_1501; 
x_1501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1501, 0, x_1494);
lean_ctor_set(x_1501, 1, x_1495);
return x_1501;
}
}
}
}
}
else
{
lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; uint8_t x_1505; 
x_1502 = lean_ctor_get(x_60, 1);
lean_inc(x_1502);
lean_dec(x_60);
x_1503 = lean_ctor_get(x_5, 2);
lean_inc(x_1503);
x_1504 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1505 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1503, x_1504);
lean_dec(x_1503);
if (x_1505 == 0)
{
lean_object* x_1506; lean_object* x_1507; 
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1506 = lean_box(0);
x_1507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1507, 0, x_1506);
lean_ctor_set(x_1507, 1, x_1502);
return x_1507;
}
else
{
lean_object* x_1508; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_1508 = lean_infer_type(x_54, x_3, x_4, x_5, x_6, x_1502);
if (lean_obj_tag(x_1508) == 0)
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
x_1509 = lean_ctor_get(x_1508, 0);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1508, 1);
lean_inc(x_1510);
lean_dec(x_1508);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1511 = lean_whnf(x_1509, x_3, x_4, x_5, x_6, x_1510);
if (lean_obj_tag(x_1511) == 0)
{
lean_object* x_1512; 
x_1512 = lean_ctor_get(x_1511, 0);
lean_inc(x_1512);
if (lean_obj_tag(x_1512) == 7)
{
lean_object* x_1513; 
x_1513 = lean_ctor_get(x_1512, 1);
lean_inc(x_1513);
if (lean_obj_tag(x_1513) == 3)
{
lean_object* x_1514; 
x_1514 = lean_ctor_get(x_1512, 2);
lean_inc(x_1514);
lean_dec(x_1512);
if (lean_obj_tag(x_1514) == 3)
{
lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
x_1515 = lean_ctor_get(x_1511, 1);
lean_inc(x_1515);
lean_dec(x_1511);
x_1516 = lean_ctor_get(x_1513, 0);
lean_inc(x_1516);
lean_dec(x_1513);
x_1517 = lean_ctor_get(x_1514, 0);
lean_inc(x_1517);
lean_dec(x_1514);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_1518 = lean_infer_type(x_40, x_3, x_4, x_5, x_6, x_1515);
if (lean_obj_tag(x_1518) == 0)
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; 
x_1519 = lean_ctor_get(x_1518, 0);
lean_inc(x_1519);
x_1520 = lean_ctor_get(x_1518, 1);
lean_inc(x_1520);
lean_dec(x_1518);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1521 = lean_whnf(x_1519, x_3, x_4, x_5, x_6, x_1520);
if (lean_obj_tag(x_1521) == 0)
{
lean_object* x_1522; 
x_1522 = lean_ctor_get(x_1521, 0);
lean_inc(x_1522);
if (lean_obj_tag(x_1522) == 7)
{
lean_object* x_1523; 
x_1523 = lean_ctor_get(x_1522, 1);
lean_inc(x_1523);
if (lean_obj_tag(x_1523) == 3)
{
lean_object* x_1524; 
x_1524 = lean_ctor_get(x_1522, 2);
lean_inc(x_1524);
lean_dec(x_1522);
if (lean_obj_tag(x_1524) == 3)
{
lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
x_1525 = lean_ctor_get(x_1521, 1);
lean_inc(x_1525);
lean_dec(x_1521);
x_1526 = lean_ctor_get(x_1523, 0);
lean_inc(x_1526);
lean_dec(x_1523);
x_1527 = lean_ctor_get(x_1524, 0);
lean_inc(x_1527);
lean_dec(x_1524);
x_1528 = l_Lean_Meta_decLevel(x_1516, x_3, x_4, x_5, x_6, x_1525);
if (lean_obj_tag(x_1528) == 0)
{
lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; 
x_1529 = lean_ctor_get(x_1528, 0);
lean_inc(x_1529);
x_1530 = lean_ctor_get(x_1528, 1);
lean_inc(x_1530);
if (lean_is_exclusive(x_1528)) {
 lean_ctor_release(x_1528, 0);
 lean_ctor_release(x_1528, 1);
 x_1531 = x_1528;
} else {
 lean_dec_ref(x_1528);
 x_1531 = lean_box(0);
}
x_1532 = l_Lean_Meta_decLevel(x_1526, x_3, x_4, x_5, x_6, x_1530);
if (lean_obj_tag(x_1532) == 0)
{
lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; uint8_t x_1536; lean_object* x_1537; 
x_1533 = lean_ctor_get(x_1532, 0);
lean_inc(x_1533);
x_1534 = lean_ctor_get(x_1532, 1);
lean_inc(x_1534);
if (lean_is_exclusive(x_1532)) {
 lean_ctor_release(x_1532, 0);
 lean_ctor_release(x_1532, 1);
 x_1535 = x_1532;
} else {
 lean_dec_ref(x_1532);
 x_1535 = lean_box(0);
}
x_1536 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1529);
x_1537 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1529, x_1533, x_1536, x_3, x_4, x_5, x_6, x_1534);
if (lean_obj_tag(x_1537) == 0)
{
lean_object* x_1538; uint8_t x_1539; 
x_1538 = lean_ctor_get(x_1537, 0);
lean_inc(x_1538);
x_1539 = lean_unbox(x_1538);
lean_dec(x_1538);
if (x_1539 == 0)
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; 
lean_dec(x_1535);
lean_dec(x_1531);
lean_dec(x_1529);
lean_dec(x_1527);
lean_dec(x_1517);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1540 = lean_ctor_get(x_1537, 1);
lean_inc(x_1540);
if (lean_is_exclusive(x_1537)) {
 lean_ctor_release(x_1537, 0);
 lean_ctor_release(x_1537, 1);
 x_1541 = x_1537;
} else {
 lean_dec_ref(x_1537);
 x_1541 = lean_box(0);
}
x_1542 = lean_box(0);
if (lean_is_scalar(x_1541)) {
 x_1543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1543 = x_1541;
}
lean_ctor_set(x_1543, 0, x_1542);
lean_ctor_set(x_1543, 1, x_1540);
return x_1543;
}
else
{
lean_object* x_1544; lean_object* x_1545; 
x_1544 = lean_ctor_get(x_1537, 1);
lean_inc(x_1544);
lean_dec(x_1537);
x_1545 = l_Lean_Meta_decLevel(x_1517, x_3, x_4, x_5, x_6, x_1544);
if (lean_obj_tag(x_1545) == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; 
x_1546 = lean_ctor_get(x_1545, 0);
lean_inc(x_1546);
x_1547 = lean_ctor_get(x_1545, 1);
lean_inc(x_1547);
if (lean_is_exclusive(x_1545)) {
 lean_ctor_release(x_1545, 0);
 lean_ctor_release(x_1545, 1);
 x_1548 = x_1545;
} else {
 lean_dec_ref(x_1545);
 x_1548 = lean_box(0);
}
x_1549 = l_Lean_Meta_decLevel(x_1527, x_3, x_4, x_5, x_6, x_1547);
if (lean_obj_tag(x_1549) == 0)
{
lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
x_1550 = lean_ctor_get(x_1549, 0);
lean_inc(x_1550);
x_1551 = lean_ctor_get(x_1549, 1);
lean_inc(x_1551);
if (lean_is_exclusive(x_1549)) {
 lean_ctor_release(x_1549, 0);
 lean_ctor_release(x_1549, 1);
 x_1552 = x_1549;
} else {
 lean_dec_ref(x_1549);
 x_1552 = lean_box(0);
}
x_1553 = lean_box(0);
if (lean_is_scalar(x_1552)) {
 x_1554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1554 = x_1552;
 lean_ctor_set_tag(x_1554, 1);
}
lean_ctor_set(x_1554, 0, x_1550);
lean_ctor_set(x_1554, 1, x_1553);
if (lean_is_scalar(x_1548)) {
 x_1555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1555 = x_1548;
 lean_ctor_set_tag(x_1555, 1);
}
lean_ctor_set(x_1555, 0, x_1546);
lean_ctor_set(x_1555, 1, x_1554);
if (lean_is_scalar(x_1535)) {
 x_1556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1556 = x_1535;
 lean_ctor_set_tag(x_1556, 1);
}
lean_ctor_set(x_1556, 0, x_1529);
lean_ctor_set(x_1556, 1, x_1555);
x_1557 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1558 = l_Lean_Expr_const___override(x_1557, x_1556);
lean_inc(x_40);
if (lean_is_scalar(x_1531)) {
 x_1559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1559 = x_1531;
 lean_ctor_set_tag(x_1559, 1);
}
lean_ctor_set(x_1559, 0, x_40);
lean_ctor_set(x_1559, 1, x_1553);
lean_inc(x_54);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_1559);
lean_ctor_set(x_56, 0, x_54);
x_1560 = lean_array_mk(x_56);
x_1561 = l_Lean_mkAppN(x_1558, x_1560);
lean_dec(x_1560);
x_1562 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1563 = l_Lean_Meta_trySynthInstance(x_1561, x_1562, x_3, x_4, x_5, x_6, x_1551);
if (lean_obj_tag(x_1563) == 0)
{
lean_object* x_1564; 
x_1564 = lean_ctor_get(x_1563, 0);
lean_inc(x_1564);
if (lean_obj_tag(x_1564) == 1)
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; 
x_1565 = lean_ctor_get(x_1563, 1);
lean_inc(x_1565);
lean_dec(x_1563);
x_1566 = lean_ctor_get(x_1564, 0);
lean_inc(x_1566);
lean_dec(x_1564);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1567 = l_Lean_Meta_getDecLevel(x_55, x_3, x_4, x_5, x_6, x_1565);
if (lean_obj_tag(x_1567) == 0)
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1571 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_1569);
if (lean_obj_tag(x_1571) == 0)
{
lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; 
x_1572 = lean_ctor_get(x_1571, 0);
lean_inc(x_1572);
x_1573 = lean_ctor_get(x_1571, 1);
lean_inc(x_1573);
if (lean_is_exclusive(x_1571)) {
 lean_ctor_release(x_1571, 0);
 lean_ctor_release(x_1571, 1);
 x_1574 = x_1571;
} else {
 lean_dec_ref(x_1571);
 x_1574 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_1575 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_1573);
if (lean_obj_tag(x_1575) == 0)
{
lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1576 = lean_ctor_get(x_1575, 0);
lean_inc(x_1576);
x_1577 = lean_ctor_get(x_1575, 1);
lean_inc(x_1577);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1578 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1578 = lean_box(0);
}
if (lean_is_scalar(x_1578)) {
 x_1579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1579 = x_1578;
 lean_ctor_set_tag(x_1579, 1);
}
lean_ctor_set(x_1579, 0, x_1576);
lean_ctor_set(x_1579, 1, x_1553);
if (lean_is_scalar(x_1574)) {
 x_1580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1580 = x_1574;
 lean_ctor_set_tag(x_1580, 1);
}
lean_ctor_set(x_1580, 0, x_1572);
lean_ctor_set(x_1580, 1, x_1579);
if (lean_is_scalar(x_1570)) {
 x_1581 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1581 = x_1570;
 lean_ctor_set_tag(x_1581, 1);
}
lean_ctor_set(x_1581, 0, x_1568);
lean_ctor_set(x_1581, 1, x_1580);
x_1582 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_1581);
x_1583 = l_Lean_Expr_const___override(x_1582, x_1581);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_1553);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_1566);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_1566);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_1584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1584, 0, x_54);
lean_ctor_set(x_1584, 1, x_17);
x_1585 = lean_array_mk(x_1584);
x_1586 = l_Lean_mkAppN(x_1583, x_1585);
lean_dec(x_1585);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1586);
x_1587 = lean_infer_type(x_1586, x_3, x_4, x_5, x_6, x_1577);
if (lean_obj_tag(x_1587) == 0)
{
lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
x_1588 = lean_ctor_get(x_1587, 0);
lean_inc(x_1588);
x_1589 = lean_ctor_get(x_1587, 1);
lean_inc(x_1589);
if (lean_is_exclusive(x_1587)) {
 lean_ctor_release(x_1587, 0);
 lean_ctor_release(x_1587, 1);
 x_1590 = x_1587;
} else {
 lean_dec_ref(x_1587);
 x_1590 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_1591 = l_Lean_Meta_isExprDefEq(x_19, x_1588, x_3, x_4, x_5, x_6, x_1589);
if (lean_obj_tag(x_1591) == 0)
{
lean_object* x_1592; uint8_t x_1593; 
x_1592 = lean_ctor_get(x_1591, 0);
lean_inc(x_1592);
x_1593 = lean_unbox(x_1592);
lean_dec(x_1592);
if (x_1593 == 0)
{
lean_object* x_1594; lean_object* x_1595; 
lean_dec(x_1586);
lean_free_object(x_43);
x_1594 = lean_ctor_get(x_1591, 1);
lean_inc(x_1594);
lean_dec(x_1591);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_1595 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_1594);
if (lean_obj_tag(x_1595) == 0)
{
lean_object* x_1596; 
x_1596 = lean_ctor_get(x_1595, 0);
lean_inc(x_1596);
if (lean_obj_tag(x_1596) == 0)
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
lean_dec(x_1590);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1597 = lean_ctor_get(x_1595, 1);
lean_inc(x_1597);
if (lean_is_exclusive(x_1595)) {
 lean_ctor_release(x_1595, 0);
 lean_ctor_release(x_1595, 1);
 x_1598 = x_1595;
} else {
 lean_dec_ref(x_1595);
 x_1598 = lean_box(0);
}
if (lean_is_scalar(x_1598)) {
 x_1599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1599 = x_1598;
}
lean_ctor_set(x_1599, 0, x_1562);
lean_ctor_set(x_1599, 1, x_1597);
return x_1599;
}
else
{
lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; 
x_1600 = lean_ctor_get(x_1595, 1);
lean_inc(x_1600);
lean_dec(x_1595);
x_1601 = lean_ctor_get(x_1596, 0);
lean_inc(x_1601);
lean_dec(x_1596);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1602 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_1600);
if (lean_obj_tag(x_1602) == 0)
{
lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
x_1603 = lean_ctor_get(x_1602, 0);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1602, 1);
lean_inc(x_1604);
if (lean_is_exclusive(x_1602)) {
 lean_ctor_release(x_1602, 0);
 lean_ctor_release(x_1602, 1);
 x_1605 = x_1602;
} else {
 lean_dec_ref(x_1602);
 x_1605 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_1606 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_1604);
if (lean_obj_tag(x_1606) == 0)
{
lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; uint8_t x_1621; lean_object* x_1622; lean_object* x_1623; 
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
if (lean_is_scalar(x_1609)) {
 x_1610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1610 = x_1609;
 lean_ctor_set_tag(x_1610, 1);
}
lean_ctor_set(x_1610, 0, x_1607);
lean_ctor_set(x_1610, 1, x_1553);
if (lean_is_scalar(x_1605)) {
 x_1611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1611 = x_1605;
 lean_ctor_set_tag(x_1611, 1);
}
lean_ctor_set(x_1611, 0, x_1603);
lean_ctor_set(x_1611, 1, x_1610);
x_1612 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1613 = l_Lean_Expr_const___override(x_1612, x_1611);
lean_inc(x_41);
if (lean_is_scalar(x_1590)) {
 x_1614 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1614 = x_1590;
 lean_ctor_set_tag(x_1614, 1);
}
lean_ctor_set(x_1614, 0, x_41);
lean_ctor_set(x_1614, 1, x_1553);
x_1615 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1616, 0, x_1615);
lean_ctor_set(x_1616, 1, x_1614);
lean_inc(x_55);
x_1617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1617, 0, x_55);
lean_ctor_set(x_1617, 1, x_1616);
x_1618 = lean_array_mk(x_1617);
x_1619 = l_Lean_mkAppN(x_1613, x_1618);
lean_dec(x_1618);
x_1620 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1621 = 0;
lean_inc(x_55);
x_1622 = l_Lean_Expr_forallE___override(x_1620, x_55, x_1619, x_1621);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1623 = l_Lean_Meta_trySynthInstance(x_1622, x_1562, x_3, x_4, x_5, x_6, x_1608);
if (lean_obj_tag(x_1623) == 0)
{
lean_object* x_1624; 
x_1624 = lean_ctor_get(x_1623, 0);
lean_inc(x_1624);
if (lean_obj_tag(x_1624) == 1)
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; 
x_1625 = lean_ctor_get(x_1623, 1);
lean_inc(x_1625);
lean_dec(x_1623);
x_1626 = lean_ctor_get(x_1624, 0);
lean_inc(x_1626);
lean_dec(x_1624);
x_1627 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1628 = l_Lean_Expr_const___override(x_1627, x_1581);
x_1629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1629, 0, x_1601);
lean_ctor_set(x_1629, 1, x_51);
x_1630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1630, 0, x_1626);
lean_ctor_set(x_1630, 1, x_1629);
x_1631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1631, 0, x_1566);
lean_ctor_set(x_1631, 1, x_1630);
x_1632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1632, 0, x_41);
lean_ctor_set(x_1632, 1, x_1631);
x_1633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1633, 0, x_55);
lean_ctor_set(x_1633, 1, x_1632);
x_1634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1634, 0, x_40);
lean_ctor_set(x_1634, 1, x_1633);
x_1635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1635, 0, x_54);
lean_ctor_set(x_1635, 1, x_1634);
x_1636 = lean_array_mk(x_1635);
x_1637 = l_Lean_mkAppN(x_1628, x_1636);
lean_dec(x_1636);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1638 = l_Lean_Meta_expandCoe(x_1637, x_3, x_4, x_5, x_6, x_1625);
if (lean_obj_tag(x_1638) == 0)
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; 
x_1639 = lean_ctor_get(x_1638, 0);
lean_inc(x_1639);
x_1640 = lean_ctor_get(x_1638, 1);
lean_inc(x_1640);
lean_dec(x_1638);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1639);
x_1641 = lean_infer_type(x_1639, x_3, x_4, x_5, x_6, x_1640);
if (lean_obj_tag(x_1641) == 0)
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
x_1642 = lean_ctor_get(x_1641, 0);
lean_inc(x_1642);
x_1643 = lean_ctor_get(x_1641, 1);
lean_inc(x_1643);
lean_dec(x_1641);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1644 = l_Lean_Meta_isExprDefEq(x_19, x_1642, x_3, x_4, x_5, x_6, x_1643);
if (lean_obj_tag(x_1644) == 0)
{
lean_object* x_1645; uint8_t x_1646; 
x_1645 = lean_ctor_get(x_1644, 0);
lean_inc(x_1645);
x_1646 = lean_unbox(x_1645);
lean_dec(x_1645);
if (x_1646 == 0)
{
lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; 
lean_dec(x_1639);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1647 = lean_ctor_get(x_1644, 1);
lean_inc(x_1647);
if (lean_is_exclusive(x_1644)) {
 lean_ctor_release(x_1644, 0);
 lean_ctor_release(x_1644, 1);
 x_1648 = x_1644;
} else {
 lean_dec_ref(x_1644);
 x_1648 = lean_box(0);
}
if (lean_is_scalar(x_1648)) {
 x_1649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1649 = x_1648;
}
lean_ctor_set(x_1649, 0, x_1562);
lean_ctor_set(x_1649, 1, x_1647);
return x_1649;
}
else
{
lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; 
x_1650 = lean_ctor_get(x_1644, 1);
lean_inc(x_1650);
lean_dec(x_1644);
x_1651 = lean_box(0);
x_1652 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1639, x_1651, x_3, x_4, x_5, x_6, x_1650);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1653 = lean_ctor_get(x_1652, 0);
lean_inc(x_1653);
x_1654 = lean_ctor_get(x_1652, 1);
lean_inc(x_1654);
if (lean_is_exclusive(x_1652)) {
 lean_ctor_release(x_1652, 0);
 lean_ctor_release(x_1652, 1);
 x_1655 = x_1652;
} else {
 lean_dec_ref(x_1652);
 x_1655 = lean_box(0);
}
if (lean_is_scalar(x_1655)) {
 x_1656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1656 = x_1655;
}
lean_ctor_set(x_1656, 0, x_1653);
lean_ctor_set(x_1656, 1, x_1654);
return x_1656;
}
}
else
{
lean_object* x_1657; lean_object* x_1658; 
lean_dec(x_1639);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1657 = lean_ctor_get(x_1644, 0);
lean_inc(x_1657);
x_1658 = lean_ctor_get(x_1644, 1);
lean_inc(x_1658);
lean_dec(x_1644);
x_8 = x_1657;
x_9 = x_1658;
goto block_16;
}
}
else
{
lean_object* x_1659; lean_object* x_1660; 
lean_dec(x_1639);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1659 = lean_ctor_get(x_1641, 0);
lean_inc(x_1659);
x_1660 = lean_ctor_get(x_1641, 1);
lean_inc(x_1660);
lean_dec(x_1641);
x_8 = x_1659;
x_9 = x_1660;
goto block_16;
}
}
else
{
lean_object* x_1661; lean_object* x_1662; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1661 = lean_ctor_get(x_1638, 0);
lean_inc(x_1661);
x_1662 = lean_ctor_get(x_1638, 1);
lean_inc(x_1662);
lean_dec(x_1638);
x_8 = x_1661;
x_9 = x_1662;
goto block_16;
}
}
else
{
lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; 
lean_dec(x_1624);
lean_dec(x_1601);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1663 = lean_ctor_get(x_1623, 1);
lean_inc(x_1663);
if (lean_is_exclusive(x_1623)) {
 lean_ctor_release(x_1623, 0);
 lean_ctor_release(x_1623, 1);
 x_1664 = x_1623;
} else {
 lean_dec_ref(x_1623);
 x_1664 = lean_box(0);
}
if (lean_is_scalar(x_1664)) {
 x_1665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1665 = x_1664;
}
lean_ctor_set(x_1665, 0, x_1562);
lean_ctor_set(x_1665, 1, x_1663);
return x_1665;
}
}
else
{
lean_object* x_1666; lean_object* x_1667; 
lean_dec(x_1601);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1666 = lean_ctor_get(x_1623, 0);
lean_inc(x_1666);
x_1667 = lean_ctor_get(x_1623, 1);
lean_inc(x_1667);
lean_dec(x_1623);
x_8 = x_1666;
x_9 = x_1667;
goto block_16;
}
}
else
{
lean_object* x_1668; lean_object* x_1669; 
lean_dec(x_1605);
lean_dec(x_1603);
lean_dec(x_1601);
lean_dec(x_1590);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1668 = lean_ctor_get(x_1606, 0);
lean_inc(x_1668);
x_1669 = lean_ctor_get(x_1606, 1);
lean_inc(x_1669);
lean_dec(x_1606);
x_8 = x_1668;
x_9 = x_1669;
goto block_16;
}
}
else
{
lean_object* x_1670; lean_object* x_1671; 
lean_dec(x_1601);
lean_dec(x_1590);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1670 = lean_ctor_get(x_1602, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1602, 1);
lean_inc(x_1671);
lean_dec(x_1602);
x_8 = x_1670;
x_9 = x_1671;
goto block_16;
}
}
}
else
{
lean_object* x_1672; lean_object* x_1673; 
lean_dec(x_1590);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1672 = lean_ctor_get(x_1595, 0);
lean_inc(x_1672);
x_1673 = lean_ctor_get(x_1595, 1);
lean_inc(x_1673);
lean_dec(x_1595);
x_8 = x_1672;
x_9 = x_1673;
goto block_16;
}
}
else
{
lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; 
lean_dec(x_1590);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1674 = lean_ctor_get(x_1591, 1);
lean_inc(x_1674);
if (lean_is_exclusive(x_1591)) {
 lean_ctor_release(x_1591, 0);
 lean_ctor_release(x_1591, 1);
 x_1675 = x_1591;
} else {
 lean_dec_ref(x_1591);
 x_1675 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_1586);
if (lean_is_scalar(x_1675)) {
 x_1676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1676 = x_1675;
}
lean_ctor_set(x_1676, 0, x_43);
lean_ctor_set(x_1676, 1, x_1674);
return x_1676;
}
}
else
{
lean_object* x_1677; lean_object* x_1678; 
lean_dec(x_1590);
lean_dec(x_1586);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1677 = lean_ctor_get(x_1591, 0);
lean_inc(x_1677);
x_1678 = lean_ctor_get(x_1591, 1);
lean_inc(x_1678);
lean_dec(x_1591);
x_8 = x_1677;
x_9 = x_1678;
goto block_16;
}
}
else
{
lean_object* x_1679; lean_object* x_1680; 
lean_dec(x_1586);
lean_dec(x_51);
lean_dec(x_1581);
lean_dec(x_1566);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1679 = lean_ctor_get(x_1587, 0);
lean_inc(x_1679);
x_1680 = lean_ctor_get(x_1587, 1);
lean_inc(x_1680);
lean_dec(x_1587);
x_8 = x_1679;
x_9 = x_1680;
goto block_16;
}
}
else
{
lean_object* x_1681; lean_object* x_1682; 
lean_dec(x_1574);
lean_dec(x_1572);
lean_dec(x_1570);
lean_dec(x_1568);
lean_dec(x_1566);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1681 = lean_ctor_get(x_1575, 0);
lean_inc(x_1681);
x_1682 = lean_ctor_get(x_1575, 1);
lean_inc(x_1682);
lean_dec(x_1575);
x_8 = x_1681;
x_9 = x_1682;
goto block_16;
}
}
else
{
lean_object* x_1683; lean_object* x_1684; 
lean_dec(x_1570);
lean_dec(x_1568);
lean_dec(x_1566);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1683 = lean_ctor_get(x_1571, 0);
lean_inc(x_1683);
x_1684 = lean_ctor_get(x_1571, 1);
lean_inc(x_1684);
lean_dec(x_1571);
x_8 = x_1683;
x_9 = x_1684;
goto block_16;
}
}
else
{
lean_object* x_1685; lean_object* x_1686; 
lean_dec(x_1566);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1685 = lean_ctor_get(x_1567, 0);
lean_inc(x_1685);
x_1686 = lean_ctor_get(x_1567, 1);
lean_inc(x_1686);
lean_dec(x_1567);
x_8 = x_1685;
x_9 = x_1686;
goto block_16;
}
}
else
{
lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
lean_dec(x_1564);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1687 = lean_ctor_get(x_1563, 1);
lean_inc(x_1687);
if (lean_is_exclusive(x_1563)) {
 lean_ctor_release(x_1563, 0);
 lean_ctor_release(x_1563, 1);
 x_1688 = x_1563;
} else {
 lean_dec_ref(x_1563);
 x_1688 = lean_box(0);
}
if (lean_is_scalar(x_1688)) {
 x_1689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1689 = x_1688;
}
lean_ctor_set(x_1689, 0, x_1562);
lean_ctor_set(x_1689, 1, x_1687);
return x_1689;
}
}
else
{
lean_object* x_1690; lean_object* x_1691; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1690 = lean_ctor_get(x_1563, 0);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1563, 1);
lean_inc(x_1691);
lean_dec(x_1563);
x_8 = x_1690;
x_9 = x_1691;
goto block_16;
}
}
else
{
lean_object* x_1692; lean_object* x_1693; 
lean_dec(x_1548);
lean_dec(x_1546);
lean_dec(x_1535);
lean_dec(x_1531);
lean_dec(x_1529);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1692 = lean_ctor_get(x_1549, 0);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1549, 1);
lean_inc(x_1693);
lean_dec(x_1549);
x_8 = x_1692;
x_9 = x_1693;
goto block_16;
}
}
else
{
lean_object* x_1694; lean_object* x_1695; 
lean_dec(x_1535);
lean_dec(x_1531);
lean_dec(x_1529);
lean_dec(x_1527);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1694 = lean_ctor_get(x_1545, 0);
lean_inc(x_1694);
x_1695 = lean_ctor_get(x_1545, 1);
lean_inc(x_1695);
lean_dec(x_1545);
x_8 = x_1694;
x_9 = x_1695;
goto block_16;
}
}
}
else
{
lean_object* x_1696; lean_object* x_1697; 
lean_dec(x_1535);
lean_dec(x_1531);
lean_dec(x_1529);
lean_dec(x_1527);
lean_dec(x_1517);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1696 = lean_ctor_get(x_1537, 0);
lean_inc(x_1696);
x_1697 = lean_ctor_get(x_1537, 1);
lean_inc(x_1697);
lean_dec(x_1537);
x_8 = x_1696;
x_9 = x_1697;
goto block_16;
}
}
else
{
lean_object* x_1698; lean_object* x_1699; 
lean_dec(x_1531);
lean_dec(x_1529);
lean_dec(x_1527);
lean_dec(x_1517);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1698 = lean_ctor_get(x_1532, 0);
lean_inc(x_1698);
x_1699 = lean_ctor_get(x_1532, 1);
lean_inc(x_1699);
lean_dec(x_1532);
x_8 = x_1698;
x_9 = x_1699;
goto block_16;
}
}
else
{
lean_object* x_1700; lean_object* x_1701; 
lean_dec(x_1527);
lean_dec(x_1526);
lean_dec(x_1517);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1700 = lean_ctor_get(x_1528, 0);
lean_inc(x_1700);
x_1701 = lean_ctor_get(x_1528, 1);
lean_inc(x_1701);
lean_dec(x_1528);
x_8 = x_1700;
x_9 = x_1701;
goto block_16;
}
}
else
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; 
lean_dec(x_1524);
lean_dec(x_1523);
lean_dec(x_1517);
lean_dec(x_1516);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1702 = lean_ctor_get(x_1521, 1);
lean_inc(x_1702);
if (lean_is_exclusive(x_1521)) {
 lean_ctor_release(x_1521, 0);
 lean_ctor_release(x_1521, 1);
 x_1703 = x_1521;
} else {
 lean_dec_ref(x_1521);
 x_1703 = lean_box(0);
}
x_1704 = lean_box(0);
if (lean_is_scalar(x_1703)) {
 x_1705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1705 = x_1703;
}
lean_ctor_set(x_1705, 0, x_1704);
lean_ctor_set(x_1705, 1, x_1702);
return x_1705;
}
}
else
{
lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; 
lean_dec(x_1523);
lean_dec(x_1522);
lean_dec(x_1517);
lean_dec(x_1516);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1706 = lean_ctor_get(x_1521, 1);
lean_inc(x_1706);
if (lean_is_exclusive(x_1521)) {
 lean_ctor_release(x_1521, 0);
 lean_ctor_release(x_1521, 1);
 x_1707 = x_1521;
} else {
 lean_dec_ref(x_1521);
 x_1707 = lean_box(0);
}
x_1708 = lean_box(0);
if (lean_is_scalar(x_1707)) {
 x_1709 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1709 = x_1707;
}
lean_ctor_set(x_1709, 0, x_1708);
lean_ctor_set(x_1709, 1, x_1706);
return x_1709;
}
}
else
{
lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; 
lean_dec(x_1522);
lean_dec(x_1517);
lean_dec(x_1516);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1710 = lean_ctor_get(x_1521, 1);
lean_inc(x_1710);
if (lean_is_exclusive(x_1521)) {
 lean_ctor_release(x_1521, 0);
 lean_ctor_release(x_1521, 1);
 x_1711 = x_1521;
} else {
 lean_dec_ref(x_1521);
 x_1711 = lean_box(0);
}
x_1712 = lean_box(0);
if (lean_is_scalar(x_1711)) {
 x_1713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1713 = x_1711;
}
lean_ctor_set(x_1713, 0, x_1712);
lean_ctor_set(x_1713, 1, x_1710);
return x_1713;
}
}
else
{
lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; uint8_t x_1717; 
lean_dec(x_1517);
lean_dec(x_1516);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1714 = lean_ctor_get(x_1521, 0);
lean_inc(x_1714);
x_1715 = lean_ctor_get(x_1521, 1);
lean_inc(x_1715);
if (lean_is_exclusive(x_1521)) {
 lean_ctor_release(x_1521, 0);
 lean_ctor_release(x_1521, 1);
 x_1716 = x_1521;
} else {
 lean_dec_ref(x_1521);
 x_1716 = lean_box(0);
}
x_1717 = l_Lean_Exception_isInterrupt(x_1714);
if (x_1717 == 0)
{
uint8_t x_1718; 
x_1718 = l_Lean_Exception_isRuntime(x_1714);
if (x_1718 == 0)
{
lean_object* x_1719; lean_object* x_1720; 
lean_dec(x_1714);
x_1719 = lean_box(0);
if (lean_is_scalar(x_1716)) {
 x_1720 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1720 = x_1716;
 lean_ctor_set_tag(x_1720, 0);
}
lean_ctor_set(x_1720, 0, x_1719);
lean_ctor_set(x_1720, 1, x_1715);
return x_1720;
}
else
{
lean_object* x_1721; 
if (lean_is_scalar(x_1716)) {
 x_1721 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1721 = x_1716;
}
lean_ctor_set(x_1721, 0, x_1714);
lean_ctor_set(x_1721, 1, x_1715);
return x_1721;
}
}
else
{
lean_object* x_1722; 
if (lean_is_scalar(x_1716)) {
 x_1722 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1722 = x_1716;
}
lean_ctor_set(x_1722, 0, x_1714);
lean_ctor_set(x_1722, 1, x_1715);
return x_1722;
}
}
}
else
{
lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; uint8_t x_1726; 
lean_dec(x_1517);
lean_dec(x_1516);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1723 = lean_ctor_get(x_1518, 0);
lean_inc(x_1723);
x_1724 = lean_ctor_get(x_1518, 1);
lean_inc(x_1724);
if (lean_is_exclusive(x_1518)) {
 lean_ctor_release(x_1518, 0);
 lean_ctor_release(x_1518, 1);
 x_1725 = x_1518;
} else {
 lean_dec_ref(x_1518);
 x_1725 = lean_box(0);
}
x_1726 = l_Lean_Exception_isInterrupt(x_1723);
if (x_1726 == 0)
{
uint8_t x_1727; 
x_1727 = l_Lean_Exception_isRuntime(x_1723);
if (x_1727 == 0)
{
lean_object* x_1728; lean_object* x_1729; 
lean_dec(x_1723);
x_1728 = lean_box(0);
if (lean_is_scalar(x_1725)) {
 x_1729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1729 = x_1725;
 lean_ctor_set_tag(x_1729, 0);
}
lean_ctor_set(x_1729, 0, x_1728);
lean_ctor_set(x_1729, 1, x_1724);
return x_1729;
}
else
{
lean_object* x_1730; 
if (lean_is_scalar(x_1725)) {
 x_1730 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1730 = x_1725;
}
lean_ctor_set(x_1730, 0, x_1723);
lean_ctor_set(x_1730, 1, x_1724);
return x_1730;
}
}
else
{
lean_object* x_1731; 
if (lean_is_scalar(x_1725)) {
 x_1731 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1731 = x_1725;
}
lean_ctor_set(x_1731, 0, x_1723);
lean_ctor_set(x_1731, 1, x_1724);
return x_1731;
}
}
}
else
{
lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; 
lean_dec(x_1514);
lean_dec(x_1513);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1732 = lean_ctor_get(x_1511, 1);
lean_inc(x_1732);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 lean_ctor_release(x_1511, 1);
 x_1733 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1733 = lean_box(0);
}
x_1734 = lean_box(0);
if (lean_is_scalar(x_1733)) {
 x_1735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1735 = x_1733;
}
lean_ctor_set(x_1735, 0, x_1734);
lean_ctor_set(x_1735, 1, x_1732);
return x_1735;
}
}
else
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; 
lean_dec(x_1513);
lean_dec(x_1512);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1736 = lean_ctor_get(x_1511, 1);
lean_inc(x_1736);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 lean_ctor_release(x_1511, 1);
 x_1737 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1737 = lean_box(0);
}
x_1738 = lean_box(0);
if (lean_is_scalar(x_1737)) {
 x_1739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1739 = x_1737;
}
lean_ctor_set(x_1739, 0, x_1738);
lean_ctor_set(x_1739, 1, x_1736);
return x_1739;
}
}
else
{
lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; 
lean_dec(x_1512);
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1740 = lean_ctor_get(x_1511, 1);
lean_inc(x_1740);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 lean_ctor_release(x_1511, 1);
 x_1741 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1741 = lean_box(0);
}
x_1742 = lean_box(0);
if (lean_is_scalar(x_1741)) {
 x_1743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1743 = x_1741;
}
lean_ctor_set(x_1743, 0, x_1742);
lean_ctor_set(x_1743, 1, x_1740);
return x_1743;
}
}
else
{
lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; uint8_t x_1747; 
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1744 = lean_ctor_get(x_1511, 0);
lean_inc(x_1744);
x_1745 = lean_ctor_get(x_1511, 1);
lean_inc(x_1745);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 lean_ctor_release(x_1511, 1);
 x_1746 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1746 = lean_box(0);
}
x_1747 = l_Lean_Exception_isInterrupt(x_1744);
if (x_1747 == 0)
{
uint8_t x_1748; 
x_1748 = l_Lean_Exception_isRuntime(x_1744);
if (x_1748 == 0)
{
lean_object* x_1749; lean_object* x_1750; 
lean_dec(x_1744);
x_1749 = lean_box(0);
if (lean_is_scalar(x_1746)) {
 x_1750 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1750 = x_1746;
 lean_ctor_set_tag(x_1750, 0);
}
lean_ctor_set(x_1750, 0, x_1749);
lean_ctor_set(x_1750, 1, x_1745);
return x_1750;
}
else
{
lean_object* x_1751; 
if (lean_is_scalar(x_1746)) {
 x_1751 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1751 = x_1746;
}
lean_ctor_set(x_1751, 0, x_1744);
lean_ctor_set(x_1751, 1, x_1745);
return x_1751;
}
}
else
{
lean_object* x_1752; 
if (lean_is_scalar(x_1746)) {
 x_1752 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1752 = x_1746;
}
lean_ctor_set(x_1752, 0, x_1744);
lean_ctor_set(x_1752, 1, x_1745);
return x_1752;
}
}
}
else
{
lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; uint8_t x_1756; 
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1753 = lean_ctor_get(x_1508, 0);
lean_inc(x_1753);
x_1754 = lean_ctor_get(x_1508, 1);
lean_inc(x_1754);
if (lean_is_exclusive(x_1508)) {
 lean_ctor_release(x_1508, 0);
 lean_ctor_release(x_1508, 1);
 x_1755 = x_1508;
} else {
 lean_dec_ref(x_1508);
 x_1755 = lean_box(0);
}
x_1756 = l_Lean_Exception_isInterrupt(x_1753);
if (x_1756 == 0)
{
uint8_t x_1757; 
x_1757 = l_Lean_Exception_isRuntime(x_1753);
if (x_1757 == 0)
{
lean_object* x_1758; lean_object* x_1759; 
lean_dec(x_1753);
x_1758 = lean_box(0);
if (lean_is_scalar(x_1755)) {
 x_1759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1759 = x_1755;
 lean_ctor_set_tag(x_1759, 0);
}
lean_ctor_set(x_1759, 0, x_1758);
lean_ctor_set(x_1759, 1, x_1754);
return x_1759;
}
else
{
lean_object* x_1760; 
if (lean_is_scalar(x_1755)) {
 x_1760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1760 = x_1755;
}
lean_ctor_set(x_1760, 0, x_1753);
lean_ctor_set(x_1760, 1, x_1754);
return x_1760;
}
}
else
{
lean_object* x_1761; 
if (lean_is_scalar(x_1755)) {
 x_1761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1761 = x_1755;
}
lean_ctor_set(x_1761, 0, x_1753);
lean_ctor_set(x_1761, 1, x_1754);
return x_1761;
}
}
}
}
}
else
{
lean_object* x_1762; lean_object* x_1763; 
lean_dec(x_26);
lean_dec(x_19);
x_1762 = lean_ctor_get(x_60, 1);
lean_inc(x_1762);
lean_dec(x_60);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1763 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_1762);
if (lean_obj_tag(x_1763) == 0)
{
lean_object* x_1764; 
x_1764 = lean_ctor_get(x_1763, 0);
lean_inc(x_1764);
if (lean_obj_tag(x_1764) == 0)
{
lean_object* x_1765; lean_object* x_1766; uint8_t x_1767; 
lean_free_object(x_56);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_1);
x_1765 = lean_ctor_get(x_1763, 1);
lean_inc(x_1765);
lean_dec(x_1763);
x_1766 = l_Lean_Meta_SavedState_restore(x_58, x_3, x_4, x_5, x_6, x_1765);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_58);
x_1767 = !lean_is_exclusive(x_1766);
if (x_1767 == 0)
{
lean_object* x_1768; lean_object* x_1769; 
x_1768 = lean_ctor_get(x_1766, 0);
lean_dec(x_1768);
x_1769 = lean_box(0);
lean_ctor_set(x_1766, 0, x_1769);
return x_1766;
}
else
{
lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; 
x_1770 = lean_ctor_get(x_1766, 1);
lean_inc(x_1770);
lean_dec(x_1766);
x_1771 = lean_box(0);
x_1772 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1772, 0, x_1771);
lean_ctor_set(x_1772, 1, x_1770);
return x_1772;
}
}
else
{
lean_object* x_1773; lean_object* x_1774; uint8_t x_1775; 
x_1773 = lean_ctor_get(x_1763, 1);
lean_inc(x_1773);
if (lean_is_exclusive(x_1763)) {
 lean_ctor_release(x_1763, 0);
 lean_ctor_release(x_1763, 1);
 x_1774 = x_1763;
} else {
 lean_dec_ref(x_1763);
 x_1774 = lean_box(0);
}
x_1775 = !lean_is_exclusive(x_1764);
if (x_1775 == 0)
{
lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1795; lean_object* x_1796; 
x_1776 = lean_ctor_get(x_1764, 0);
lean_ctor_set(x_1764, 0, x_54);
lean_ctor_set(x_43, 0, x_55);
lean_ctor_set(x_29, 0, x_41);
x_1777 = lean_box(0);
x_1778 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1778, 0, x_1776);
x_1779 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1779, 0, x_1);
x_1780 = lean_box(0);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_1780);
lean_ctor_set(x_56, 0, x_1779);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_56);
lean_ctor_set(x_51, 0, x_1778);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_1777);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_29);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_43);
x_1781 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1781, 0, x_1764);
lean_ctor_set(x_1781, 1, x_17);
x_1782 = lean_array_mk(x_1781);
x_1795 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1796 = l_Lean_Meta_mkAppOptM(x_1795, x_1782, x_3, x_4, x_5, x_6, x_1773);
if (lean_obj_tag(x_1796) == 0)
{
lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; 
x_1797 = lean_ctor_get(x_1796, 0);
lean_inc(x_1797);
x_1798 = lean_ctor_get(x_1796, 1);
lean_inc(x_1798);
lean_dec(x_1796);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1799 = l_Lean_Meta_expandCoe(x_1797, x_3, x_4, x_5, x_6, x_1798);
if (lean_obj_tag(x_1799) == 0)
{
uint8_t x_1800; 
lean_dec(x_1774);
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1800 = !lean_is_exclusive(x_1799);
if (x_1800 == 0)
{
lean_object* x_1801; lean_object* x_1802; 
x_1801 = lean_ctor_get(x_1799, 0);
x_1802 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1802, 0, x_1801);
lean_ctor_set(x_1799, 0, x_1802);
return x_1799;
}
else
{
lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; 
x_1803 = lean_ctor_get(x_1799, 0);
x_1804 = lean_ctor_get(x_1799, 1);
lean_inc(x_1804);
lean_inc(x_1803);
lean_dec(x_1799);
x_1805 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1805, 0, x_1803);
x_1806 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1806, 0, x_1805);
lean_ctor_set(x_1806, 1, x_1804);
return x_1806;
}
}
else
{
lean_object* x_1807; lean_object* x_1808; 
x_1807 = lean_ctor_get(x_1799, 0);
lean_inc(x_1807);
x_1808 = lean_ctor_get(x_1799, 1);
lean_inc(x_1808);
lean_dec(x_1799);
x_1783 = x_1807;
x_1784 = x_1808;
goto block_1794;
}
}
else
{
lean_object* x_1809; lean_object* x_1810; 
x_1809 = lean_ctor_get(x_1796, 0);
lean_inc(x_1809);
x_1810 = lean_ctor_get(x_1796, 1);
lean_inc(x_1810);
lean_dec(x_1796);
x_1783 = x_1809;
x_1784 = x_1810;
goto block_1794;
}
block_1794:
{
uint8_t x_1785; 
x_1785 = l_Lean_Exception_isInterrupt(x_1783);
if (x_1785 == 0)
{
uint8_t x_1786; 
x_1786 = l_Lean_Exception_isRuntime(x_1783);
if (x_1786 == 0)
{
lean_object* x_1787; uint8_t x_1788; 
lean_dec(x_1783);
lean_dec(x_1774);
x_1787 = l_Lean_Meta_SavedState_restore(x_58, x_3, x_4, x_5, x_6, x_1784);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_58);
x_1788 = !lean_is_exclusive(x_1787);
if (x_1788 == 0)
{
lean_object* x_1789; 
x_1789 = lean_ctor_get(x_1787, 0);
lean_dec(x_1789);
lean_ctor_set(x_1787, 0, x_1777);
return x_1787;
}
else
{
lean_object* x_1790; lean_object* x_1791; 
x_1790 = lean_ctor_get(x_1787, 1);
lean_inc(x_1790);
lean_dec(x_1787);
x_1791 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1791, 0, x_1777);
lean_ctor_set(x_1791, 1, x_1790);
return x_1791;
}
}
else
{
lean_object* x_1792; 
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_1774)) {
 x_1792 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1792 = x_1774;
 lean_ctor_set_tag(x_1792, 1);
}
lean_ctor_set(x_1792, 0, x_1783);
lean_ctor_set(x_1792, 1, x_1784);
return x_1792;
}
}
else
{
lean_object* x_1793; 
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_1774)) {
 x_1793 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1793 = x_1774;
 lean_ctor_set_tag(x_1793, 1);
}
lean_ctor_set(x_1793, 0, x_1783);
lean_ctor_set(x_1793, 1, x_1784);
return x_1793;
}
}
}
else
{
lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1830; lean_object* x_1831; 
x_1811 = lean_ctor_get(x_1764, 0);
lean_inc(x_1811);
lean_dec(x_1764);
x_1812 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1812, 0, x_54);
lean_ctor_set(x_43, 0, x_55);
lean_ctor_set(x_29, 0, x_41);
x_1813 = lean_box(0);
x_1814 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1814, 0, x_1811);
x_1815 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1815, 0, x_1);
x_1816 = lean_box(0);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_1816);
lean_ctor_set(x_56, 0, x_1815);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_56);
lean_ctor_set(x_51, 0, x_1814);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_1813);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_29);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_43);
x_1817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1817, 0, x_1812);
lean_ctor_set(x_1817, 1, x_17);
x_1818 = lean_array_mk(x_1817);
x_1830 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1831 = l_Lean_Meta_mkAppOptM(x_1830, x_1818, x_3, x_4, x_5, x_6, x_1773);
if (lean_obj_tag(x_1831) == 0)
{
lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; 
x_1832 = lean_ctor_get(x_1831, 0);
lean_inc(x_1832);
x_1833 = lean_ctor_get(x_1831, 1);
lean_inc(x_1833);
lean_dec(x_1831);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1834 = l_Lean_Meta_expandCoe(x_1832, x_3, x_4, x_5, x_6, x_1833);
if (lean_obj_tag(x_1834) == 0)
{
lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; 
lean_dec(x_1774);
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1835 = lean_ctor_get(x_1834, 0);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1834, 1);
lean_inc(x_1836);
if (lean_is_exclusive(x_1834)) {
 lean_ctor_release(x_1834, 0);
 lean_ctor_release(x_1834, 1);
 x_1837 = x_1834;
} else {
 lean_dec_ref(x_1834);
 x_1837 = lean_box(0);
}
x_1838 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1838, 0, x_1835);
if (lean_is_scalar(x_1837)) {
 x_1839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1839 = x_1837;
}
lean_ctor_set(x_1839, 0, x_1838);
lean_ctor_set(x_1839, 1, x_1836);
return x_1839;
}
else
{
lean_object* x_1840; lean_object* x_1841; 
x_1840 = lean_ctor_get(x_1834, 0);
lean_inc(x_1840);
x_1841 = lean_ctor_get(x_1834, 1);
lean_inc(x_1841);
lean_dec(x_1834);
x_1819 = x_1840;
x_1820 = x_1841;
goto block_1829;
}
}
else
{
lean_object* x_1842; lean_object* x_1843; 
x_1842 = lean_ctor_get(x_1831, 0);
lean_inc(x_1842);
x_1843 = lean_ctor_get(x_1831, 1);
lean_inc(x_1843);
lean_dec(x_1831);
x_1819 = x_1842;
x_1820 = x_1843;
goto block_1829;
}
block_1829:
{
uint8_t x_1821; 
x_1821 = l_Lean_Exception_isInterrupt(x_1819);
if (x_1821 == 0)
{
uint8_t x_1822; 
x_1822 = l_Lean_Exception_isRuntime(x_1819);
if (x_1822 == 0)
{
lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; 
lean_dec(x_1819);
lean_dec(x_1774);
x_1823 = l_Lean_Meta_SavedState_restore(x_58, x_3, x_4, x_5, x_6, x_1820);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_58);
x_1824 = lean_ctor_get(x_1823, 1);
lean_inc(x_1824);
if (lean_is_exclusive(x_1823)) {
 lean_ctor_release(x_1823, 0);
 lean_ctor_release(x_1823, 1);
 x_1825 = x_1823;
} else {
 lean_dec_ref(x_1823);
 x_1825 = lean_box(0);
}
if (lean_is_scalar(x_1825)) {
 x_1826 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1826 = x_1825;
}
lean_ctor_set(x_1826, 0, x_1813);
lean_ctor_set(x_1826, 1, x_1824);
return x_1826;
}
else
{
lean_object* x_1827; 
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_1774)) {
 x_1827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1827 = x_1774;
 lean_ctor_set_tag(x_1827, 1);
}
lean_ctor_set(x_1827, 0, x_1819);
lean_ctor_set(x_1827, 1, x_1820);
return x_1827;
}
}
else
{
lean_object* x_1828; 
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_1774)) {
 x_1828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1828 = x_1774;
 lean_ctor_set_tag(x_1828, 1);
}
lean_ctor_set(x_1828, 0, x_1819);
lean_ctor_set(x_1828, 1, x_1820);
return x_1828;
}
}
}
}
}
else
{
uint8_t x_1844; 
lean_free_object(x_56);
lean_dec(x_58);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1844 = !lean_is_exclusive(x_1763);
if (x_1844 == 0)
{
return x_1763;
}
else
{
lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; 
x_1845 = lean_ctor_get(x_1763, 0);
x_1846 = lean_ctor_get(x_1763, 1);
lean_inc(x_1846);
lean_inc(x_1845);
lean_dec(x_1763);
x_1847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1847, 0, x_1845);
lean_ctor_set(x_1847, 1, x_1846);
return x_1847;
}
}
}
}
else
{
uint8_t x_1848; 
lean_free_object(x_56);
lean_dec(x_58);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1848 = !lean_is_exclusive(x_60);
if (x_1848 == 0)
{
return x_60;
}
else
{
lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; 
x_1849 = lean_ctor_get(x_60, 0);
x_1850 = lean_ctor_get(x_60, 1);
lean_inc(x_1850);
lean_inc(x_1849);
lean_dec(x_60);
x_1851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1851, 0, x_1849);
lean_ctor_set(x_1851, 1, x_1850);
return x_1851;
}
}
}
else
{
lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; 
x_1852 = lean_ctor_get(x_56, 0);
x_1853 = lean_ctor_get(x_56, 1);
lean_inc(x_1853);
lean_inc(x_1852);
lean_dec(x_56);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
lean_inc(x_54);
x_1854 = l_Lean_Meta_isExprDefEq(x_54, x_40, x_3, x_4, x_5, x_6, x_1853);
if (lean_obj_tag(x_1854) == 0)
{
lean_object* x_1855; uint8_t x_1856; 
x_1855 = lean_ctor_get(x_1854, 0);
lean_inc(x_1855);
x_1856 = lean_unbox(x_1855);
lean_dec(x_1855);
if (x_1856 == 0)
{
lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; uint8_t x_1861; 
lean_dec(x_1852);
lean_free_object(x_29);
x_1857 = lean_ctor_get(x_1854, 1);
lean_inc(x_1857);
if (lean_is_exclusive(x_1854)) {
 lean_ctor_release(x_1854, 0);
 lean_ctor_release(x_1854, 1);
 x_1858 = x_1854;
} else {
 lean_dec_ref(x_1854);
 x_1858 = lean_box(0);
}
x_1859 = lean_ctor_get(x_5, 2);
lean_inc(x_1859);
x_1860 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1861 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1859, x_1860);
lean_dec(x_1859);
if (x_1861 == 0)
{
lean_object* x_1862; lean_object* x_1863; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1862 = lean_box(0);
if (lean_is_scalar(x_1858)) {
 x_1863 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1863 = x_1858;
}
lean_ctor_set(x_1863, 0, x_1862);
lean_ctor_set(x_1863, 1, x_1857);
return x_1863;
}
else
{
lean_object* x_1864; 
lean_dec(x_1858);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
x_1864 = lean_infer_type(x_54, x_3, x_4, x_5, x_6, x_1857);
if (lean_obj_tag(x_1864) == 0)
{
lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; 
x_1865 = lean_ctor_get(x_1864, 0);
lean_inc(x_1865);
x_1866 = lean_ctor_get(x_1864, 1);
lean_inc(x_1866);
lean_dec(x_1864);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1867 = lean_whnf(x_1865, x_3, x_4, x_5, x_6, x_1866);
if (lean_obj_tag(x_1867) == 0)
{
lean_object* x_1868; 
x_1868 = lean_ctor_get(x_1867, 0);
lean_inc(x_1868);
if (lean_obj_tag(x_1868) == 7)
{
lean_object* x_1869; 
x_1869 = lean_ctor_get(x_1868, 1);
lean_inc(x_1869);
if (lean_obj_tag(x_1869) == 3)
{
lean_object* x_1870; 
x_1870 = lean_ctor_get(x_1868, 2);
lean_inc(x_1870);
lean_dec(x_1868);
if (lean_obj_tag(x_1870) == 3)
{
lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
x_1871 = lean_ctor_get(x_1867, 1);
lean_inc(x_1871);
lean_dec(x_1867);
x_1872 = lean_ctor_get(x_1869, 0);
lean_inc(x_1872);
lean_dec(x_1869);
x_1873 = lean_ctor_get(x_1870, 0);
lean_inc(x_1873);
lean_dec(x_1870);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_1874 = lean_infer_type(x_40, x_3, x_4, x_5, x_6, x_1871);
if (lean_obj_tag(x_1874) == 0)
{
lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; 
x_1875 = lean_ctor_get(x_1874, 0);
lean_inc(x_1875);
x_1876 = lean_ctor_get(x_1874, 1);
lean_inc(x_1876);
lean_dec(x_1874);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1877 = lean_whnf(x_1875, x_3, x_4, x_5, x_6, x_1876);
if (lean_obj_tag(x_1877) == 0)
{
lean_object* x_1878; 
x_1878 = lean_ctor_get(x_1877, 0);
lean_inc(x_1878);
if (lean_obj_tag(x_1878) == 7)
{
lean_object* x_1879; 
x_1879 = lean_ctor_get(x_1878, 1);
lean_inc(x_1879);
if (lean_obj_tag(x_1879) == 3)
{
lean_object* x_1880; 
x_1880 = lean_ctor_get(x_1878, 2);
lean_inc(x_1880);
lean_dec(x_1878);
if (lean_obj_tag(x_1880) == 3)
{
lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; 
x_1881 = lean_ctor_get(x_1877, 1);
lean_inc(x_1881);
lean_dec(x_1877);
x_1882 = lean_ctor_get(x_1879, 0);
lean_inc(x_1882);
lean_dec(x_1879);
x_1883 = lean_ctor_get(x_1880, 0);
lean_inc(x_1883);
lean_dec(x_1880);
x_1884 = l_Lean_Meta_decLevel(x_1872, x_3, x_4, x_5, x_6, x_1881);
if (lean_obj_tag(x_1884) == 0)
{
lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; 
x_1885 = lean_ctor_get(x_1884, 0);
lean_inc(x_1885);
x_1886 = lean_ctor_get(x_1884, 1);
lean_inc(x_1886);
if (lean_is_exclusive(x_1884)) {
 lean_ctor_release(x_1884, 0);
 lean_ctor_release(x_1884, 1);
 x_1887 = x_1884;
} else {
 lean_dec_ref(x_1884);
 x_1887 = lean_box(0);
}
x_1888 = l_Lean_Meta_decLevel(x_1882, x_3, x_4, x_5, x_6, x_1886);
if (lean_obj_tag(x_1888) == 0)
{
lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; uint8_t x_1892; lean_object* x_1893; 
x_1889 = lean_ctor_get(x_1888, 0);
lean_inc(x_1889);
x_1890 = lean_ctor_get(x_1888, 1);
lean_inc(x_1890);
if (lean_is_exclusive(x_1888)) {
 lean_ctor_release(x_1888, 0);
 lean_ctor_release(x_1888, 1);
 x_1891 = x_1888;
} else {
 lean_dec_ref(x_1888);
 x_1891 = lean_box(0);
}
x_1892 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1885);
x_1893 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1885, x_1889, x_1892, x_3, x_4, x_5, x_6, x_1890);
if (lean_obj_tag(x_1893) == 0)
{
lean_object* x_1894; uint8_t x_1895; 
x_1894 = lean_ctor_get(x_1893, 0);
lean_inc(x_1894);
x_1895 = lean_unbox(x_1894);
lean_dec(x_1894);
if (x_1895 == 0)
{
lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; 
lean_dec(x_1891);
lean_dec(x_1887);
lean_dec(x_1885);
lean_dec(x_1883);
lean_dec(x_1873);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1896 = lean_ctor_get(x_1893, 1);
lean_inc(x_1896);
if (lean_is_exclusive(x_1893)) {
 lean_ctor_release(x_1893, 0);
 lean_ctor_release(x_1893, 1);
 x_1897 = x_1893;
} else {
 lean_dec_ref(x_1893);
 x_1897 = lean_box(0);
}
x_1898 = lean_box(0);
if (lean_is_scalar(x_1897)) {
 x_1899 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1899 = x_1897;
}
lean_ctor_set(x_1899, 0, x_1898);
lean_ctor_set(x_1899, 1, x_1896);
return x_1899;
}
else
{
lean_object* x_1900; lean_object* x_1901; 
x_1900 = lean_ctor_get(x_1893, 1);
lean_inc(x_1900);
lean_dec(x_1893);
x_1901 = l_Lean_Meta_decLevel(x_1873, x_3, x_4, x_5, x_6, x_1900);
if (lean_obj_tag(x_1901) == 0)
{
lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; 
x_1902 = lean_ctor_get(x_1901, 0);
lean_inc(x_1902);
x_1903 = lean_ctor_get(x_1901, 1);
lean_inc(x_1903);
if (lean_is_exclusive(x_1901)) {
 lean_ctor_release(x_1901, 0);
 lean_ctor_release(x_1901, 1);
 x_1904 = x_1901;
} else {
 lean_dec_ref(x_1901);
 x_1904 = lean_box(0);
}
x_1905 = l_Lean_Meta_decLevel(x_1883, x_3, x_4, x_5, x_6, x_1903);
if (lean_obj_tag(x_1905) == 0)
{
lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; 
x_1906 = lean_ctor_get(x_1905, 0);
lean_inc(x_1906);
x_1907 = lean_ctor_get(x_1905, 1);
lean_inc(x_1907);
if (lean_is_exclusive(x_1905)) {
 lean_ctor_release(x_1905, 0);
 lean_ctor_release(x_1905, 1);
 x_1908 = x_1905;
} else {
 lean_dec_ref(x_1905);
 x_1908 = lean_box(0);
}
x_1909 = lean_box(0);
if (lean_is_scalar(x_1908)) {
 x_1910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1910 = x_1908;
 lean_ctor_set_tag(x_1910, 1);
}
lean_ctor_set(x_1910, 0, x_1906);
lean_ctor_set(x_1910, 1, x_1909);
if (lean_is_scalar(x_1904)) {
 x_1911 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1911 = x_1904;
 lean_ctor_set_tag(x_1911, 1);
}
lean_ctor_set(x_1911, 0, x_1902);
lean_ctor_set(x_1911, 1, x_1910);
if (lean_is_scalar(x_1891)) {
 x_1912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1912 = x_1891;
 lean_ctor_set_tag(x_1912, 1);
}
lean_ctor_set(x_1912, 0, x_1885);
lean_ctor_set(x_1912, 1, x_1911);
x_1913 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1914 = l_Lean_Expr_const___override(x_1913, x_1912);
lean_inc(x_40);
if (lean_is_scalar(x_1887)) {
 x_1915 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1915 = x_1887;
 lean_ctor_set_tag(x_1915, 1);
}
lean_ctor_set(x_1915, 0, x_40);
lean_ctor_set(x_1915, 1, x_1909);
lean_inc(x_54);
x_1916 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1916, 0, x_54);
lean_ctor_set(x_1916, 1, x_1915);
x_1917 = lean_array_mk(x_1916);
x_1918 = l_Lean_mkAppN(x_1914, x_1917);
lean_dec(x_1917);
x_1919 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1920 = l_Lean_Meta_trySynthInstance(x_1918, x_1919, x_3, x_4, x_5, x_6, x_1907);
if (lean_obj_tag(x_1920) == 0)
{
lean_object* x_1921; 
x_1921 = lean_ctor_get(x_1920, 0);
lean_inc(x_1921);
if (lean_obj_tag(x_1921) == 1)
{
lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; 
x_1922 = lean_ctor_get(x_1920, 1);
lean_inc(x_1922);
lean_dec(x_1920);
x_1923 = lean_ctor_get(x_1921, 0);
lean_inc(x_1923);
lean_dec(x_1921);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1924 = l_Lean_Meta_getDecLevel(x_55, x_3, x_4, x_5, x_6, x_1922);
if (lean_obj_tag(x_1924) == 0)
{
lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; 
x_1925 = lean_ctor_get(x_1924, 0);
lean_inc(x_1925);
x_1926 = lean_ctor_get(x_1924, 1);
lean_inc(x_1926);
if (lean_is_exclusive(x_1924)) {
 lean_ctor_release(x_1924, 0);
 lean_ctor_release(x_1924, 1);
 x_1927 = x_1924;
} else {
 lean_dec_ref(x_1924);
 x_1927 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1928 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_1926);
if (lean_obj_tag(x_1928) == 0)
{
lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; 
x_1929 = lean_ctor_get(x_1928, 0);
lean_inc(x_1929);
x_1930 = lean_ctor_get(x_1928, 1);
lean_inc(x_1930);
if (lean_is_exclusive(x_1928)) {
 lean_ctor_release(x_1928, 0);
 lean_ctor_release(x_1928, 1);
 x_1931 = x_1928;
} else {
 lean_dec_ref(x_1928);
 x_1931 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_1932 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_1930);
if (lean_obj_tag(x_1932) == 0)
{
lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; 
x_1933 = lean_ctor_get(x_1932, 0);
lean_inc(x_1933);
x_1934 = lean_ctor_get(x_1932, 1);
lean_inc(x_1934);
if (lean_is_exclusive(x_1932)) {
 lean_ctor_release(x_1932, 0);
 lean_ctor_release(x_1932, 1);
 x_1935 = x_1932;
} else {
 lean_dec_ref(x_1932);
 x_1935 = lean_box(0);
}
if (lean_is_scalar(x_1935)) {
 x_1936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1936 = x_1935;
 lean_ctor_set_tag(x_1936, 1);
}
lean_ctor_set(x_1936, 0, x_1933);
lean_ctor_set(x_1936, 1, x_1909);
if (lean_is_scalar(x_1931)) {
 x_1937 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1937 = x_1931;
 lean_ctor_set_tag(x_1937, 1);
}
lean_ctor_set(x_1937, 0, x_1929);
lean_ctor_set(x_1937, 1, x_1936);
if (lean_is_scalar(x_1927)) {
 x_1938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1938 = x_1927;
 lean_ctor_set_tag(x_1938, 1);
}
lean_ctor_set(x_1938, 0, x_1925);
lean_ctor_set(x_1938, 1, x_1937);
x_1939 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_1938);
x_1940 = l_Lean_Expr_const___override(x_1939, x_1938);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_1909);
lean_ctor_set(x_51, 0, x_1);
lean_inc(x_51);
lean_inc(x_55);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_55);
lean_inc(x_1923);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_1923);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_54);
x_1941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1941, 0, x_54);
lean_ctor_set(x_1941, 1, x_17);
x_1942 = lean_array_mk(x_1941);
x_1943 = l_Lean_mkAppN(x_1940, x_1942);
lean_dec(x_1942);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1943);
x_1944 = lean_infer_type(x_1943, x_3, x_4, x_5, x_6, x_1934);
if (lean_obj_tag(x_1944) == 0)
{
lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; 
x_1945 = lean_ctor_get(x_1944, 0);
lean_inc(x_1945);
x_1946 = lean_ctor_get(x_1944, 1);
lean_inc(x_1946);
if (lean_is_exclusive(x_1944)) {
 lean_ctor_release(x_1944, 0);
 lean_ctor_release(x_1944, 1);
 x_1947 = x_1944;
} else {
 lean_dec_ref(x_1944);
 x_1947 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_1948 = l_Lean_Meta_isExprDefEq(x_19, x_1945, x_3, x_4, x_5, x_6, x_1946);
if (lean_obj_tag(x_1948) == 0)
{
lean_object* x_1949; uint8_t x_1950; 
x_1949 = lean_ctor_get(x_1948, 0);
lean_inc(x_1949);
x_1950 = lean_unbox(x_1949);
lean_dec(x_1949);
if (x_1950 == 0)
{
lean_object* x_1951; lean_object* x_1952; 
lean_dec(x_1943);
lean_free_object(x_43);
x_1951 = lean_ctor_get(x_1948, 1);
lean_inc(x_1951);
lean_dec(x_1948);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_1952 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_1951);
if (lean_obj_tag(x_1952) == 0)
{
lean_object* x_1953; 
x_1953 = lean_ctor_get(x_1952, 0);
lean_inc(x_1953);
if (lean_obj_tag(x_1953) == 0)
{
lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; 
lean_dec(x_1947);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1954 = lean_ctor_get(x_1952, 1);
lean_inc(x_1954);
if (lean_is_exclusive(x_1952)) {
 lean_ctor_release(x_1952, 0);
 lean_ctor_release(x_1952, 1);
 x_1955 = x_1952;
} else {
 lean_dec_ref(x_1952);
 x_1955 = lean_box(0);
}
if (lean_is_scalar(x_1955)) {
 x_1956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1956 = x_1955;
}
lean_ctor_set(x_1956, 0, x_1919);
lean_ctor_set(x_1956, 1, x_1954);
return x_1956;
}
else
{
lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; 
x_1957 = lean_ctor_get(x_1952, 1);
lean_inc(x_1957);
lean_dec(x_1952);
x_1958 = lean_ctor_get(x_1953, 0);
lean_inc(x_1958);
lean_dec(x_1953);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
x_1959 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_1957);
if (lean_obj_tag(x_1959) == 0)
{
lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; 
x_1960 = lean_ctor_get(x_1959, 0);
lean_inc(x_1960);
x_1961 = lean_ctor_get(x_1959, 1);
lean_inc(x_1961);
if (lean_is_exclusive(x_1959)) {
 lean_ctor_release(x_1959, 0);
 lean_ctor_release(x_1959, 1);
 x_1962 = x_1959;
} else {
 lean_dec_ref(x_1959);
 x_1962 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_1963 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_1961);
if (lean_obj_tag(x_1963) == 0)
{
lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; uint8_t x_1978; lean_object* x_1979; lean_object* x_1980; 
x_1964 = lean_ctor_get(x_1963, 0);
lean_inc(x_1964);
x_1965 = lean_ctor_get(x_1963, 1);
lean_inc(x_1965);
if (lean_is_exclusive(x_1963)) {
 lean_ctor_release(x_1963, 0);
 lean_ctor_release(x_1963, 1);
 x_1966 = x_1963;
} else {
 lean_dec_ref(x_1963);
 x_1966 = lean_box(0);
}
if (lean_is_scalar(x_1966)) {
 x_1967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1967 = x_1966;
 lean_ctor_set_tag(x_1967, 1);
}
lean_ctor_set(x_1967, 0, x_1964);
lean_ctor_set(x_1967, 1, x_1909);
if (lean_is_scalar(x_1962)) {
 x_1968 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1968 = x_1962;
 lean_ctor_set_tag(x_1968, 1);
}
lean_ctor_set(x_1968, 0, x_1960);
lean_ctor_set(x_1968, 1, x_1967);
x_1969 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1970 = l_Lean_Expr_const___override(x_1969, x_1968);
lean_inc(x_41);
if (lean_is_scalar(x_1947)) {
 x_1971 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1971 = x_1947;
 lean_ctor_set_tag(x_1971, 1);
}
lean_ctor_set(x_1971, 0, x_41);
lean_ctor_set(x_1971, 1, x_1909);
x_1972 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_1973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1973, 0, x_1972);
lean_ctor_set(x_1973, 1, x_1971);
lean_inc(x_55);
x_1974 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1974, 0, x_55);
lean_ctor_set(x_1974, 1, x_1973);
x_1975 = lean_array_mk(x_1974);
x_1976 = l_Lean_mkAppN(x_1970, x_1975);
lean_dec(x_1975);
x_1977 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_1978 = 0;
lean_inc(x_55);
x_1979 = l_Lean_Expr_forallE___override(x_1977, x_55, x_1976, x_1978);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1980 = l_Lean_Meta_trySynthInstance(x_1979, x_1919, x_3, x_4, x_5, x_6, x_1965);
if (lean_obj_tag(x_1980) == 0)
{
lean_object* x_1981; 
x_1981 = lean_ctor_get(x_1980, 0);
lean_inc(x_1981);
if (lean_obj_tag(x_1981) == 1)
{
lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; 
x_1982 = lean_ctor_get(x_1980, 1);
lean_inc(x_1982);
lean_dec(x_1980);
x_1983 = lean_ctor_get(x_1981, 0);
lean_inc(x_1983);
lean_dec(x_1981);
x_1984 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_1985 = l_Lean_Expr_const___override(x_1984, x_1938);
x_1986 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1986, 0, x_1958);
lean_ctor_set(x_1986, 1, x_51);
x_1987 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1987, 0, x_1983);
lean_ctor_set(x_1987, 1, x_1986);
x_1988 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1988, 0, x_1923);
lean_ctor_set(x_1988, 1, x_1987);
x_1989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1989, 0, x_41);
lean_ctor_set(x_1989, 1, x_1988);
x_1990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1990, 0, x_55);
lean_ctor_set(x_1990, 1, x_1989);
x_1991 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1991, 0, x_40);
lean_ctor_set(x_1991, 1, x_1990);
x_1992 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1992, 0, x_54);
lean_ctor_set(x_1992, 1, x_1991);
x_1993 = lean_array_mk(x_1992);
x_1994 = l_Lean_mkAppN(x_1985, x_1993);
lean_dec(x_1993);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1995 = l_Lean_Meta_expandCoe(x_1994, x_3, x_4, x_5, x_6, x_1982);
if (lean_obj_tag(x_1995) == 0)
{
lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; 
x_1996 = lean_ctor_get(x_1995, 0);
lean_inc(x_1996);
x_1997 = lean_ctor_get(x_1995, 1);
lean_inc(x_1997);
lean_dec(x_1995);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1996);
x_1998 = lean_infer_type(x_1996, x_3, x_4, x_5, x_6, x_1997);
if (lean_obj_tag(x_1998) == 0)
{
lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; 
x_1999 = lean_ctor_get(x_1998, 0);
lean_inc(x_1999);
x_2000 = lean_ctor_get(x_1998, 1);
lean_inc(x_2000);
lean_dec(x_1998);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2001 = l_Lean_Meta_isExprDefEq(x_19, x_1999, x_3, x_4, x_5, x_6, x_2000);
if (lean_obj_tag(x_2001) == 0)
{
lean_object* x_2002; uint8_t x_2003; 
x_2002 = lean_ctor_get(x_2001, 0);
lean_inc(x_2002);
x_2003 = lean_unbox(x_2002);
lean_dec(x_2002);
if (x_2003 == 0)
{
lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; 
lean_dec(x_1996);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2004 = lean_ctor_get(x_2001, 1);
lean_inc(x_2004);
if (lean_is_exclusive(x_2001)) {
 lean_ctor_release(x_2001, 0);
 lean_ctor_release(x_2001, 1);
 x_2005 = x_2001;
} else {
 lean_dec_ref(x_2001);
 x_2005 = lean_box(0);
}
if (lean_is_scalar(x_2005)) {
 x_2006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2006 = x_2005;
}
lean_ctor_set(x_2006, 0, x_1919);
lean_ctor_set(x_2006, 1, x_2004);
return x_2006;
}
else
{
lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; 
x_2007 = lean_ctor_get(x_2001, 1);
lean_inc(x_2007);
lean_dec(x_2001);
x_2008 = lean_box(0);
x_2009 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1996, x_2008, x_3, x_4, x_5, x_6, x_2007);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2010 = lean_ctor_get(x_2009, 0);
lean_inc(x_2010);
x_2011 = lean_ctor_get(x_2009, 1);
lean_inc(x_2011);
if (lean_is_exclusive(x_2009)) {
 lean_ctor_release(x_2009, 0);
 lean_ctor_release(x_2009, 1);
 x_2012 = x_2009;
} else {
 lean_dec_ref(x_2009);
 x_2012 = lean_box(0);
}
if (lean_is_scalar(x_2012)) {
 x_2013 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2013 = x_2012;
}
lean_ctor_set(x_2013, 0, x_2010);
lean_ctor_set(x_2013, 1, x_2011);
return x_2013;
}
}
else
{
lean_object* x_2014; lean_object* x_2015; 
lean_dec(x_1996);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2014 = lean_ctor_get(x_2001, 0);
lean_inc(x_2014);
x_2015 = lean_ctor_get(x_2001, 1);
lean_inc(x_2015);
lean_dec(x_2001);
x_8 = x_2014;
x_9 = x_2015;
goto block_16;
}
}
else
{
lean_object* x_2016; lean_object* x_2017; 
lean_dec(x_1996);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2016 = lean_ctor_get(x_1998, 0);
lean_inc(x_2016);
x_2017 = lean_ctor_get(x_1998, 1);
lean_inc(x_2017);
lean_dec(x_1998);
x_8 = x_2016;
x_9 = x_2017;
goto block_16;
}
}
else
{
lean_object* x_2018; lean_object* x_2019; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2018 = lean_ctor_get(x_1995, 0);
lean_inc(x_2018);
x_2019 = lean_ctor_get(x_1995, 1);
lean_inc(x_2019);
lean_dec(x_1995);
x_8 = x_2018;
x_9 = x_2019;
goto block_16;
}
}
else
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; 
lean_dec(x_1981);
lean_dec(x_1958);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2020 = lean_ctor_get(x_1980, 1);
lean_inc(x_2020);
if (lean_is_exclusive(x_1980)) {
 lean_ctor_release(x_1980, 0);
 lean_ctor_release(x_1980, 1);
 x_2021 = x_1980;
} else {
 lean_dec_ref(x_1980);
 x_2021 = lean_box(0);
}
if (lean_is_scalar(x_2021)) {
 x_2022 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2022 = x_2021;
}
lean_ctor_set(x_2022, 0, x_1919);
lean_ctor_set(x_2022, 1, x_2020);
return x_2022;
}
}
else
{
lean_object* x_2023; lean_object* x_2024; 
lean_dec(x_1958);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2023 = lean_ctor_get(x_1980, 0);
lean_inc(x_2023);
x_2024 = lean_ctor_get(x_1980, 1);
lean_inc(x_2024);
lean_dec(x_1980);
x_8 = x_2023;
x_9 = x_2024;
goto block_16;
}
}
else
{
lean_object* x_2025; lean_object* x_2026; 
lean_dec(x_1962);
lean_dec(x_1960);
lean_dec(x_1958);
lean_dec(x_1947);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2025 = lean_ctor_get(x_1963, 0);
lean_inc(x_2025);
x_2026 = lean_ctor_get(x_1963, 1);
lean_inc(x_2026);
lean_dec(x_1963);
x_8 = x_2025;
x_9 = x_2026;
goto block_16;
}
}
else
{
lean_object* x_2027; lean_object* x_2028; 
lean_dec(x_1958);
lean_dec(x_1947);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2027 = lean_ctor_get(x_1959, 0);
lean_inc(x_2027);
x_2028 = lean_ctor_get(x_1959, 1);
lean_inc(x_2028);
lean_dec(x_1959);
x_8 = x_2027;
x_9 = x_2028;
goto block_16;
}
}
}
else
{
lean_object* x_2029; lean_object* x_2030; 
lean_dec(x_1947);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2029 = lean_ctor_get(x_1952, 0);
lean_inc(x_2029);
x_2030 = lean_ctor_get(x_1952, 1);
lean_inc(x_2030);
lean_dec(x_1952);
x_8 = x_2029;
x_9 = x_2030;
goto block_16;
}
}
else
{
lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; 
lean_dec(x_1947);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2031 = lean_ctor_get(x_1948, 1);
lean_inc(x_2031);
if (lean_is_exclusive(x_1948)) {
 lean_ctor_release(x_1948, 0);
 lean_ctor_release(x_1948, 1);
 x_2032 = x_1948;
} else {
 lean_dec_ref(x_1948);
 x_2032 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_1943);
if (lean_is_scalar(x_2032)) {
 x_2033 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2033 = x_2032;
}
lean_ctor_set(x_2033, 0, x_43);
lean_ctor_set(x_2033, 1, x_2031);
return x_2033;
}
}
else
{
lean_object* x_2034; lean_object* x_2035; 
lean_dec(x_1947);
lean_dec(x_1943);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2034 = lean_ctor_get(x_1948, 0);
lean_inc(x_2034);
x_2035 = lean_ctor_get(x_1948, 1);
lean_inc(x_2035);
lean_dec(x_1948);
x_8 = x_2034;
x_9 = x_2035;
goto block_16;
}
}
else
{
lean_object* x_2036; lean_object* x_2037; 
lean_dec(x_1943);
lean_dec(x_51);
lean_dec(x_1938);
lean_dec(x_1923);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2036 = lean_ctor_get(x_1944, 0);
lean_inc(x_2036);
x_2037 = lean_ctor_get(x_1944, 1);
lean_inc(x_2037);
lean_dec(x_1944);
x_8 = x_2036;
x_9 = x_2037;
goto block_16;
}
}
else
{
lean_object* x_2038; lean_object* x_2039; 
lean_dec(x_1931);
lean_dec(x_1929);
lean_dec(x_1927);
lean_dec(x_1925);
lean_dec(x_1923);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2038 = lean_ctor_get(x_1932, 0);
lean_inc(x_2038);
x_2039 = lean_ctor_get(x_1932, 1);
lean_inc(x_2039);
lean_dec(x_1932);
x_8 = x_2038;
x_9 = x_2039;
goto block_16;
}
}
else
{
lean_object* x_2040; lean_object* x_2041; 
lean_dec(x_1927);
lean_dec(x_1925);
lean_dec(x_1923);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2040 = lean_ctor_get(x_1928, 0);
lean_inc(x_2040);
x_2041 = lean_ctor_get(x_1928, 1);
lean_inc(x_2041);
lean_dec(x_1928);
x_8 = x_2040;
x_9 = x_2041;
goto block_16;
}
}
else
{
lean_object* x_2042; lean_object* x_2043; 
lean_dec(x_1923);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2042 = lean_ctor_get(x_1924, 0);
lean_inc(x_2042);
x_2043 = lean_ctor_get(x_1924, 1);
lean_inc(x_2043);
lean_dec(x_1924);
x_8 = x_2042;
x_9 = x_2043;
goto block_16;
}
}
else
{
lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; 
lean_dec(x_1921);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2044 = lean_ctor_get(x_1920, 1);
lean_inc(x_2044);
if (lean_is_exclusive(x_1920)) {
 lean_ctor_release(x_1920, 0);
 lean_ctor_release(x_1920, 1);
 x_2045 = x_1920;
} else {
 lean_dec_ref(x_1920);
 x_2045 = lean_box(0);
}
if (lean_is_scalar(x_2045)) {
 x_2046 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2046 = x_2045;
}
lean_ctor_set(x_2046, 0, x_1919);
lean_ctor_set(x_2046, 1, x_2044);
return x_2046;
}
}
else
{
lean_object* x_2047; lean_object* x_2048; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2047 = lean_ctor_get(x_1920, 0);
lean_inc(x_2047);
x_2048 = lean_ctor_get(x_1920, 1);
lean_inc(x_2048);
lean_dec(x_1920);
x_8 = x_2047;
x_9 = x_2048;
goto block_16;
}
}
else
{
lean_object* x_2049; lean_object* x_2050; 
lean_dec(x_1904);
lean_dec(x_1902);
lean_dec(x_1891);
lean_dec(x_1887);
lean_dec(x_1885);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2049 = lean_ctor_get(x_1905, 0);
lean_inc(x_2049);
x_2050 = lean_ctor_get(x_1905, 1);
lean_inc(x_2050);
lean_dec(x_1905);
x_8 = x_2049;
x_9 = x_2050;
goto block_16;
}
}
else
{
lean_object* x_2051; lean_object* x_2052; 
lean_dec(x_1891);
lean_dec(x_1887);
lean_dec(x_1885);
lean_dec(x_1883);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2051 = lean_ctor_get(x_1901, 0);
lean_inc(x_2051);
x_2052 = lean_ctor_get(x_1901, 1);
lean_inc(x_2052);
lean_dec(x_1901);
x_8 = x_2051;
x_9 = x_2052;
goto block_16;
}
}
}
else
{
lean_object* x_2053; lean_object* x_2054; 
lean_dec(x_1891);
lean_dec(x_1887);
lean_dec(x_1885);
lean_dec(x_1883);
lean_dec(x_1873);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2053 = lean_ctor_get(x_1893, 0);
lean_inc(x_2053);
x_2054 = lean_ctor_get(x_1893, 1);
lean_inc(x_2054);
lean_dec(x_1893);
x_8 = x_2053;
x_9 = x_2054;
goto block_16;
}
}
else
{
lean_object* x_2055; lean_object* x_2056; 
lean_dec(x_1887);
lean_dec(x_1885);
lean_dec(x_1883);
lean_dec(x_1873);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2055 = lean_ctor_get(x_1888, 0);
lean_inc(x_2055);
x_2056 = lean_ctor_get(x_1888, 1);
lean_inc(x_2056);
lean_dec(x_1888);
x_8 = x_2055;
x_9 = x_2056;
goto block_16;
}
}
else
{
lean_object* x_2057; lean_object* x_2058; 
lean_dec(x_1883);
lean_dec(x_1882);
lean_dec(x_1873);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2057 = lean_ctor_get(x_1884, 0);
lean_inc(x_2057);
x_2058 = lean_ctor_get(x_1884, 1);
lean_inc(x_2058);
lean_dec(x_1884);
x_8 = x_2057;
x_9 = x_2058;
goto block_16;
}
}
else
{
lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; 
lean_dec(x_1880);
lean_dec(x_1879);
lean_dec(x_1873);
lean_dec(x_1872);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2059 = lean_ctor_get(x_1877, 1);
lean_inc(x_2059);
if (lean_is_exclusive(x_1877)) {
 lean_ctor_release(x_1877, 0);
 lean_ctor_release(x_1877, 1);
 x_2060 = x_1877;
} else {
 lean_dec_ref(x_1877);
 x_2060 = lean_box(0);
}
x_2061 = lean_box(0);
if (lean_is_scalar(x_2060)) {
 x_2062 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2062 = x_2060;
}
lean_ctor_set(x_2062, 0, x_2061);
lean_ctor_set(x_2062, 1, x_2059);
return x_2062;
}
}
else
{
lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; 
lean_dec(x_1879);
lean_dec(x_1878);
lean_dec(x_1873);
lean_dec(x_1872);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2063 = lean_ctor_get(x_1877, 1);
lean_inc(x_2063);
if (lean_is_exclusive(x_1877)) {
 lean_ctor_release(x_1877, 0);
 lean_ctor_release(x_1877, 1);
 x_2064 = x_1877;
} else {
 lean_dec_ref(x_1877);
 x_2064 = lean_box(0);
}
x_2065 = lean_box(0);
if (lean_is_scalar(x_2064)) {
 x_2066 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2066 = x_2064;
}
lean_ctor_set(x_2066, 0, x_2065);
lean_ctor_set(x_2066, 1, x_2063);
return x_2066;
}
}
else
{
lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; 
lean_dec(x_1878);
lean_dec(x_1873);
lean_dec(x_1872);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2067 = lean_ctor_get(x_1877, 1);
lean_inc(x_2067);
if (lean_is_exclusive(x_1877)) {
 lean_ctor_release(x_1877, 0);
 lean_ctor_release(x_1877, 1);
 x_2068 = x_1877;
} else {
 lean_dec_ref(x_1877);
 x_2068 = lean_box(0);
}
x_2069 = lean_box(0);
if (lean_is_scalar(x_2068)) {
 x_2070 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2070 = x_2068;
}
lean_ctor_set(x_2070, 0, x_2069);
lean_ctor_set(x_2070, 1, x_2067);
return x_2070;
}
}
else
{
lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; uint8_t x_2074; 
lean_dec(x_1873);
lean_dec(x_1872);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2071 = lean_ctor_get(x_1877, 0);
lean_inc(x_2071);
x_2072 = lean_ctor_get(x_1877, 1);
lean_inc(x_2072);
if (lean_is_exclusive(x_1877)) {
 lean_ctor_release(x_1877, 0);
 lean_ctor_release(x_1877, 1);
 x_2073 = x_1877;
} else {
 lean_dec_ref(x_1877);
 x_2073 = lean_box(0);
}
x_2074 = l_Lean_Exception_isInterrupt(x_2071);
if (x_2074 == 0)
{
uint8_t x_2075; 
x_2075 = l_Lean_Exception_isRuntime(x_2071);
if (x_2075 == 0)
{
lean_object* x_2076; lean_object* x_2077; 
lean_dec(x_2071);
x_2076 = lean_box(0);
if (lean_is_scalar(x_2073)) {
 x_2077 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2077 = x_2073;
 lean_ctor_set_tag(x_2077, 0);
}
lean_ctor_set(x_2077, 0, x_2076);
lean_ctor_set(x_2077, 1, x_2072);
return x_2077;
}
else
{
lean_object* x_2078; 
if (lean_is_scalar(x_2073)) {
 x_2078 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2078 = x_2073;
}
lean_ctor_set(x_2078, 0, x_2071);
lean_ctor_set(x_2078, 1, x_2072);
return x_2078;
}
}
else
{
lean_object* x_2079; 
if (lean_is_scalar(x_2073)) {
 x_2079 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2079 = x_2073;
}
lean_ctor_set(x_2079, 0, x_2071);
lean_ctor_set(x_2079, 1, x_2072);
return x_2079;
}
}
}
else
{
lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; uint8_t x_2083; 
lean_dec(x_1873);
lean_dec(x_1872);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2080 = lean_ctor_get(x_1874, 0);
lean_inc(x_2080);
x_2081 = lean_ctor_get(x_1874, 1);
lean_inc(x_2081);
if (lean_is_exclusive(x_1874)) {
 lean_ctor_release(x_1874, 0);
 lean_ctor_release(x_1874, 1);
 x_2082 = x_1874;
} else {
 lean_dec_ref(x_1874);
 x_2082 = lean_box(0);
}
x_2083 = l_Lean_Exception_isInterrupt(x_2080);
if (x_2083 == 0)
{
uint8_t x_2084; 
x_2084 = l_Lean_Exception_isRuntime(x_2080);
if (x_2084 == 0)
{
lean_object* x_2085; lean_object* x_2086; 
lean_dec(x_2080);
x_2085 = lean_box(0);
if (lean_is_scalar(x_2082)) {
 x_2086 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2086 = x_2082;
 lean_ctor_set_tag(x_2086, 0);
}
lean_ctor_set(x_2086, 0, x_2085);
lean_ctor_set(x_2086, 1, x_2081);
return x_2086;
}
else
{
lean_object* x_2087; 
if (lean_is_scalar(x_2082)) {
 x_2087 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2087 = x_2082;
}
lean_ctor_set(x_2087, 0, x_2080);
lean_ctor_set(x_2087, 1, x_2081);
return x_2087;
}
}
else
{
lean_object* x_2088; 
if (lean_is_scalar(x_2082)) {
 x_2088 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2088 = x_2082;
}
lean_ctor_set(x_2088, 0, x_2080);
lean_ctor_set(x_2088, 1, x_2081);
return x_2088;
}
}
}
else
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; 
lean_dec(x_1870);
lean_dec(x_1869);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2089 = lean_ctor_get(x_1867, 1);
lean_inc(x_2089);
if (lean_is_exclusive(x_1867)) {
 lean_ctor_release(x_1867, 0);
 lean_ctor_release(x_1867, 1);
 x_2090 = x_1867;
} else {
 lean_dec_ref(x_1867);
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
lean_dec(x_1869);
lean_dec(x_1868);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2093 = lean_ctor_get(x_1867, 1);
lean_inc(x_2093);
if (lean_is_exclusive(x_1867)) {
 lean_ctor_release(x_1867, 0);
 lean_ctor_release(x_1867, 1);
 x_2094 = x_1867;
} else {
 lean_dec_ref(x_1867);
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
lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; 
lean_dec(x_1868);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2097 = lean_ctor_get(x_1867, 1);
lean_inc(x_2097);
if (lean_is_exclusive(x_1867)) {
 lean_ctor_release(x_1867, 0);
 lean_ctor_release(x_1867, 1);
 x_2098 = x_1867;
} else {
 lean_dec_ref(x_1867);
 x_2098 = lean_box(0);
}
x_2099 = lean_box(0);
if (lean_is_scalar(x_2098)) {
 x_2100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2100 = x_2098;
}
lean_ctor_set(x_2100, 0, x_2099);
lean_ctor_set(x_2100, 1, x_2097);
return x_2100;
}
}
else
{
lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; uint8_t x_2104; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2101 = lean_ctor_get(x_1867, 0);
lean_inc(x_2101);
x_2102 = lean_ctor_get(x_1867, 1);
lean_inc(x_2102);
if (lean_is_exclusive(x_1867)) {
 lean_ctor_release(x_1867, 0);
 lean_ctor_release(x_1867, 1);
 x_2103 = x_1867;
} else {
 lean_dec_ref(x_1867);
 x_2103 = lean_box(0);
}
x_2104 = l_Lean_Exception_isInterrupt(x_2101);
if (x_2104 == 0)
{
uint8_t x_2105; 
x_2105 = l_Lean_Exception_isRuntime(x_2101);
if (x_2105 == 0)
{
lean_object* x_2106; lean_object* x_2107; 
lean_dec(x_2101);
x_2106 = lean_box(0);
if (lean_is_scalar(x_2103)) {
 x_2107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2107 = x_2103;
 lean_ctor_set_tag(x_2107, 0);
}
lean_ctor_set(x_2107, 0, x_2106);
lean_ctor_set(x_2107, 1, x_2102);
return x_2107;
}
else
{
lean_object* x_2108; 
if (lean_is_scalar(x_2103)) {
 x_2108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2108 = x_2103;
}
lean_ctor_set(x_2108, 0, x_2101);
lean_ctor_set(x_2108, 1, x_2102);
return x_2108;
}
}
else
{
lean_object* x_2109; 
if (lean_is_scalar(x_2103)) {
 x_2109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2109 = x_2103;
}
lean_ctor_set(x_2109, 0, x_2101);
lean_ctor_set(x_2109, 1, x_2102);
return x_2109;
}
}
}
else
{
lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; uint8_t x_2113; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2110 = lean_ctor_get(x_1864, 0);
lean_inc(x_2110);
x_2111 = lean_ctor_get(x_1864, 1);
lean_inc(x_2111);
if (lean_is_exclusive(x_1864)) {
 lean_ctor_release(x_1864, 0);
 lean_ctor_release(x_1864, 1);
 x_2112 = x_1864;
} else {
 lean_dec_ref(x_1864);
 x_2112 = lean_box(0);
}
x_2113 = l_Lean_Exception_isInterrupt(x_2110);
if (x_2113 == 0)
{
uint8_t x_2114; 
x_2114 = l_Lean_Exception_isRuntime(x_2110);
if (x_2114 == 0)
{
lean_object* x_2115; lean_object* x_2116; 
lean_dec(x_2110);
x_2115 = lean_box(0);
if (lean_is_scalar(x_2112)) {
 x_2116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2116 = x_2112;
 lean_ctor_set_tag(x_2116, 0);
}
lean_ctor_set(x_2116, 0, x_2115);
lean_ctor_set(x_2116, 1, x_2111);
return x_2116;
}
else
{
lean_object* x_2117; 
if (lean_is_scalar(x_2112)) {
 x_2117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2117 = x_2112;
}
lean_ctor_set(x_2117, 0, x_2110);
lean_ctor_set(x_2117, 1, x_2111);
return x_2117;
}
}
else
{
lean_object* x_2118; 
if (lean_is_scalar(x_2112)) {
 x_2118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2118 = x_2112;
}
lean_ctor_set(x_2118, 0, x_2110);
lean_ctor_set(x_2118, 1, x_2111);
return x_2118;
}
}
}
}
else
{
lean_object* x_2119; lean_object* x_2120; 
lean_dec(x_26);
lean_dec(x_19);
x_2119 = lean_ctor_get(x_1854, 1);
lean_inc(x_2119);
lean_dec(x_1854);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2120 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_2119);
if (lean_obj_tag(x_2120) == 0)
{
lean_object* x_2121; 
x_2121 = lean_ctor_get(x_2120, 0);
lean_inc(x_2121);
if (lean_obj_tag(x_2121) == 0)
{
lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; 
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_1);
x_2122 = lean_ctor_get(x_2120, 1);
lean_inc(x_2122);
lean_dec(x_2120);
x_2123 = l_Lean_Meta_SavedState_restore(x_1852, x_3, x_4, x_5, x_6, x_2122);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1852);
x_2124 = lean_ctor_get(x_2123, 1);
lean_inc(x_2124);
if (lean_is_exclusive(x_2123)) {
 lean_ctor_release(x_2123, 0);
 lean_ctor_release(x_2123, 1);
 x_2125 = x_2123;
} else {
 lean_dec_ref(x_2123);
 x_2125 = lean_box(0);
}
x_2126 = lean_box(0);
if (lean_is_scalar(x_2125)) {
 x_2127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2127 = x_2125;
}
lean_ctor_set(x_2127, 0, x_2126);
lean_ctor_set(x_2127, 1, x_2124);
return x_2127;
}
else
{
lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2151; lean_object* x_2152; 
x_2128 = lean_ctor_get(x_2120, 1);
lean_inc(x_2128);
if (lean_is_exclusive(x_2120)) {
 lean_ctor_release(x_2120, 0);
 lean_ctor_release(x_2120, 1);
 x_2129 = x_2120;
} else {
 lean_dec_ref(x_2120);
 x_2129 = lean_box(0);
}
x_2130 = lean_ctor_get(x_2121, 0);
lean_inc(x_2130);
if (lean_is_exclusive(x_2121)) {
 lean_ctor_release(x_2121, 0);
 x_2131 = x_2121;
} else {
 lean_dec_ref(x_2121);
 x_2131 = lean_box(0);
}
if (lean_is_scalar(x_2131)) {
 x_2132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2132 = x_2131;
}
lean_ctor_set(x_2132, 0, x_54);
lean_ctor_set(x_43, 0, x_55);
lean_ctor_set(x_29, 0, x_41);
x_2133 = lean_box(0);
x_2134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2134, 0, x_2130);
x_2135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2135, 0, x_1);
x_2136 = lean_box(0);
x_2137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2137, 0, x_2135);
lean_ctor_set(x_2137, 1, x_2136);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_2137);
lean_ctor_set(x_51, 0, x_2134);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_2133);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_29);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_43);
x_2138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2138, 0, x_2132);
lean_ctor_set(x_2138, 1, x_17);
x_2139 = lean_array_mk(x_2138);
x_2151 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2152 = l_Lean_Meta_mkAppOptM(x_2151, x_2139, x_3, x_4, x_5, x_6, x_2128);
if (lean_obj_tag(x_2152) == 0)
{
lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; 
x_2153 = lean_ctor_get(x_2152, 0);
lean_inc(x_2153);
x_2154 = lean_ctor_get(x_2152, 1);
lean_inc(x_2154);
lean_dec(x_2152);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2155 = l_Lean_Meta_expandCoe(x_2153, x_3, x_4, x_5, x_6, x_2154);
if (lean_obj_tag(x_2155) == 0)
{
lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; 
lean_dec(x_2129);
lean_dec(x_1852);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2156 = lean_ctor_get(x_2155, 0);
lean_inc(x_2156);
x_2157 = lean_ctor_get(x_2155, 1);
lean_inc(x_2157);
if (lean_is_exclusive(x_2155)) {
 lean_ctor_release(x_2155, 0);
 lean_ctor_release(x_2155, 1);
 x_2158 = x_2155;
} else {
 lean_dec_ref(x_2155);
 x_2158 = lean_box(0);
}
x_2159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2159, 0, x_2156);
if (lean_is_scalar(x_2158)) {
 x_2160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2160 = x_2158;
}
lean_ctor_set(x_2160, 0, x_2159);
lean_ctor_set(x_2160, 1, x_2157);
return x_2160;
}
else
{
lean_object* x_2161; lean_object* x_2162; 
x_2161 = lean_ctor_get(x_2155, 0);
lean_inc(x_2161);
x_2162 = lean_ctor_get(x_2155, 1);
lean_inc(x_2162);
lean_dec(x_2155);
x_2140 = x_2161;
x_2141 = x_2162;
goto block_2150;
}
}
else
{
lean_object* x_2163; lean_object* x_2164; 
x_2163 = lean_ctor_get(x_2152, 0);
lean_inc(x_2163);
x_2164 = lean_ctor_get(x_2152, 1);
lean_inc(x_2164);
lean_dec(x_2152);
x_2140 = x_2163;
x_2141 = x_2164;
goto block_2150;
}
block_2150:
{
uint8_t x_2142; 
x_2142 = l_Lean_Exception_isInterrupt(x_2140);
if (x_2142 == 0)
{
uint8_t x_2143; 
x_2143 = l_Lean_Exception_isRuntime(x_2140);
if (x_2143 == 0)
{
lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; 
lean_dec(x_2140);
lean_dec(x_2129);
x_2144 = l_Lean_Meta_SavedState_restore(x_1852, x_3, x_4, x_5, x_6, x_2141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1852);
x_2145 = lean_ctor_get(x_2144, 1);
lean_inc(x_2145);
if (lean_is_exclusive(x_2144)) {
 lean_ctor_release(x_2144, 0);
 lean_ctor_release(x_2144, 1);
 x_2146 = x_2144;
} else {
 lean_dec_ref(x_2144);
 x_2146 = lean_box(0);
}
if (lean_is_scalar(x_2146)) {
 x_2147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2147 = x_2146;
}
lean_ctor_set(x_2147, 0, x_2133);
lean_ctor_set(x_2147, 1, x_2145);
return x_2147;
}
else
{
lean_object* x_2148; 
lean_dec(x_1852);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_2129)) {
 x_2148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2148 = x_2129;
 lean_ctor_set_tag(x_2148, 1);
}
lean_ctor_set(x_2148, 0, x_2140);
lean_ctor_set(x_2148, 1, x_2141);
return x_2148;
}
}
else
{
lean_object* x_2149; 
lean_dec(x_1852);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_2129)) {
 x_2149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2149 = x_2129;
 lean_ctor_set_tag(x_2149, 1);
}
lean_ctor_set(x_2149, 0, x_2140);
lean_ctor_set(x_2149, 1, x_2141);
return x_2149;
}
}
}
}
else
{
lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; 
lean_dec(x_1852);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2165 = lean_ctor_get(x_2120, 0);
lean_inc(x_2165);
x_2166 = lean_ctor_get(x_2120, 1);
lean_inc(x_2166);
if (lean_is_exclusive(x_2120)) {
 lean_ctor_release(x_2120, 0);
 lean_ctor_release(x_2120, 1);
 x_2167 = x_2120;
} else {
 lean_dec_ref(x_2120);
 x_2167 = lean_box(0);
}
if (lean_is_scalar(x_2167)) {
 x_2168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2168 = x_2167;
}
lean_ctor_set(x_2168, 0, x_2165);
lean_ctor_set(x_2168, 1, x_2166);
return x_2168;
}
}
}
else
{
lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; 
lean_dec(x_1852);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2169 = lean_ctor_get(x_1854, 0);
lean_inc(x_2169);
x_2170 = lean_ctor_get(x_1854, 1);
lean_inc(x_2170);
if (lean_is_exclusive(x_1854)) {
 lean_ctor_release(x_1854, 0);
 lean_ctor_release(x_1854, 1);
 x_2171 = x_1854;
} else {
 lean_dec_ref(x_1854);
 x_2171 = lean_box(0);
}
if (lean_is_scalar(x_2171)) {
 x_2172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2172 = x_2171;
}
lean_ctor_set(x_2172, 0, x_2169);
lean_ctor_set(x_2172, 1, x_2170);
return x_2172;
}
}
}
else
{
lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; 
x_2173 = lean_ctor_get(x_51, 0);
x_2174 = lean_ctor_get(x_51, 1);
lean_inc(x_2174);
lean_inc(x_2173);
lean_dec(x_51);
x_2175 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_52);
x_2176 = lean_ctor_get(x_2175, 0);
lean_inc(x_2176);
x_2177 = lean_ctor_get(x_2175, 1);
lean_inc(x_2177);
if (lean_is_exclusive(x_2175)) {
 lean_ctor_release(x_2175, 0);
 lean_ctor_release(x_2175, 1);
 x_2178 = x_2175;
} else {
 lean_dec_ref(x_2175);
 x_2178 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
lean_inc(x_2173);
x_2179 = l_Lean_Meta_isExprDefEq(x_2173, x_40, x_3, x_4, x_5, x_6, x_2177);
if (lean_obj_tag(x_2179) == 0)
{
lean_object* x_2180; uint8_t x_2181; 
x_2180 = lean_ctor_get(x_2179, 0);
lean_inc(x_2180);
x_2181 = lean_unbox(x_2180);
lean_dec(x_2180);
if (x_2181 == 0)
{
lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; uint8_t x_2186; 
lean_dec(x_2176);
lean_free_object(x_29);
x_2182 = lean_ctor_get(x_2179, 1);
lean_inc(x_2182);
if (lean_is_exclusive(x_2179)) {
 lean_ctor_release(x_2179, 0);
 lean_ctor_release(x_2179, 1);
 x_2183 = x_2179;
} else {
 lean_dec_ref(x_2179);
 x_2183 = lean_box(0);
}
x_2184 = lean_ctor_get(x_5, 2);
lean_inc(x_2184);
x_2185 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_2186 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2184, x_2185);
lean_dec(x_2184);
if (x_2186 == 0)
{
lean_object* x_2187; lean_object* x_2188; 
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2187 = lean_box(0);
if (lean_is_scalar(x_2183)) {
 x_2188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2188 = x_2183;
}
lean_ctor_set(x_2188, 0, x_2187);
lean_ctor_set(x_2188, 1, x_2182);
return x_2188;
}
else
{
lean_object* x_2189; 
lean_dec(x_2183);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2173);
x_2189 = lean_infer_type(x_2173, x_3, x_4, x_5, x_6, x_2182);
if (lean_obj_tag(x_2189) == 0)
{
lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; 
x_2190 = lean_ctor_get(x_2189, 0);
lean_inc(x_2190);
x_2191 = lean_ctor_get(x_2189, 1);
lean_inc(x_2191);
lean_dec(x_2189);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2192 = lean_whnf(x_2190, x_3, x_4, x_5, x_6, x_2191);
if (lean_obj_tag(x_2192) == 0)
{
lean_object* x_2193; 
x_2193 = lean_ctor_get(x_2192, 0);
lean_inc(x_2193);
if (lean_obj_tag(x_2193) == 7)
{
lean_object* x_2194; 
x_2194 = lean_ctor_get(x_2193, 1);
lean_inc(x_2194);
if (lean_obj_tag(x_2194) == 3)
{
lean_object* x_2195; 
x_2195 = lean_ctor_get(x_2193, 2);
lean_inc(x_2195);
lean_dec(x_2193);
if (lean_obj_tag(x_2195) == 3)
{
lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; 
x_2196 = lean_ctor_get(x_2192, 1);
lean_inc(x_2196);
lean_dec(x_2192);
x_2197 = lean_ctor_get(x_2194, 0);
lean_inc(x_2197);
lean_dec(x_2194);
x_2198 = lean_ctor_get(x_2195, 0);
lean_inc(x_2198);
lean_dec(x_2195);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_2199 = lean_infer_type(x_40, x_3, x_4, x_5, x_6, x_2196);
if (lean_obj_tag(x_2199) == 0)
{
lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; 
x_2200 = lean_ctor_get(x_2199, 0);
lean_inc(x_2200);
x_2201 = lean_ctor_get(x_2199, 1);
lean_inc(x_2201);
lean_dec(x_2199);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2202 = lean_whnf(x_2200, x_3, x_4, x_5, x_6, x_2201);
if (lean_obj_tag(x_2202) == 0)
{
lean_object* x_2203; 
x_2203 = lean_ctor_get(x_2202, 0);
lean_inc(x_2203);
if (lean_obj_tag(x_2203) == 7)
{
lean_object* x_2204; 
x_2204 = lean_ctor_get(x_2203, 1);
lean_inc(x_2204);
if (lean_obj_tag(x_2204) == 3)
{
lean_object* x_2205; 
x_2205 = lean_ctor_get(x_2203, 2);
lean_inc(x_2205);
lean_dec(x_2203);
if (lean_obj_tag(x_2205) == 3)
{
lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; 
x_2206 = lean_ctor_get(x_2202, 1);
lean_inc(x_2206);
lean_dec(x_2202);
x_2207 = lean_ctor_get(x_2204, 0);
lean_inc(x_2207);
lean_dec(x_2204);
x_2208 = lean_ctor_get(x_2205, 0);
lean_inc(x_2208);
lean_dec(x_2205);
x_2209 = l_Lean_Meta_decLevel(x_2197, x_3, x_4, x_5, x_6, x_2206);
if (lean_obj_tag(x_2209) == 0)
{
lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; 
x_2210 = lean_ctor_get(x_2209, 0);
lean_inc(x_2210);
x_2211 = lean_ctor_get(x_2209, 1);
lean_inc(x_2211);
if (lean_is_exclusive(x_2209)) {
 lean_ctor_release(x_2209, 0);
 lean_ctor_release(x_2209, 1);
 x_2212 = x_2209;
} else {
 lean_dec_ref(x_2209);
 x_2212 = lean_box(0);
}
x_2213 = l_Lean_Meta_decLevel(x_2207, x_3, x_4, x_5, x_6, x_2211);
if (lean_obj_tag(x_2213) == 0)
{
lean_object* x_2214; lean_object* x_2215; lean_object* x_2216; uint8_t x_2217; lean_object* x_2218; 
x_2214 = lean_ctor_get(x_2213, 0);
lean_inc(x_2214);
x_2215 = lean_ctor_get(x_2213, 1);
lean_inc(x_2215);
if (lean_is_exclusive(x_2213)) {
 lean_ctor_release(x_2213, 0);
 lean_ctor_release(x_2213, 1);
 x_2216 = x_2213;
} else {
 lean_dec_ref(x_2213);
 x_2216 = lean_box(0);
}
x_2217 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2210);
x_2218 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_2210, x_2214, x_2217, x_3, x_4, x_5, x_6, x_2215);
if (lean_obj_tag(x_2218) == 0)
{
lean_object* x_2219; uint8_t x_2220; 
x_2219 = lean_ctor_get(x_2218, 0);
lean_inc(x_2219);
x_2220 = lean_unbox(x_2219);
lean_dec(x_2219);
if (x_2220 == 0)
{
lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; 
lean_dec(x_2216);
lean_dec(x_2212);
lean_dec(x_2210);
lean_dec(x_2208);
lean_dec(x_2198);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2221 = lean_ctor_get(x_2218, 1);
lean_inc(x_2221);
if (lean_is_exclusive(x_2218)) {
 lean_ctor_release(x_2218, 0);
 lean_ctor_release(x_2218, 1);
 x_2222 = x_2218;
} else {
 lean_dec_ref(x_2218);
 x_2222 = lean_box(0);
}
x_2223 = lean_box(0);
if (lean_is_scalar(x_2222)) {
 x_2224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2224 = x_2222;
}
lean_ctor_set(x_2224, 0, x_2223);
lean_ctor_set(x_2224, 1, x_2221);
return x_2224;
}
else
{
lean_object* x_2225; lean_object* x_2226; 
x_2225 = lean_ctor_get(x_2218, 1);
lean_inc(x_2225);
lean_dec(x_2218);
x_2226 = l_Lean_Meta_decLevel(x_2198, x_3, x_4, x_5, x_6, x_2225);
if (lean_obj_tag(x_2226) == 0)
{
lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; 
x_2227 = lean_ctor_get(x_2226, 0);
lean_inc(x_2227);
x_2228 = lean_ctor_get(x_2226, 1);
lean_inc(x_2228);
if (lean_is_exclusive(x_2226)) {
 lean_ctor_release(x_2226, 0);
 lean_ctor_release(x_2226, 1);
 x_2229 = x_2226;
} else {
 lean_dec_ref(x_2226);
 x_2229 = lean_box(0);
}
x_2230 = l_Lean_Meta_decLevel(x_2208, x_3, x_4, x_5, x_6, x_2228);
if (lean_obj_tag(x_2230) == 0)
{
lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; lean_object* x_2245; 
x_2231 = lean_ctor_get(x_2230, 0);
lean_inc(x_2231);
x_2232 = lean_ctor_get(x_2230, 1);
lean_inc(x_2232);
if (lean_is_exclusive(x_2230)) {
 lean_ctor_release(x_2230, 0);
 lean_ctor_release(x_2230, 1);
 x_2233 = x_2230;
} else {
 lean_dec_ref(x_2230);
 x_2233 = lean_box(0);
}
x_2234 = lean_box(0);
if (lean_is_scalar(x_2233)) {
 x_2235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2235 = x_2233;
 lean_ctor_set_tag(x_2235, 1);
}
lean_ctor_set(x_2235, 0, x_2231);
lean_ctor_set(x_2235, 1, x_2234);
if (lean_is_scalar(x_2229)) {
 x_2236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2236 = x_2229;
 lean_ctor_set_tag(x_2236, 1);
}
lean_ctor_set(x_2236, 0, x_2227);
lean_ctor_set(x_2236, 1, x_2235);
if (lean_is_scalar(x_2216)) {
 x_2237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2237 = x_2216;
 lean_ctor_set_tag(x_2237, 1);
}
lean_ctor_set(x_2237, 0, x_2210);
lean_ctor_set(x_2237, 1, x_2236);
x_2238 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2239 = l_Lean_Expr_const___override(x_2238, x_2237);
lean_inc(x_40);
if (lean_is_scalar(x_2212)) {
 x_2240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2240 = x_2212;
 lean_ctor_set_tag(x_2240, 1);
}
lean_ctor_set(x_2240, 0, x_40);
lean_ctor_set(x_2240, 1, x_2234);
lean_inc(x_2173);
if (lean_is_scalar(x_2178)) {
 x_2241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2241 = x_2178;
 lean_ctor_set_tag(x_2241, 1);
}
lean_ctor_set(x_2241, 0, x_2173);
lean_ctor_set(x_2241, 1, x_2240);
x_2242 = lean_array_mk(x_2241);
x_2243 = l_Lean_mkAppN(x_2239, x_2242);
lean_dec(x_2242);
x_2244 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2245 = l_Lean_Meta_trySynthInstance(x_2243, x_2244, x_3, x_4, x_5, x_6, x_2232);
if (lean_obj_tag(x_2245) == 0)
{
lean_object* x_2246; 
x_2246 = lean_ctor_get(x_2245, 0);
lean_inc(x_2246);
if (lean_obj_tag(x_2246) == 1)
{
lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; 
x_2247 = lean_ctor_get(x_2245, 1);
lean_inc(x_2247);
lean_dec(x_2245);
x_2248 = lean_ctor_get(x_2246, 0);
lean_inc(x_2248);
lean_dec(x_2246);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2174);
x_2249 = l_Lean_Meta_getDecLevel(x_2174, x_3, x_4, x_5, x_6, x_2247);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2253 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_2251);
if (lean_obj_tag(x_2253) == 0)
{
lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_2257 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_2255);
if (lean_obj_tag(x_2257) == 0)
{
lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; 
x_2258 = lean_ctor_get(x_2257, 0);
lean_inc(x_2258);
x_2259 = lean_ctor_get(x_2257, 1);
lean_inc(x_2259);
if (lean_is_exclusive(x_2257)) {
 lean_ctor_release(x_2257, 0);
 lean_ctor_release(x_2257, 1);
 x_2260 = x_2257;
} else {
 lean_dec_ref(x_2257);
 x_2260 = lean_box(0);
}
if (lean_is_scalar(x_2260)) {
 x_2261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2261 = x_2260;
 lean_ctor_set_tag(x_2261, 1);
}
lean_ctor_set(x_2261, 0, x_2258);
lean_ctor_set(x_2261, 1, x_2234);
if (lean_is_scalar(x_2256)) {
 x_2262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2262 = x_2256;
 lean_ctor_set_tag(x_2262, 1);
}
lean_ctor_set(x_2262, 0, x_2254);
lean_ctor_set(x_2262, 1, x_2261);
if (lean_is_scalar(x_2252)) {
 x_2263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2263 = x_2252;
 lean_ctor_set_tag(x_2263, 1);
}
lean_ctor_set(x_2263, 0, x_2250);
lean_ctor_set(x_2263, 1, x_2262);
x_2264 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_2263);
x_2265 = l_Lean_Expr_const___override(x_2264, x_2263);
x_2266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2266, 0, x_1);
lean_ctor_set(x_2266, 1, x_2234);
lean_inc(x_2266);
lean_inc(x_2174);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_2266);
lean_ctor_set(x_37, 0, x_2174);
lean_inc(x_2248);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_2248);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_2173);
x_2267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2267, 0, x_2173);
lean_ctor_set(x_2267, 1, x_17);
x_2268 = lean_array_mk(x_2267);
x_2269 = l_Lean_mkAppN(x_2265, x_2268);
lean_dec(x_2268);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2269);
x_2270 = lean_infer_type(x_2269, x_3, x_4, x_5, x_6, x_2259);
if (lean_obj_tag(x_2270) == 0)
{
lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; 
x_2271 = lean_ctor_get(x_2270, 0);
lean_inc(x_2271);
x_2272 = lean_ctor_get(x_2270, 1);
lean_inc(x_2272);
if (lean_is_exclusive(x_2270)) {
 lean_ctor_release(x_2270, 0);
 lean_ctor_release(x_2270, 1);
 x_2273 = x_2270;
} else {
 lean_dec_ref(x_2270);
 x_2273 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_2274 = l_Lean_Meta_isExprDefEq(x_19, x_2271, x_3, x_4, x_5, x_6, x_2272);
if (lean_obj_tag(x_2274) == 0)
{
lean_object* x_2275; uint8_t x_2276; 
x_2275 = lean_ctor_get(x_2274, 0);
lean_inc(x_2275);
x_2276 = lean_unbox(x_2275);
lean_dec(x_2275);
if (x_2276 == 0)
{
lean_object* x_2277; lean_object* x_2278; 
lean_dec(x_2269);
lean_free_object(x_43);
x_2277 = lean_ctor_get(x_2274, 1);
lean_inc(x_2277);
lean_dec(x_2274);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_2278 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_2277);
if (lean_obj_tag(x_2278) == 0)
{
lean_object* x_2279; 
x_2279 = lean_ctor_get(x_2278, 0);
lean_inc(x_2279);
if (lean_obj_tag(x_2279) == 0)
{
lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; 
lean_dec(x_2273);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2280 = lean_ctor_get(x_2278, 1);
lean_inc(x_2280);
if (lean_is_exclusive(x_2278)) {
 lean_ctor_release(x_2278, 0);
 lean_ctor_release(x_2278, 1);
 x_2281 = x_2278;
} else {
 lean_dec_ref(x_2278);
 x_2281 = lean_box(0);
}
if (lean_is_scalar(x_2281)) {
 x_2282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2282 = x_2281;
}
lean_ctor_set(x_2282, 0, x_2244);
lean_ctor_set(x_2282, 1, x_2280);
return x_2282;
}
else
{
lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; 
x_2283 = lean_ctor_get(x_2278, 1);
lean_inc(x_2283);
lean_dec(x_2278);
x_2284 = lean_ctor_get(x_2279, 0);
lean_inc(x_2284);
lean_dec(x_2279);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2174);
x_2285 = l_Lean_Meta_getLevel(x_2174, x_3, x_4, x_5, x_6, x_2283);
if (lean_obj_tag(x_2285) == 0)
{
lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; 
x_2286 = lean_ctor_get(x_2285, 0);
lean_inc(x_2286);
x_2287 = lean_ctor_get(x_2285, 1);
lean_inc(x_2287);
if (lean_is_exclusive(x_2285)) {
 lean_ctor_release(x_2285, 0);
 lean_ctor_release(x_2285, 1);
 x_2288 = x_2285;
} else {
 lean_dec_ref(x_2285);
 x_2288 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_2289 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_2287);
if (lean_obj_tag(x_2289) == 0)
{
lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; uint8_t x_2304; lean_object* x_2305; lean_object* x_2306; 
x_2290 = lean_ctor_get(x_2289, 0);
lean_inc(x_2290);
x_2291 = lean_ctor_get(x_2289, 1);
lean_inc(x_2291);
if (lean_is_exclusive(x_2289)) {
 lean_ctor_release(x_2289, 0);
 lean_ctor_release(x_2289, 1);
 x_2292 = x_2289;
} else {
 lean_dec_ref(x_2289);
 x_2292 = lean_box(0);
}
if (lean_is_scalar(x_2292)) {
 x_2293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2293 = x_2292;
 lean_ctor_set_tag(x_2293, 1);
}
lean_ctor_set(x_2293, 0, x_2290);
lean_ctor_set(x_2293, 1, x_2234);
if (lean_is_scalar(x_2288)) {
 x_2294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2294 = x_2288;
 lean_ctor_set_tag(x_2294, 1);
}
lean_ctor_set(x_2294, 0, x_2286);
lean_ctor_set(x_2294, 1, x_2293);
x_2295 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_2296 = l_Lean_Expr_const___override(x_2295, x_2294);
lean_inc(x_41);
if (lean_is_scalar(x_2273)) {
 x_2297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2297 = x_2273;
 lean_ctor_set_tag(x_2297, 1);
}
lean_ctor_set(x_2297, 0, x_41);
lean_ctor_set(x_2297, 1, x_2234);
x_2298 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_2299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2299, 0, x_2298);
lean_ctor_set(x_2299, 1, x_2297);
lean_inc(x_2174);
x_2300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2300, 0, x_2174);
lean_ctor_set(x_2300, 1, x_2299);
x_2301 = lean_array_mk(x_2300);
x_2302 = l_Lean_mkAppN(x_2296, x_2301);
lean_dec(x_2301);
x_2303 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_2304 = 0;
lean_inc(x_2174);
x_2305 = l_Lean_Expr_forallE___override(x_2303, x_2174, x_2302, x_2304);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2306 = l_Lean_Meta_trySynthInstance(x_2305, x_2244, x_3, x_4, x_5, x_6, x_2291);
if (lean_obj_tag(x_2306) == 0)
{
lean_object* x_2307; 
x_2307 = lean_ctor_get(x_2306, 0);
lean_inc(x_2307);
if (lean_obj_tag(x_2307) == 1)
{
lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; 
x_2308 = lean_ctor_get(x_2306, 1);
lean_inc(x_2308);
lean_dec(x_2306);
x_2309 = lean_ctor_get(x_2307, 0);
lean_inc(x_2309);
lean_dec(x_2307);
x_2310 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_2311 = l_Lean_Expr_const___override(x_2310, x_2263);
x_2312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2312, 0, x_2284);
lean_ctor_set(x_2312, 1, x_2266);
x_2313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2313, 0, x_2309);
lean_ctor_set(x_2313, 1, x_2312);
x_2314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2314, 0, x_2248);
lean_ctor_set(x_2314, 1, x_2313);
x_2315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2315, 0, x_41);
lean_ctor_set(x_2315, 1, x_2314);
x_2316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2316, 0, x_2174);
lean_ctor_set(x_2316, 1, x_2315);
x_2317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2317, 0, x_40);
lean_ctor_set(x_2317, 1, x_2316);
x_2318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2318, 0, x_2173);
lean_ctor_set(x_2318, 1, x_2317);
x_2319 = lean_array_mk(x_2318);
x_2320 = l_Lean_mkAppN(x_2311, x_2319);
lean_dec(x_2319);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2321 = l_Lean_Meta_expandCoe(x_2320, x_3, x_4, x_5, x_6, x_2308);
if (lean_obj_tag(x_2321) == 0)
{
lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; 
x_2322 = lean_ctor_get(x_2321, 0);
lean_inc(x_2322);
x_2323 = lean_ctor_get(x_2321, 1);
lean_inc(x_2323);
lean_dec(x_2321);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2322);
x_2324 = lean_infer_type(x_2322, x_3, x_4, x_5, x_6, x_2323);
if (lean_obj_tag(x_2324) == 0)
{
lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; 
x_2325 = lean_ctor_get(x_2324, 0);
lean_inc(x_2325);
x_2326 = lean_ctor_get(x_2324, 1);
lean_inc(x_2326);
lean_dec(x_2324);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2327 = l_Lean_Meta_isExprDefEq(x_19, x_2325, x_3, x_4, x_5, x_6, x_2326);
if (lean_obj_tag(x_2327) == 0)
{
lean_object* x_2328; uint8_t x_2329; 
x_2328 = lean_ctor_get(x_2327, 0);
lean_inc(x_2328);
x_2329 = lean_unbox(x_2328);
lean_dec(x_2328);
if (x_2329 == 0)
{
lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; 
lean_dec(x_2322);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2330 = lean_ctor_get(x_2327, 1);
lean_inc(x_2330);
if (lean_is_exclusive(x_2327)) {
 lean_ctor_release(x_2327, 0);
 lean_ctor_release(x_2327, 1);
 x_2331 = x_2327;
} else {
 lean_dec_ref(x_2327);
 x_2331 = lean_box(0);
}
if (lean_is_scalar(x_2331)) {
 x_2332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2332 = x_2331;
}
lean_ctor_set(x_2332, 0, x_2244);
lean_ctor_set(x_2332, 1, x_2330);
return x_2332;
}
else
{
lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; 
x_2333 = lean_ctor_get(x_2327, 1);
lean_inc(x_2333);
lean_dec(x_2327);
x_2334 = lean_box(0);
x_2335 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2322, x_2334, x_3, x_4, x_5, x_6, x_2333);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2336 = lean_ctor_get(x_2335, 0);
lean_inc(x_2336);
x_2337 = lean_ctor_get(x_2335, 1);
lean_inc(x_2337);
if (lean_is_exclusive(x_2335)) {
 lean_ctor_release(x_2335, 0);
 lean_ctor_release(x_2335, 1);
 x_2338 = x_2335;
} else {
 lean_dec_ref(x_2335);
 x_2338 = lean_box(0);
}
if (lean_is_scalar(x_2338)) {
 x_2339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2339 = x_2338;
}
lean_ctor_set(x_2339, 0, x_2336);
lean_ctor_set(x_2339, 1, x_2337);
return x_2339;
}
}
else
{
lean_object* x_2340; lean_object* x_2341; 
lean_dec(x_2322);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2340 = lean_ctor_get(x_2327, 0);
lean_inc(x_2340);
x_2341 = lean_ctor_get(x_2327, 1);
lean_inc(x_2341);
lean_dec(x_2327);
x_8 = x_2340;
x_9 = x_2341;
goto block_16;
}
}
else
{
lean_object* x_2342; lean_object* x_2343; 
lean_dec(x_2322);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2342 = lean_ctor_get(x_2324, 0);
lean_inc(x_2342);
x_2343 = lean_ctor_get(x_2324, 1);
lean_inc(x_2343);
lean_dec(x_2324);
x_8 = x_2342;
x_9 = x_2343;
goto block_16;
}
}
else
{
lean_object* x_2344; lean_object* x_2345; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2344 = lean_ctor_get(x_2321, 0);
lean_inc(x_2344);
x_2345 = lean_ctor_get(x_2321, 1);
lean_inc(x_2345);
lean_dec(x_2321);
x_8 = x_2344;
x_9 = x_2345;
goto block_16;
}
}
else
{
lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; 
lean_dec(x_2307);
lean_dec(x_2284);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2346 = lean_ctor_get(x_2306, 1);
lean_inc(x_2346);
if (lean_is_exclusive(x_2306)) {
 lean_ctor_release(x_2306, 0);
 lean_ctor_release(x_2306, 1);
 x_2347 = x_2306;
} else {
 lean_dec_ref(x_2306);
 x_2347 = lean_box(0);
}
if (lean_is_scalar(x_2347)) {
 x_2348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2348 = x_2347;
}
lean_ctor_set(x_2348, 0, x_2244);
lean_ctor_set(x_2348, 1, x_2346);
return x_2348;
}
}
else
{
lean_object* x_2349; lean_object* x_2350; 
lean_dec(x_2284);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2349 = lean_ctor_get(x_2306, 0);
lean_inc(x_2349);
x_2350 = lean_ctor_get(x_2306, 1);
lean_inc(x_2350);
lean_dec(x_2306);
x_8 = x_2349;
x_9 = x_2350;
goto block_16;
}
}
else
{
lean_object* x_2351; lean_object* x_2352; 
lean_dec(x_2288);
lean_dec(x_2286);
lean_dec(x_2284);
lean_dec(x_2273);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2351 = lean_ctor_get(x_2289, 0);
lean_inc(x_2351);
x_2352 = lean_ctor_get(x_2289, 1);
lean_inc(x_2352);
lean_dec(x_2289);
x_8 = x_2351;
x_9 = x_2352;
goto block_16;
}
}
else
{
lean_object* x_2353; lean_object* x_2354; 
lean_dec(x_2284);
lean_dec(x_2273);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2353 = lean_ctor_get(x_2285, 0);
lean_inc(x_2353);
x_2354 = lean_ctor_get(x_2285, 1);
lean_inc(x_2354);
lean_dec(x_2285);
x_8 = x_2353;
x_9 = x_2354;
goto block_16;
}
}
}
else
{
lean_object* x_2355; lean_object* x_2356; 
lean_dec(x_2273);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2355 = lean_ctor_get(x_2278, 0);
lean_inc(x_2355);
x_2356 = lean_ctor_get(x_2278, 1);
lean_inc(x_2356);
lean_dec(x_2278);
x_8 = x_2355;
x_9 = x_2356;
goto block_16;
}
}
else
{
lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; 
lean_dec(x_2273);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2357 = lean_ctor_get(x_2274, 1);
lean_inc(x_2357);
if (lean_is_exclusive(x_2274)) {
 lean_ctor_release(x_2274, 0);
 lean_ctor_release(x_2274, 1);
 x_2358 = x_2274;
} else {
 lean_dec_ref(x_2274);
 x_2358 = lean_box(0);
}
lean_ctor_set(x_43, 0, x_2269);
if (lean_is_scalar(x_2358)) {
 x_2359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2359 = x_2358;
}
lean_ctor_set(x_2359, 0, x_43);
lean_ctor_set(x_2359, 1, x_2357);
return x_2359;
}
}
else
{
lean_object* x_2360; lean_object* x_2361; 
lean_dec(x_2273);
lean_dec(x_2269);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2360 = lean_ctor_get(x_2274, 0);
lean_inc(x_2360);
x_2361 = lean_ctor_get(x_2274, 1);
lean_inc(x_2361);
lean_dec(x_2274);
x_8 = x_2360;
x_9 = x_2361;
goto block_16;
}
}
else
{
lean_object* x_2362; lean_object* x_2363; 
lean_dec(x_2269);
lean_dec(x_2266);
lean_dec(x_2263);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2362 = lean_ctor_get(x_2270, 0);
lean_inc(x_2362);
x_2363 = lean_ctor_get(x_2270, 1);
lean_inc(x_2363);
lean_dec(x_2270);
x_8 = x_2362;
x_9 = x_2363;
goto block_16;
}
}
else
{
lean_object* x_2364; lean_object* x_2365; 
lean_dec(x_2256);
lean_dec(x_2254);
lean_dec(x_2252);
lean_dec(x_2250);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2364 = lean_ctor_get(x_2257, 0);
lean_inc(x_2364);
x_2365 = lean_ctor_get(x_2257, 1);
lean_inc(x_2365);
lean_dec(x_2257);
x_8 = x_2364;
x_9 = x_2365;
goto block_16;
}
}
else
{
lean_object* x_2366; lean_object* x_2367; 
lean_dec(x_2252);
lean_dec(x_2250);
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2366 = lean_ctor_get(x_2253, 0);
lean_inc(x_2366);
x_2367 = lean_ctor_get(x_2253, 1);
lean_inc(x_2367);
lean_dec(x_2253);
x_8 = x_2366;
x_9 = x_2367;
goto block_16;
}
}
else
{
lean_object* x_2368; lean_object* x_2369; 
lean_dec(x_2248);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2368 = lean_ctor_get(x_2249, 0);
lean_inc(x_2368);
x_2369 = lean_ctor_get(x_2249, 1);
lean_inc(x_2369);
lean_dec(x_2249);
x_8 = x_2368;
x_9 = x_2369;
goto block_16;
}
}
else
{
lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; 
lean_dec(x_2246);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2370 = lean_ctor_get(x_2245, 1);
lean_inc(x_2370);
if (lean_is_exclusive(x_2245)) {
 lean_ctor_release(x_2245, 0);
 lean_ctor_release(x_2245, 1);
 x_2371 = x_2245;
} else {
 lean_dec_ref(x_2245);
 x_2371 = lean_box(0);
}
if (lean_is_scalar(x_2371)) {
 x_2372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2372 = x_2371;
}
lean_ctor_set(x_2372, 0, x_2244);
lean_ctor_set(x_2372, 1, x_2370);
return x_2372;
}
}
else
{
lean_object* x_2373; lean_object* x_2374; 
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2373 = lean_ctor_get(x_2245, 0);
lean_inc(x_2373);
x_2374 = lean_ctor_get(x_2245, 1);
lean_inc(x_2374);
lean_dec(x_2245);
x_8 = x_2373;
x_9 = x_2374;
goto block_16;
}
}
else
{
lean_object* x_2375; lean_object* x_2376; 
lean_dec(x_2229);
lean_dec(x_2227);
lean_dec(x_2216);
lean_dec(x_2212);
lean_dec(x_2210);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2375 = lean_ctor_get(x_2230, 0);
lean_inc(x_2375);
x_2376 = lean_ctor_get(x_2230, 1);
lean_inc(x_2376);
lean_dec(x_2230);
x_8 = x_2375;
x_9 = x_2376;
goto block_16;
}
}
else
{
lean_object* x_2377; lean_object* x_2378; 
lean_dec(x_2216);
lean_dec(x_2212);
lean_dec(x_2210);
lean_dec(x_2208);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2377 = lean_ctor_get(x_2226, 0);
lean_inc(x_2377);
x_2378 = lean_ctor_get(x_2226, 1);
lean_inc(x_2378);
lean_dec(x_2226);
x_8 = x_2377;
x_9 = x_2378;
goto block_16;
}
}
}
else
{
lean_object* x_2379; lean_object* x_2380; 
lean_dec(x_2216);
lean_dec(x_2212);
lean_dec(x_2210);
lean_dec(x_2208);
lean_dec(x_2198);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2379 = lean_ctor_get(x_2218, 0);
lean_inc(x_2379);
x_2380 = lean_ctor_get(x_2218, 1);
lean_inc(x_2380);
lean_dec(x_2218);
x_8 = x_2379;
x_9 = x_2380;
goto block_16;
}
}
else
{
lean_object* x_2381; lean_object* x_2382; 
lean_dec(x_2212);
lean_dec(x_2210);
lean_dec(x_2208);
lean_dec(x_2198);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2381 = lean_ctor_get(x_2213, 0);
lean_inc(x_2381);
x_2382 = lean_ctor_get(x_2213, 1);
lean_inc(x_2382);
lean_dec(x_2213);
x_8 = x_2381;
x_9 = x_2382;
goto block_16;
}
}
else
{
lean_object* x_2383; lean_object* x_2384; 
lean_dec(x_2208);
lean_dec(x_2207);
lean_dec(x_2198);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2383 = lean_ctor_get(x_2209, 0);
lean_inc(x_2383);
x_2384 = lean_ctor_get(x_2209, 1);
lean_inc(x_2384);
lean_dec(x_2209);
x_8 = x_2383;
x_9 = x_2384;
goto block_16;
}
}
else
{
lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; 
lean_dec(x_2205);
lean_dec(x_2204);
lean_dec(x_2198);
lean_dec(x_2197);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2385 = lean_ctor_get(x_2202, 1);
lean_inc(x_2385);
if (lean_is_exclusive(x_2202)) {
 lean_ctor_release(x_2202, 0);
 lean_ctor_release(x_2202, 1);
 x_2386 = x_2202;
} else {
 lean_dec_ref(x_2202);
 x_2386 = lean_box(0);
}
x_2387 = lean_box(0);
if (lean_is_scalar(x_2386)) {
 x_2388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2388 = x_2386;
}
lean_ctor_set(x_2388, 0, x_2387);
lean_ctor_set(x_2388, 1, x_2385);
return x_2388;
}
}
else
{
lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; 
lean_dec(x_2204);
lean_dec(x_2203);
lean_dec(x_2198);
lean_dec(x_2197);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2389 = lean_ctor_get(x_2202, 1);
lean_inc(x_2389);
if (lean_is_exclusive(x_2202)) {
 lean_ctor_release(x_2202, 0);
 lean_ctor_release(x_2202, 1);
 x_2390 = x_2202;
} else {
 lean_dec_ref(x_2202);
 x_2390 = lean_box(0);
}
x_2391 = lean_box(0);
if (lean_is_scalar(x_2390)) {
 x_2392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2392 = x_2390;
}
lean_ctor_set(x_2392, 0, x_2391);
lean_ctor_set(x_2392, 1, x_2389);
return x_2392;
}
}
else
{
lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; 
lean_dec(x_2203);
lean_dec(x_2198);
lean_dec(x_2197);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2393 = lean_ctor_get(x_2202, 1);
lean_inc(x_2393);
if (lean_is_exclusive(x_2202)) {
 lean_ctor_release(x_2202, 0);
 lean_ctor_release(x_2202, 1);
 x_2394 = x_2202;
} else {
 lean_dec_ref(x_2202);
 x_2394 = lean_box(0);
}
x_2395 = lean_box(0);
if (lean_is_scalar(x_2394)) {
 x_2396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2396 = x_2394;
}
lean_ctor_set(x_2396, 0, x_2395);
lean_ctor_set(x_2396, 1, x_2393);
return x_2396;
}
}
else
{
lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; uint8_t x_2400; 
lean_dec(x_2198);
lean_dec(x_2197);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2397 = lean_ctor_get(x_2202, 0);
lean_inc(x_2397);
x_2398 = lean_ctor_get(x_2202, 1);
lean_inc(x_2398);
if (lean_is_exclusive(x_2202)) {
 lean_ctor_release(x_2202, 0);
 lean_ctor_release(x_2202, 1);
 x_2399 = x_2202;
} else {
 lean_dec_ref(x_2202);
 x_2399 = lean_box(0);
}
x_2400 = l_Lean_Exception_isInterrupt(x_2397);
if (x_2400 == 0)
{
uint8_t x_2401; 
x_2401 = l_Lean_Exception_isRuntime(x_2397);
if (x_2401 == 0)
{
lean_object* x_2402; lean_object* x_2403; 
lean_dec(x_2397);
x_2402 = lean_box(0);
if (lean_is_scalar(x_2399)) {
 x_2403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2403 = x_2399;
 lean_ctor_set_tag(x_2403, 0);
}
lean_ctor_set(x_2403, 0, x_2402);
lean_ctor_set(x_2403, 1, x_2398);
return x_2403;
}
else
{
lean_object* x_2404; 
if (lean_is_scalar(x_2399)) {
 x_2404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2404 = x_2399;
}
lean_ctor_set(x_2404, 0, x_2397);
lean_ctor_set(x_2404, 1, x_2398);
return x_2404;
}
}
else
{
lean_object* x_2405; 
if (lean_is_scalar(x_2399)) {
 x_2405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2405 = x_2399;
}
lean_ctor_set(x_2405, 0, x_2397);
lean_ctor_set(x_2405, 1, x_2398);
return x_2405;
}
}
}
else
{
lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; uint8_t x_2409; 
lean_dec(x_2198);
lean_dec(x_2197);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2406 = lean_ctor_get(x_2199, 0);
lean_inc(x_2406);
x_2407 = lean_ctor_get(x_2199, 1);
lean_inc(x_2407);
if (lean_is_exclusive(x_2199)) {
 lean_ctor_release(x_2199, 0);
 lean_ctor_release(x_2199, 1);
 x_2408 = x_2199;
} else {
 lean_dec_ref(x_2199);
 x_2408 = lean_box(0);
}
x_2409 = l_Lean_Exception_isInterrupt(x_2406);
if (x_2409 == 0)
{
uint8_t x_2410; 
x_2410 = l_Lean_Exception_isRuntime(x_2406);
if (x_2410 == 0)
{
lean_object* x_2411; lean_object* x_2412; 
lean_dec(x_2406);
x_2411 = lean_box(0);
if (lean_is_scalar(x_2408)) {
 x_2412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2412 = x_2408;
 lean_ctor_set_tag(x_2412, 0);
}
lean_ctor_set(x_2412, 0, x_2411);
lean_ctor_set(x_2412, 1, x_2407);
return x_2412;
}
else
{
lean_object* x_2413; 
if (lean_is_scalar(x_2408)) {
 x_2413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2413 = x_2408;
}
lean_ctor_set(x_2413, 0, x_2406);
lean_ctor_set(x_2413, 1, x_2407);
return x_2413;
}
}
else
{
lean_object* x_2414; 
if (lean_is_scalar(x_2408)) {
 x_2414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2414 = x_2408;
}
lean_ctor_set(x_2414, 0, x_2406);
lean_ctor_set(x_2414, 1, x_2407);
return x_2414;
}
}
}
else
{
lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; 
lean_dec(x_2195);
lean_dec(x_2194);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2415 = lean_ctor_get(x_2192, 1);
lean_inc(x_2415);
if (lean_is_exclusive(x_2192)) {
 lean_ctor_release(x_2192, 0);
 lean_ctor_release(x_2192, 1);
 x_2416 = x_2192;
} else {
 lean_dec_ref(x_2192);
 x_2416 = lean_box(0);
}
x_2417 = lean_box(0);
if (lean_is_scalar(x_2416)) {
 x_2418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2418 = x_2416;
}
lean_ctor_set(x_2418, 0, x_2417);
lean_ctor_set(x_2418, 1, x_2415);
return x_2418;
}
}
else
{
lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; 
lean_dec(x_2194);
lean_dec(x_2193);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2419 = lean_ctor_get(x_2192, 1);
lean_inc(x_2419);
if (lean_is_exclusive(x_2192)) {
 lean_ctor_release(x_2192, 0);
 lean_ctor_release(x_2192, 1);
 x_2420 = x_2192;
} else {
 lean_dec_ref(x_2192);
 x_2420 = lean_box(0);
}
x_2421 = lean_box(0);
if (lean_is_scalar(x_2420)) {
 x_2422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2422 = x_2420;
}
lean_ctor_set(x_2422, 0, x_2421);
lean_ctor_set(x_2422, 1, x_2419);
return x_2422;
}
}
else
{
lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; 
lean_dec(x_2193);
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2423 = lean_ctor_get(x_2192, 1);
lean_inc(x_2423);
if (lean_is_exclusive(x_2192)) {
 lean_ctor_release(x_2192, 0);
 lean_ctor_release(x_2192, 1);
 x_2424 = x_2192;
} else {
 lean_dec_ref(x_2192);
 x_2424 = lean_box(0);
}
x_2425 = lean_box(0);
if (lean_is_scalar(x_2424)) {
 x_2426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2426 = x_2424;
}
lean_ctor_set(x_2426, 0, x_2425);
lean_ctor_set(x_2426, 1, x_2423);
return x_2426;
}
}
else
{
lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; uint8_t x_2430; 
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2427 = lean_ctor_get(x_2192, 0);
lean_inc(x_2427);
x_2428 = lean_ctor_get(x_2192, 1);
lean_inc(x_2428);
if (lean_is_exclusive(x_2192)) {
 lean_ctor_release(x_2192, 0);
 lean_ctor_release(x_2192, 1);
 x_2429 = x_2192;
} else {
 lean_dec_ref(x_2192);
 x_2429 = lean_box(0);
}
x_2430 = l_Lean_Exception_isInterrupt(x_2427);
if (x_2430 == 0)
{
uint8_t x_2431; 
x_2431 = l_Lean_Exception_isRuntime(x_2427);
if (x_2431 == 0)
{
lean_object* x_2432; lean_object* x_2433; 
lean_dec(x_2427);
x_2432 = lean_box(0);
if (lean_is_scalar(x_2429)) {
 x_2433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2433 = x_2429;
 lean_ctor_set_tag(x_2433, 0);
}
lean_ctor_set(x_2433, 0, x_2432);
lean_ctor_set(x_2433, 1, x_2428);
return x_2433;
}
else
{
lean_object* x_2434; 
if (lean_is_scalar(x_2429)) {
 x_2434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2434 = x_2429;
}
lean_ctor_set(x_2434, 0, x_2427);
lean_ctor_set(x_2434, 1, x_2428);
return x_2434;
}
}
else
{
lean_object* x_2435; 
if (lean_is_scalar(x_2429)) {
 x_2435 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2435 = x_2429;
}
lean_ctor_set(x_2435, 0, x_2427);
lean_ctor_set(x_2435, 1, x_2428);
return x_2435;
}
}
}
else
{
lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; uint8_t x_2439; 
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2436 = lean_ctor_get(x_2189, 0);
lean_inc(x_2436);
x_2437 = lean_ctor_get(x_2189, 1);
lean_inc(x_2437);
if (lean_is_exclusive(x_2189)) {
 lean_ctor_release(x_2189, 0);
 lean_ctor_release(x_2189, 1);
 x_2438 = x_2189;
} else {
 lean_dec_ref(x_2189);
 x_2438 = lean_box(0);
}
x_2439 = l_Lean_Exception_isInterrupt(x_2436);
if (x_2439 == 0)
{
uint8_t x_2440; 
x_2440 = l_Lean_Exception_isRuntime(x_2436);
if (x_2440 == 0)
{
lean_object* x_2441; lean_object* x_2442; 
lean_dec(x_2436);
x_2441 = lean_box(0);
if (lean_is_scalar(x_2438)) {
 x_2442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2442 = x_2438;
 lean_ctor_set_tag(x_2442, 0);
}
lean_ctor_set(x_2442, 0, x_2441);
lean_ctor_set(x_2442, 1, x_2437);
return x_2442;
}
else
{
lean_object* x_2443; 
if (lean_is_scalar(x_2438)) {
 x_2443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2443 = x_2438;
}
lean_ctor_set(x_2443, 0, x_2436);
lean_ctor_set(x_2443, 1, x_2437);
return x_2443;
}
}
else
{
lean_object* x_2444; 
if (lean_is_scalar(x_2438)) {
 x_2444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2444 = x_2438;
}
lean_ctor_set(x_2444, 0, x_2436);
lean_ctor_set(x_2444, 1, x_2437);
return x_2444;
}
}
}
}
else
{
lean_object* x_2445; lean_object* x_2446; 
lean_dec(x_26);
lean_dec(x_19);
x_2445 = lean_ctor_get(x_2179, 1);
lean_inc(x_2445);
lean_dec(x_2179);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2446 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_2445);
if (lean_obj_tag(x_2446) == 0)
{
lean_object* x_2447; 
x_2447 = lean_ctor_get(x_2446, 0);
lean_inc(x_2447);
if (lean_obj_tag(x_2447) == 0)
{
lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; lean_object* x_2453; 
lean_dec(x_2178);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_1);
x_2448 = lean_ctor_get(x_2446, 1);
lean_inc(x_2448);
lean_dec(x_2446);
x_2449 = l_Lean_Meta_SavedState_restore(x_2176, x_3, x_4, x_5, x_6, x_2448);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2176);
x_2450 = lean_ctor_get(x_2449, 1);
lean_inc(x_2450);
if (lean_is_exclusive(x_2449)) {
 lean_ctor_release(x_2449, 0);
 lean_ctor_release(x_2449, 1);
 x_2451 = x_2449;
} else {
 lean_dec_ref(x_2449);
 x_2451 = lean_box(0);
}
x_2452 = lean_box(0);
if (lean_is_scalar(x_2451)) {
 x_2453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2453 = x_2451;
}
lean_ctor_set(x_2453, 0, x_2452);
lean_ctor_set(x_2453, 1, x_2450);
return x_2453;
}
else
{
lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2478; lean_object* x_2479; 
x_2454 = lean_ctor_get(x_2446, 1);
lean_inc(x_2454);
if (lean_is_exclusive(x_2446)) {
 lean_ctor_release(x_2446, 0);
 lean_ctor_release(x_2446, 1);
 x_2455 = x_2446;
} else {
 lean_dec_ref(x_2446);
 x_2455 = lean_box(0);
}
x_2456 = lean_ctor_get(x_2447, 0);
lean_inc(x_2456);
if (lean_is_exclusive(x_2447)) {
 lean_ctor_release(x_2447, 0);
 x_2457 = x_2447;
} else {
 lean_dec_ref(x_2447);
 x_2457 = lean_box(0);
}
if (lean_is_scalar(x_2457)) {
 x_2458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2458 = x_2457;
}
lean_ctor_set(x_2458, 0, x_2173);
lean_ctor_set(x_43, 0, x_2174);
lean_ctor_set(x_29, 0, x_41);
x_2459 = lean_box(0);
x_2460 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2460, 0, x_2456);
x_2461 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2461, 0, x_1);
x_2462 = lean_box(0);
if (lean_is_scalar(x_2178)) {
 x_2463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2463 = x_2178;
 lean_ctor_set_tag(x_2463, 1);
}
lean_ctor_set(x_2463, 0, x_2461);
lean_ctor_set(x_2463, 1, x_2462);
x_2464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2464, 0, x_2460);
lean_ctor_set(x_2464, 1, x_2463);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_2464);
lean_ctor_set(x_37, 0, x_2459);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_29);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_43);
x_2465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2465, 0, x_2458);
lean_ctor_set(x_2465, 1, x_17);
x_2466 = lean_array_mk(x_2465);
x_2478 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2479 = l_Lean_Meta_mkAppOptM(x_2478, x_2466, x_3, x_4, x_5, x_6, x_2454);
if (lean_obj_tag(x_2479) == 0)
{
lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; 
x_2480 = lean_ctor_get(x_2479, 0);
lean_inc(x_2480);
x_2481 = lean_ctor_get(x_2479, 1);
lean_inc(x_2481);
lean_dec(x_2479);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2482 = l_Lean_Meta_expandCoe(x_2480, x_3, x_4, x_5, x_6, x_2481);
if (lean_obj_tag(x_2482) == 0)
{
lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; 
lean_dec(x_2455);
lean_dec(x_2176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2483 = lean_ctor_get(x_2482, 0);
lean_inc(x_2483);
x_2484 = lean_ctor_get(x_2482, 1);
lean_inc(x_2484);
if (lean_is_exclusive(x_2482)) {
 lean_ctor_release(x_2482, 0);
 lean_ctor_release(x_2482, 1);
 x_2485 = x_2482;
} else {
 lean_dec_ref(x_2482);
 x_2485 = lean_box(0);
}
x_2486 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2486, 0, x_2483);
if (lean_is_scalar(x_2485)) {
 x_2487 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2487 = x_2485;
}
lean_ctor_set(x_2487, 0, x_2486);
lean_ctor_set(x_2487, 1, x_2484);
return x_2487;
}
else
{
lean_object* x_2488; lean_object* x_2489; 
x_2488 = lean_ctor_get(x_2482, 0);
lean_inc(x_2488);
x_2489 = lean_ctor_get(x_2482, 1);
lean_inc(x_2489);
lean_dec(x_2482);
x_2467 = x_2488;
x_2468 = x_2489;
goto block_2477;
}
}
else
{
lean_object* x_2490; lean_object* x_2491; 
x_2490 = lean_ctor_get(x_2479, 0);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_2479, 1);
lean_inc(x_2491);
lean_dec(x_2479);
x_2467 = x_2490;
x_2468 = x_2491;
goto block_2477;
}
block_2477:
{
uint8_t x_2469; 
x_2469 = l_Lean_Exception_isInterrupt(x_2467);
if (x_2469 == 0)
{
uint8_t x_2470; 
x_2470 = l_Lean_Exception_isRuntime(x_2467);
if (x_2470 == 0)
{
lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; 
lean_dec(x_2467);
lean_dec(x_2455);
x_2471 = l_Lean_Meta_SavedState_restore(x_2176, x_3, x_4, x_5, x_6, x_2468);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2176);
x_2472 = lean_ctor_get(x_2471, 1);
lean_inc(x_2472);
if (lean_is_exclusive(x_2471)) {
 lean_ctor_release(x_2471, 0);
 lean_ctor_release(x_2471, 1);
 x_2473 = x_2471;
} else {
 lean_dec_ref(x_2471);
 x_2473 = lean_box(0);
}
if (lean_is_scalar(x_2473)) {
 x_2474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2474 = x_2473;
}
lean_ctor_set(x_2474, 0, x_2459);
lean_ctor_set(x_2474, 1, x_2472);
return x_2474;
}
else
{
lean_object* x_2475; 
lean_dec(x_2176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_2455)) {
 x_2475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2475 = x_2455;
 lean_ctor_set_tag(x_2475, 1);
}
lean_ctor_set(x_2475, 0, x_2467);
lean_ctor_set(x_2475, 1, x_2468);
return x_2475;
}
}
else
{
lean_object* x_2476; 
lean_dec(x_2176);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_2455)) {
 x_2476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2476 = x_2455;
 lean_ctor_set_tag(x_2476, 1);
}
lean_ctor_set(x_2476, 0, x_2467);
lean_ctor_set(x_2476, 1, x_2468);
return x_2476;
}
}
}
}
else
{
lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; 
lean_dec(x_2178);
lean_dec(x_2176);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2492 = lean_ctor_get(x_2446, 0);
lean_inc(x_2492);
x_2493 = lean_ctor_get(x_2446, 1);
lean_inc(x_2493);
if (lean_is_exclusive(x_2446)) {
 lean_ctor_release(x_2446, 0);
 lean_ctor_release(x_2446, 1);
 x_2494 = x_2446;
} else {
 lean_dec_ref(x_2446);
 x_2494 = lean_box(0);
}
if (lean_is_scalar(x_2494)) {
 x_2495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2495 = x_2494;
}
lean_ctor_set(x_2495, 0, x_2492);
lean_ctor_set(x_2495, 1, x_2493);
return x_2495;
}
}
}
else
{
lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; 
lean_dec(x_2178);
lean_dec(x_2176);
lean_dec(x_2174);
lean_dec(x_2173);
lean_free_object(x_43);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2496 = lean_ctor_get(x_2179, 0);
lean_inc(x_2496);
x_2497 = lean_ctor_get(x_2179, 1);
lean_inc(x_2497);
if (lean_is_exclusive(x_2179)) {
 lean_ctor_release(x_2179, 0);
 lean_ctor_release(x_2179, 1);
 x_2498 = x_2179;
} else {
 lean_dec_ref(x_2179);
 x_2498 = lean_box(0);
}
if (lean_is_scalar(x_2498)) {
 x_2499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2499 = x_2498;
}
lean_ctor_set(x_2499, 0, x_2496);
lean_ctor_set(x_2499, 1, x_2497);
return x_2499;
}
}
}
else
{
lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; 
x_2500 = lean_ctor_get(x_43, 0);
lean_inc(x_2500);
lean_dec(x_43);
x_2501 = lean_ctor_get(x_42, 1);
lean_inc(x_2501);
lean_dec(x_42);
x_2502 = lean_ctor_get(x_2500, 0);
lean_inc(x_2502);
x_2503 = lean_ctor_get(x_2500, 1);
lean_inc(x_2503);
if (lean_is_exclusive(x_2500)) {
 lean_ctor_release(x_2500, 0);
 lean_ctor_release(x_2500, 1);
 x_2504 = x_2500;
} else {
 lean_dec_ref(x_2500);
 x_2504 = lean_box(0);
}
x_2505 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_2501);
x_2506 = lean_ctor_get(x_2505, 0);
lean_inc(x_2506);
x_2507 = lean_ctor_get(x_2505, 1);
lean_inc(x_2507);
if (lean_is_exclusive(x_2505)) {
 lean_ctor_release(x_2505, 0);
 lean_ctor_release(x_2505, 1);
 x_2508 = x_2505;
} else {
 lean_dec_ref(x_2505);
 x_2508 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
lean_inc(x_2502);
x_2509 = l_Lean_Meta_isExprDefEq(x_2502, x_40, x_3, x_4, x_5, x_6, x_2507);
if (lean_obj_tag(x_2509) == 0)
{
lean_object* x_2510; uint8_t x_2511; 
x_2510 = lean_ctor_get(x_2509, 0);
lean_inc(x_2510);
x_2511 = lean_unbox(x_2510);
lean_dec(x_2510);
if (x_2511 == 0)
{
lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; lean_object* x_2515; uint8_t x_2516; 
lean_dec(x_2506);
lean_free_object(x_29);
x_2512 = lean_ctor_get(x_2509, 1);
lean_inc(x_2512);
if (lean_is_exclusive(x_2509)) {
 lean_ctor_release(x_2509, 0);
 lean_ctor_release(x_2509, 1);
 x_2513 = x_2509;
} else {
 lean_dec_ref(x_2509);
 x_2513 = lean_box(0);
}
x_2514 = lean_ctor_get(x_5, 2);
lean_inc(x_2514);
x_2515 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_2516 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2514, x_2515);
lean_dec(x_2514);
if (x_2516 == 0)
{
lean_object* x_2517; lean_object* x_2518; 
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2517 = lean_box(0);
if (lean_is_scalar(x_2513)) {
 x_2518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2518 = x_2513;
}
lean_ctor_set(x_2518, 0, x_2517);
lean_ctor_set(x_2518, 1, x_2512);
return x_2518;
}
else
{
lean_object* x_2519; 
lean_dec(x_2513);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2502);
x_2519 = lean_infer_type(x_2502, x_3, x_4, x_5, x_6, x_2512);
if (lean_obj_tag(x_2519) == 0)
{
lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; 
x_2520 = lean_ctor_get(x_2519, 0);
lean_inc(x_2520);
x_2521 = lean_ctor_get(x_2519, 1);
lean_inc(x_2521);
lean_dec(x_2519);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2522 = lean_whnf(x_2520, x_3, x_4, x_5, x_6, x_2521);
if (lean_obj_tag(x_2522) == 0)
{
lean_object* x_2523; 
x_2523 = lean_ctor_get(x_2522, 0);
lean_inc(x_2523);
if (lean_obj_tag(x_2523) == 7)
{
lean_object* x_2524; 
x_2524 = lean_ctor_get(x_2523, 1);
lean_inc(x_2524);
if (lean_obj_tag(x_2524) == 3)
{
lean_object* x_2525; 
x_2525 = lean_ctor_get(x_2523, 2);
lean_inc(x_2525);
lean_dec(x_2523);
if (lean_obj_tag(x_2525) == 3)
{
lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; 
x_2526 = lean_ctor_get(x_2522, 1);
lean_inc(x_2526);
lean_dec(x_2522);
x_2527 = lean_ctor_get(x_2524, 0);
lean_inc(x_2527);
lean_dec(x_2524);
x_2528 = lean_ctor_get(x_2525, 0);
lean_inc(x_2528);
lean_dec(x_2525);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_2529 = lean_infer_type(x_40, x_3, x_4, x_5, x_6, x_2526);
if (lean_obj_tag(x_2529) == 0)
{
lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; 
x_2530 = lean_ctor_get(x_2529, 0);
lean_inc(x_2530);
x_2531 = lean_ctor_get(x_2529, 1);
lean_inc(x_2531);
lean_dec(x_2529);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2532 = lean_whnf(x_2530, x_3, x_4, x_5, x_6, x_2531);
if (lean_obj_tag(x_2532) == 0)
{
lean_object* x_2533; 
x_2533 = lean_ctor_get(x_2532, 0);
lean_inc(x_2533);
if (lean_obj_tag(x_2533) == 7)
{
lean_object* x_2534; 
x_2534 = lean_ctor_get(x_2533, 1);
lean_inc(x_2534);
if (lean_obj_tag(x_2534) == 3)
{
lean_object* x_2535; 
x_2535 = lean_ctor_get(x_2533, 2);
lean_inc(x_2535);
lean_dec(x_2533);
if (lean_obj_tag(x_2535) == 3)
{
lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; 
x_2536 = lean_ctor_get(x_2532, 1);
lean_inc(x_2536);
lean_dec(x_2532);
x_2537 = lean_ctor_get(x_2534, 0);
lean_inc(x_2537);
lean_dec(x_2534);
x_2538 = lean_ctor_get(x_2535, 0);
lean_inc(x_2538);
lean_dec(x_2535);
x_2539 = l_Lean_Meta_decLevel(x_2527, x_3, x_4, x_5, x_6, x_2536);
if (lean_obj_tag(x_2539) == 0)
{
lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; 
x_2540 = lean_ctor_get(x_2539, 0);
lean_inc(x_2540);
x_2541 = lean_ctor_get(x_2539, 1);
lean_inc(x_2541);
if (lean_is_exclusive(x_2539)) {
 lean_ctor_release(x_2539, 0);
 lean_ctor_release(x_2539, 1);
 x_2542 = x_2539;
} else {
 lean_dec_ref(x_2539);
 x_2542 = lean_box(0);
}
x_2543 = l_Lean_Meta_decLevel(x_2537, x_3, x_4, x_5, x_6, x_2541);
if (lean_obj_tag(x_2543) == 0)
{
lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; uint8_t x_2547; lean_object* x_2548; 
x_2544 = lean_ctor_get(x_2543, 0);
lean_inc(x_2544);
x_2545 = lean_ctor_get(x_2543, 1);
lean_inc(x_2545);
if (lean_is_exclusive(x_2543)) {
 lean_ctor_release(x_2543, 0);
 lean_ctor_release(x_2543, 1);
 x_2546 = x_2543;
} else {
 lean_dec_ref(x_2543);
 x_2546 = lean_box(0);
}
x_2547 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2540);
x_2548 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_2540, x_2544, x_2547, x_3, x_4, x_5, x_6, x_2545);
if (lean_obj_tag(x_2548) == 0)
{
lean_object* x_2549; uint8_t x_2550; 
x_2549 = lean_ctor_get(x_2548, 0);
lean_inc(x_2549);
x_2550 = lean_unbox(x_2549);
lean_dec(x_2549);
if (x_2550 == 0)
{
lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; 
lean_dec(x_2546);
lean_dec(x_2542);
lean_dec(x_2540);
lean_dec(x_2538);
lean_dec(x_2528);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2551 = lean_ctor_get(x_2548, 1);
lean_inc(x_2551);
if (lean_is_exclusive(x_2548)) {
 lean_ctor_release(x_2548, 0);
 lean_ctor_release(x_2548, 1);
 x_2552 = x_2548;
} else {
 lean_dec_ref(x_2548);
 x_2552 = lean_box(0);
}
x_2553 = lean_box(0);
if (lean_is_scalar(x_2552)) {
 x_2554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2554 = x_2552;
}
lean_ctor_set(x_2554, 0, x_2553);
lean_ctor_set(x_2554, 1, x_2551);
return x_2554;
}
else
{
lean_object* x_2555; lean_object* x_2556; 
x_2555 = lean_ctor_get(x_2548, 1);
lean_inc(x_2555);
lean_dec(x_2548);
x_2556 = l_Lean_Meta_decLevel(x_2528, x_3, x_4, x_5, x_6, x_2555);
if (lean_obj_tag(x_2556) == 0)
{
lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; 
x_2557 = lean_ctor_get(x_2556, 0);
lean_inc(x_2557);
x_2558 = lean_ctor_get(x_2556, 1);
lean_inc(x_2558);
if (lean_is_exclusive(x_2556)) {
 lean_ctor_release(x_2556, 0);
 lean_ctor_release(x_2556, 1);
 x_2559 = x_2556;
} else {
 lean_dec_ref(x_2556);
 x_2559 = lean_box(0);
}
x_2560 = l_Lean_Meta_decLevel(x_2538, x_3, x_4, x_5, x_6, x_2558);
if (lean_obj_tag(x_2560) == 0)
{
lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; 
x_2561 = lean_ctor_get(x_2560, 0);
lean_inc(x_2561);
x_2562 = lean_ctor_get(x_2560, 1);
lean_inc(x_2562);
if (lean_is_exclusive(x_2560)) {
 lean_ctor_release(x_2560, 0);
 lean_ctor_release(x_2560, 1);
 x_2563 = x_2560;
} else {
 lean_dec_ref(x_2560);
 x_2563 = lean_box(0);
}
x_2564 = lean_box(0);
if (lean_is_scalar(x_2563)) {
 x_2565 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2565 = x_2563;
 lean_ctor_set_tag(x_2565, 1);
}
lean_ctor_set(x_2565, 0, x_2561);
lean_ctor_set(x_2565, 1, x_2564);
if (lean_is_scalar(x_2559)) {
 x_2566 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2566 = x_2559;
 lean_ctor_set_tag(x_2566, 1);
}
lean_ctor_set(x_2566, 0, x_2557);
lean_ctor_set(x_2566, 1, x_2565);
if (lean_is_scalar(x_2546)) {
 x_2567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2567 = x_2546;
 lean_ctor_set_tag(x_2567, 1);
}
lean_ctor_set(x_2567, 0, x_2540);
lean_ctor_set(x_2567, 1, x_2566);
x_2568 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2569 = l_Lean_Expr_const___override(x_2568, x_2567);
lean_inc(x_40);
if (lean_is_scalar(x_2542)) {
 x_2570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2570 = x_2542;
 lean_ctor_set_tag(x_2570, 1);
}
lean_ctor_set(x_2570, 0, x_40);
lean_ctor_set(x_2570, 1, x_2564);
lean_inc(x_2502);
if (lean_is_scalar(x_2508)) {
 x_2571 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2571 = x_2508;
 lean_ctor_set_tag(x_2571, 1);
}
lean_ctor_set(x_2571, 0, x_2502);
lean_ctor_set(x_2571, 1, x_2570);
x_2572 = lean_array_mk(x_2571);
x_2573 = l_Lean_mkAppN(x_2569, x_2572);
lean_dec(x_2572);
x_2574 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2575 = l_Lean_Meta_trySynthInstance(x_2573, x_2574, x_3, x_4, x_5, x_6, x_2562);
if (lean_obj_tag(x_2575) == 0)
{
lean_object* x_2576; 
x_2576 = lean_ctor_get(x_2575, 0);
lean_inc(x_2576);
if (lean_obj_tag(x_2576) == 1)
{
lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; 
x_2577 = lean_ctor_get(x_2575, 1);
lean_inc(x_2577);
lean_dec(x_2575);
x_2578 = lean_ctor_get(x_2576, 0);
lean_inc(x_2578);
lean_dec(x_2576);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2503);
x_2579 = l_Lean_Meta_getDecLevel(x_2503, x_3, x_4, x_5, x_6, x_2577);
if (lean_obj_tag(x_2579) == 0)
{
lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; 
x_2580 = lean_ctor_get(x_2579, 0);
lean_inc(x_2580);
x_2581 = lean_ctor_get(x_2579, 1);
lean_inc(x_2581);
if (lean_is_exclusive(x_2579)) {
 lean_ctor_release(x_2579, 0);
 lean_ctor_release(x_2579, 1);
 x_2582 = x_2579;
} else {
 lean_dec_ref(x_2579);
 x_2582 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2583 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_2581);
if (lean_obj_tag(x_2583) == 0)
{
lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; 
x_2584 = lean_ctor_get(x_2583, 0);
lean_inc(x_2584);
x_2585 = lean_ctor_get(x_2583, 1);
lean_inc(x_2585);
if (lean_is_exclusive(x_2583)) {
 lean_ctor_release(x_2583, 0);
 lean_ctor_release(x_2583, 1);
 x_2586 = x_2583;
} else {
 lean_dec_ref(x_2583);
 x_2586 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_2587 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_2585);
if (lean_obj_tag(x_2587) == 0)
{
lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; 
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
if (lean_is_scalar(x_2590)) {
 x_2591 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2591 = x_2590;
 lean_ctor_set_tag(x_2591, 1);
}
lean_ctor_set(x_2591, 0, x_2588);
lean_ctor_set(x_2591, 1, x_2564);
if (lean_is_scalar(x_2586)) {
 x_2592 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2592 = x_2586;
 lean_ctor_set_tag(x_2592, 1);
}
lean_ctor_set(x_2592, 0, x_2584);
lean_ctor_set(x_2592, 1, x_2591);
if (lean_is_scalar(x_2582)) {
 x_2593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2593 = x_2582;
 lean_ctor_set_tag(x_2593, 1);
}
lean_ctor_set(x_2593, 0, x_2580);
lean_ctor_set(x_2593, 1, x_2592);
x_2594 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_2593);
x_2595 = l_Lean_Expr_const___override(x_2594, x_2593);
if (lean_is_scalar(x_2504)) {
 x_2596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2596 = x_2504;
 lean_ctor_set_tag(x_2596, 1);
}
lean_ctor_set(x_2596, 0, x_1);
lean_ctor_set(x_2596, 1, x_2564);
lean_inc(x_2596);
lean_inc(x_2503);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_2596);
lean_ctor_set(x_37, 0, x_2503);
lean_inc(x_2578);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_2578);
lean_inc(x_40);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_40);
lean_inc(x_2502);
x_2597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2597, 0, x_2502);
lean_ctor_set(x_2597, 1, x_17);
x_2598 = lean_array_mk(x_2597);
x_2599 = l_Lean_mkAppN(x_2595, x_2598);
lean_dec(x_2598);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2599);
x_2600 = lean_infer_type(x_2599, x_3, x_4, x_5, x_6, x_2589);
if (lean_obj_tag(x_2600) == 0)
{
lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; 
x_2601 = lean_ctor_get(x_2600, 0);
lean_inc(x_2601);
x_2602 = lean_ctor_get(x_2600, 1);
lean_inc(x_2602);
if (lean_is_exclusive(x_2600)) {
 lean_ctor_release(x_2600, 0);
 lean_ctor_release(x_2600, 1);
 x_2603 = x_2600;
} else {
 lean_dec_ref(x_2600);
 x_2603 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_2604 = l_Lean_Meta_isExprDefEq(x_19, x_2601, x_3, x_4, x_5, x_6, x_2602);
if (lean_obj_tag(x_2604) == 0)
{
lean_object* x_2605; uint8_t x_2606; 
x_2605 = lean_ctor_get(x_2604, 0);
lean_inc(x_2605);
x_2606 = lean_unbox(x_2605);
lean_dec(x_2605);
if (x_2606 == 0)
{
lean_object* x_2607; lean_object* x_2608; 
lean_dec(x_2599);
x_2607 = lean_ctor_get(x_2604, 1);
lean_inc(x_2607);
lean_dec(x_2604);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_2608 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_2607);
if (lean_obj_tag(x_2608) == 0)
{
lean_object* x_2609; 
x_2609 = lean_ctor_get(x_2608, 0);
lean_inc(x_2609);
if (lean_obj_tag(x_2609) == 0)
{
lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; 
lean_dec(x_2603);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2610 = lean_ctor_get(x_2608, 1);
lean_inc(x_2610);
if (lean_is_exclusive(x_2608)) {
 lean_ctor_release(x_2608, 0);
 lean_ctor_release(x_2608, 1);
 x_2611 = x_2608;
} else {
 lean_dec_ref(x_2608);
 x_2611 = lean_box(0);
}
if (lean_is_scalar(x_2611)) {
 x_2612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2612 = x_2611;
}
lean_ctor_set(x_2612, 0, x_2574);
lean_ctor_set(x_2612, 1, x_2610);
return x_2612;
}
else
{
lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; 
x_2613 = lean_ctor_get(x_2608, 1);
lean_inc(x_2613);
lean_dec(x_2608);
x_2614 = lean_ctor_get(x_2609, 0);
lean_inc(x_2614);
lean_dec(x_2609);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2503);
x_2615 = l_Lean_Meta_getLevel(x_2503, x_3, x_4, x_5, x_6, x_2613);
if (lean_obj_tag(x_2615) == 0)
{
lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; 
x_2616 = lean_ctor_get(x_2615, 0);
lean_inc(x_2616);
x_2617 = lean_ctor_get(x_2615, 1);
lean_inc(x_2617);
if (lean_is_exclusive(x_2615)) {
 lean_ctor_release(x_2615, 0);
 lean_ctor_release(x_2615, 1);
 x_2618 = x_2615;
} else {
 lean_dec_ref(x_2615);
 x_2618 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_2619 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_2617);
if (lean_obj_tag(x_2619) == 0)
{
lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; lean_object* x_2633; uint8_t x_2634; lean_object* x_2635; lean_object* x_2636; 
x_2620 = lean_ctor_get(x_2619, 0);
lean_inc(x_2620);
x_2621 = lean_ctor_get(x_2619, 1);
lean_inc(x_2621);
if (lean_is_exclusive(x_2619)) {
 lean_ctor_release(x_2619, 0);
 lean_ctor_release(x_2619, 1);
 x_2622 = x_2619;
} else {
 lean_dec_ref(x_2619);
 x_2622 = lean_box(0);
}
if (lean_is_scalar(x_2622)) {
 x_2623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2623 = x_2622;
 lean_ctor_set_tag(x_2623, 1);
}
lean_ctor_set(x_2623, 0, x_2620);
lean_ctor_set(x_2623, 1, x_2564);
if (lean_is_scalar(x_2618)) {
 x_2624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2624 = x_2618;
 lean_ctor_set_tag(x_2624, 1);
}
lean_ctor_set(x_2624, 0, x_2616);
lean_ctor_set(x_2624, 1, x_2623);
x_2625 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_2626 = l_Lean_Expr_const___override(x_2625, x_2624);
lean_inc(x_41);
if (lean_is_scalar(x_2603)) {
 x_2627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2627 = x_2603;
 lean_ctor_set_tag(x_2627, 1);
}
lean_ctor_set(x_2627, 0, x_41);
lean_ctor_set(x_2627, 1, x_2564);
x_2628 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_2629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2629, 0, x_2628);
lean_ctor_set(x_2629, 1, x_2627);
lean_inc(x_2503);
x_2630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2630, 0, x_2503);
lean_ctor_set(x_2630, 1, x_2629);
x_2631 = lean_array_mk(x_2630);
x_2632 = l_Lean_mkAppN(x_2626, x_2631);
lean_dec(x_2631);
x_2633 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_2634 = 0;
lean_inc(x_2503);
x_2635 = l_Lean_Expr_forallE___override(x_2633, x_2503, x_2632, x_2634);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2636 = l_Lean_Meta_trySynthInstance(x_2635, x_2574, x_3, x_4, x_5, x_6, x_2621);
if (lean_obj_tag(x_2636) == 0)
{
lean_object* x_2637; 
x_2637 = lean_ctor_get(x_2636, 0);
lean_inc(x_2637);
if (lean_obj_tag(x_2637) == 1)
{
lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; 
x_2638 = lean_ctor_get(x_2636, 1);
lean_inc(x_2638);
lean_dec(x_2636);
x_2639 = lean_ctor_get(x_2637, 0);
lean_inc(x_2639);
lean_dec(x_2637);
x_2640 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_2641 = l_Lean_Expr_const___override(x_2640, x_2593);
x_2642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2642, 0, x_2614);
lean_ctor_set(x_2642, 1, x_2596);
x_2643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2643, 0, x_2639);
lean_ctor_set(x_2643, 1, x_2642);
x_2644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2644, 0, x_2578);
lean_ctor_set(x_2644, 1, x_2643);
x_2645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2645, 0, x_41);
lean_ctor_set(x_2645, 1, x_2644);
x_2646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2646, 0, x_2503);
lean_ctor_set(x_2646, 1, x_2645);
x_2647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2647, 0, x_40);
lean_ctor_set(x_2647, 1, x_2646);
x_2648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2648, 0, x_2502);
lean_ctor_set(x_2648, 1, x_2647);
x_2649 = lean_array_mk(x_2648);
x_2650 = l_Lean_mkAppN(x_2641, x_2649);
lean_dec(x_2649);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2651 = l_Lean_Meta_expandCoe(x_2650, x_3, x_4, x_5, x_6, x_2638);
if (lean_obj_tag(x_2651) == 0)
{
lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; 
x_2652 = lean_ctor_get(x_2651, 0);
lean_inc(x_2652);
x_2653 = lean_ctor_get(x_2651, 1);
lean_inc(x_2653);
lean_dec(x_2651);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2652);
x_2654 = lean_infer_type(x_2652, x_3, x_4, x_5, x_6, x_2653);
if (lean_obj_tag(x_2654) == 0)
{
lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; 
x_2655 = lean_ctor_get(x_2654, 0);
lean_inc(x_2655);
x_2656 = lean_ctor_get(x_2654, 1);
lean_inc(x_2656);
lean_dec(x_2654);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2657 = l_Lean_Meta_isExprDefEq(x_19, x_2655, x_3, x_4, x_5, x_6, x_2656);
if (lean_obj_tag(x_2657) == 0)
{
lean_object* x_2658; uint8_t x_2659; 
x_2658 = lean_ctor_get(x_2657, 0);
lean_inc(x_2658);
x_2659 = lean_unbox(x_2658);
lean_dec(x_2658);
if (x_2659 == 0)
{
lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; 
lean_dec(x_2652);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2660 = lean_ctor_get(x_2657, 1);
lean_inc(x_2660);
if (lean_is_exclusive(x_2657)) {
 lean_ctor_release(x_2657, 0);
 lean_ctor_release(x_2657, 1);
 x_2661 = x_2657;
} else {
 lean_dec_ref(x_2657);
 x_2661 = lean_box(0);
}
if (lean_is_scalar(x_2661)) {
 x_2662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2662 = x_2661;
}
lean_ctor_set(x_2662, 0, x_2574);
lean_ctor_set(x_2662, 1, x_2660);
return x_2662;
}
else
{
lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; 
x_2663 = lean_ctor_get(x_2657, 1);
lean_inc(x_2663);
lean_dec(x_2657);
x_2664 = lean_box(0);
x_2665 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2652, x_2664, x_3, x_4, x_5, x_6, x_2663);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2666 = lean_ctor_get(x_2665, 0);
lean_inc(x_2666);
x_2667 = lean_ctor_get(x_2665, 1);
lean_inc(x_2667);
if (lean_is_exclusive(x_2665)) {
 lean_ctor_release(x_2665, 0);
 lean_ctor_release(x_2665, 1);
 x_2668 = x_2665;
} else {
 lean_dec_ref(x_2665);
 x_2668 = lean_box(0);
}
if (lean_is_scalar(x_2668)) {
 x_2669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2669 = x_2668;
}
lean_ctor_set(x_2669, 0, x_2666);
lean_ctor_set(x_2669, 1, x_2667);
return x_2669;
}
}
else
{
lean_object* x_2670; lean_object* x_2671; 
lean_dec(x_2652);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2670 = lean_ctor_get(x_2657, 0);
lean_inc(x_2670);
x_2671 = lean_ctor_get(x_2657, 1);
lean_inc(x_2671);
lean_dec(x_2657);
x_8 = x_2670;
x_9 = x_2671;
goto block_16;
}
}
else
{
lean_object* x_2672; lean_object* x_2673; 
lean_dec(x_2652);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2672 = lean_ctor_get(x_2654, 0);
lean_inc(x_2672);
x_2673 = lean_ctor_get(x_2654, 1);
lean_inc(x_2673);
lean_dec(x_2654);
x_8 = x_2672;
x_9 = x_2673;
goto block_16;
}
}
else
{
lean_object* x_2674; lean_object* x_2675; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2674 = lean_ctor_get(x_2651, 0);
lean_inc(x_2674);
x_2675 = lean_ctor_get(x_2651, 1);
lean_inc(x_2675);
lean_dec(x_2651);
x_8 = x_2674;
x_9 = x_2675;
goto block_16;
}
}
else
{
lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; 
lean_dec(x_2637);
lean_dec(x_2614);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2676 = lean_ctor_get(x_2636, 1);
lean_inc(x_2676);
if (lean_is_exclusive(x_2636)) {
 lean_ctor_release(x_2636, 0);
 lean_ctor_release(x_2636, 1);
 x_2677 = x_2636;
} else {
 lean_dec_ref(x_2636);
 x_2677 = lean_box(0);
}
if (lean_is_scalar(x_2677)) {
 x_2678 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2678 = x_2677;
}
lean_ctor_set(x_2678, 0, x_2574);
lean_ctor_set(x_2678, 1, x_2676);
return x_2678;
}
}
else
{
lean_object* x_2679; lean_object* x_2680; 
lean_dec(x_2614);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2679 = lean_ctor_get(x_2636, 0);
lean_inc(x_2679);
x_2680 = lean_ctor_get(x_2636, 1);
lean_inc(x_2680);
lean_dec(x_2636);
x_8 = x_2679;
x_9 = x_2680;
goto block_16;
}
}
else
{
lean_object* x_2681; lean_object* x_2682; 
lean_dec(x_2618);
lean_dec(x_2616);
lean_dec(x_2614);
lean_dec(x_2603);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2681 = lean_ctor_get(x_2619, 0);
lean_inc(x_2681);
x_2682 = lean_ctor_get(x_2619, 1);
lean_inc(x_2682);
lean_dec(x_2619);
x_8 = x_2681;
x_9 = x_2682;
goto block_16;
}
}
else
{
lean_object* x_2683; lean_object* x_2684; 
lean_dec(x_2614);
lean_dec(x_2603);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2683 = lean_ctor_get(x_2615, 0);
lean_inc(x_2683);
x_2684 = lean_ctor_get(x_2615, 1);
lean_inc(x_2684);
lean_dec(x_2615);
x_8 = x_2683;
x_9 = x_2684;
goto block_16;
}
}
}
else
{
lean_object* x_2685; lean_object* x_2686; 
lean_dec(x_2603);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2685 = lean_ctor_get(x_2608, 0);
lean_inc(x_2685);
x_2686 = lean_ctor_get(x_2608, 1);
lean_inc(x_2686);
lean_dec(x_2608);
x_8 = x_2685;
x_9 = x_2686;
goto block_16;
}
}
else
{
lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; 
lean_dec(x_2603);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2687 = lean_ctor_get(x_2604, 1);
lean_inc(x_2687);
if (lean_is_exclusive(x_2604)) {
 lean_ctor_release(x_2604, 0);
 lean_ctor_release(x_2604, 1);
 x_2688 = x_2604;
} else {
 lean_dec_ref(x_2604);
 x_2688 = lean_box(0);
}
x_2689 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2689, 0, x_2599);
if (lean_is_scalar(x_2688)) {
 x_2690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2690 = x_2688;
}
lean_ctor_set(x_2690, 0, x_2689);
lean_ctor_set(x_2690, 1, x_2687);
return x_2690;
}
}
else
{
lean_object* x_2691; lean_object* x_2692; 
lean_dec(x_2603);
lean_dec(x_2599);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2691 = lean_ctor_get(x_2604, 0);
lean_inc(x_2691);
x_2692 = lean_ctor_get(x_2604, 1);
lean_inc(x_2692);
lean_dec(x_2604);
x_8 = x_2691;
x_9 = x_2692;
goto block_16;
}
}
else
{
lean_object* x_2693; lean_object* x_2694; 
lean_dec(x_2599);
lean_dec(x_2596);
lean_dec(x_2593);
lean_dec(x_2578);
lean_dec(x_2503);
lean_dec(x_2502);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2693 = lean_ctor_get(x_2600, 0);
lean_inc(x_2693);
x_2694 = lean_ctor_get(x_2600, 1);
lean_inc(x_2694);
lean_dec(x_2600);
x_8 = x_2693;
x_9 = x_2694;
goto block_16;
}
}
else
{
lean_object* x_2695; lean_object* x_2696; 
lean_dec(x_2586);
lean_dec(x_2584);
lean_dec(x_2582);
lean_dec(x_2580);
lean_dec(x_2578);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2695 = lean_ctor_get(x_2587, 0);
lean_inc(x_2695);
x_2696 = lean_ctor_get(x_2587, 1);
lean_inc(x_2696);
lean_dec(x_2587);
x_8 = x_2695;
x_9 = x_2696;
goto block_16;
}
}
else
{
lean_object* x_2697; lean_object* x_2698; 
lean_dec(x_2582);
lean_dec(x_2580);
lean_dec(x_2578);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2697 = lean_ctor_get(x_2583, 0);
lean_inc(x_2697);
x_2698 = lean_ctor_get(x_2583, 1);
lean_inc(x_2698);
lean_dec(x_2583);
x_8 = x_2697;
x_9 = x_2698;
goto block_16;
}
}
else
{
lean_object* x_2699; lean_object* x_2700; 
lean_dec(x_2578);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2699 = lean_ctor_get(x_2579, 0);
lean_inc(x_2699);
x_2700 = lean_ctor_get(x_2579, 1);
lean_inc(x_2700);
lean_dec(x_2579);
x_8 = x_2699;
x_9 = x_2700;
goto block_16;
}
}
else
{
lean_object* x_2701; lean_object* x_2702; lean_object* x_2703; 
lean_dec(x_2576);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2701 = lean_ctor_get(x_2575, 1);
lean_inc(x_2701);
if (lean_is_exclusive(x_2575)) {
 lean_ctor_release(x_2575, 0);
 lean_ctor_release(x_2575, 1);
 x_2702 = x_2575;
} else {
 lean_dec_ref(x_2575);
 x_2702 = lean_box(0);
}
if (lean_is_scalar(x_2702)) {
 x_2703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2703 = x_2702;
}
lean_ctor_set(x_2703, 0, x_2574);
lean_ctor_set(x_2703, 1, x_2701);
return x_2703;
}
}
else
{
lean_object* x_2704; lean_object* x_2705; 
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2704 = lean_ctor_get(x_2575, 0);
lean_inc(x_2704);
x_2705 = lean_ctor_get(x_2575, 1);
lean_inc(x_2705);
lean_dec(x_2575);
x_8 = x_2704;
x_9 = x_2705;
goto block_16;
}
}
else
{
lean_object* x_2706; lean_object* x_2707; 
lean_dec(x_2559);
lean_dec(x_2557);
lean_dec(x_2546);
lean_dec(x_2542);
lean_dec(x_2540);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2706 = lean_ctor_get(x_2560, 0);
lean_inc(x_2706);
x_2707 = lean_ctor_get(x_2560, 1);
lean_inc(x_2707);
lean_dec(x_2560);
x_8 = x_2706;
x_9 = x_2707;
goto block_16;
}
}
else
{
lean_object* x_2708; lean_object* x_2709; 
lean_dec(x_2546);
lean_dec(x_2542);
lean_dec(x_2540);
lean_dec(x_2538);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2708 = lean_ctor_get(x_2556, 0);
lean_inc(x_2708);
x_2709 = lean_ctor_get(x_2556, 1);
lean_inc(x_2709);
lean_dec(x_2556);
x_8 = x_2708;
x_9 = x_2709;
goto block_16;
}
}
}
else
{
lean_object* x_2710; lean_object* x_2711; 
lean_dec(x_2546);
lean_dec(x_2542);
lean_dec(x_2540);
lean_dec(x_2538);
lean_dec(x_2528);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2710 = lean_ctor_get(x_2548, 0);
lean_inc(x_2710);
x_2711 = lean_ctor_get(x_2548, 1);
lean_inc(x_2711);
lean_dec(x_2548);
x_8 = x_2710;
x_9 = x_2711;
goto block_16;
}
}
else
{
lean_object* x_2712; lean_object* x_2713; 
lean_dec(x_2542);
lean_dec(x_2540);
lean_dec(x_2538);
lean_dec(x_2528);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2712 = lean_ctor_get(x_2543, 0);
lean_inc(x_2712);
x_2713 = lean_ctor_get(x_2543, 1);
lean_inc(x_2713);
lean_dec(x_2543);
x_8 = x_2712;
x_9 = x_2713;
goto block_16;
}
}
else
{
lean_object* x_2714; lean_object* x_2715; 
lean_dec(x_2538);
lean_dec(x_2537);
lean_dec(x_2528);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2714 = lean_ctor_get(x_2539, 0);
lean_inc(x_2714);
x_2715 = lean_ctor_get(x_2539, 1);
lean_inc(x_2715);
lean_dec(x_2539);
x_8 = x_2714;
x_9 = x_2715;
goto block_16;
}
}
else
{
lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; 
lean_dec(x_2535);
lean_dec(x_2534);
lean_dec(x_2528);
lean_dec(x_2527);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2716 = lean_ctor_get(x_2532, 1);
lean_inc(x_2716);
if (lean_is_exclusive(x_2532)) {
 lean_ctor_release(x_2532, 0);
 lean_ctor_release(x_2532, 1);
 x_2717 = x_2532;
} else {
 lean_dec_ref(x_2532);
 x_2717 = lean_box(0);
}
x_2718 = lean_box(0);
if (lean_is_scalar(x_2717)) {
 x_2719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2719 = x_2717;
}
lean_ctor_set(x_2719, 0, x_2718);
lean_ctor_set(x_2719, 1, x_2716);
return x_2719;
}
}
else
{
lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; 
lean_dec(x_2534);
lean_dec(x_2533);
lean_dec(x_2528);
lean_dec(x_2527);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2720 = lean_ctor_get(x_2532, 1);
lean_inc(x_2720);
if (lean_is_exclusive(x_2532)) {
 lean_ctor_release(x_2532, 0);
 lean_ctor_release(x_2532, 1);
 x_2721 = x_2532;
} else {
 lean_dec_ref(x_2532);
 x_2721 = lean_box(0);
}
x_2722 = lean_box(0);
if (lean_is_scalar(x_2721)) {
 x_2723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2723 = x_2721;
}
lean_ctor_set(x_2723, 0, x_2722);
lean_ctor_set(x_2723, 1, x_2720);
return x_2723;
}
}
else
{
lean_object* x_2724; lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; 
lean_dec(x_2533);
lean_dec(x_2528);
lean_dec(x_2527);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2724 = lean_ctor_get(x_2532, 1);
lean_inc(x_2724);
if (lean_is_exclusive(x_2532)) {
 lean_ctor_release(x_2532, 0);
 lean_ctor_release(x_2532, 1);
 x_2725 = x_2532;
} else {
 lean_dec_ref(x_2532);
 x_2725 = lean_box(0);
}
x_2726 = lean_box(0);
if (lean_is_scalar(x_2725)) {
 x_2727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2727 = x_2725;
}
lean_ctor_set(x_2727, 0, x_2726);
lean_ctor_set(x_2727, 1, x_2724);
return x_2727;
}
}
else
{
lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; uint8_t x_2731; 
lean_dec(x_2528);
lean_dec(x_2527);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2728 = lean_ctor_get(x_2532, 0);
lean_inc(x_2728);
x_2729 = lean_ctor_get(x_2532, 1);
lean_inc(x_2729);
if (lean_is_exclusive(x_2532)) {
 lean_ctor_release(x_2532, 0);
 lean_ctor_release(x_2532, 1);
 x_2730 = x_2532;
} else {
 lean_dec_ref(x_2532);
 x_2730 = lean_box(0);
}
x_2731 = l_Lean_Exception_isInterrupt(x_2728);
if (x_2731 == 0)
{
uint8_t x_2732; 
x_2732 = l_Lean_Exception_isRuntime(x_2728);
if (x_2732 == 0)
{
lean_object* x_2733; lean_object* x_2734; 
lean_dec(x_2728);
x_2733 = lean_box(0);
if (lean_is_scalar(x_2730)) {
 x_2734 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2734 = x_2730;
 lean_ctor_set_tag(x_2734, 0);
}
lean_ctor_set(x_2734, 0, x_2733);
lean_ctor_set(x_2734, 1, x_2729);
return x_2734;
}
else
{
lean_object* x_2735; 
if (lean_is_scalar(x_2730)) {
 x_2735 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2735 = x_2730;
}
lean_ctor_set(x_2735, 0, x_2728);
lean_ctor_set(x_2735, 1, x_2729);
return x_2735;
}
}
else
{
lean_object* x_2736; 
if (lean_is_scalar(x_2730)) {
 x_2736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2736 = x_2730;
}
lean_ctor_set(x_2736, 0, x_2728);
lean_ctor_set(x_2736, 1, x_2729);
return x_2736;
}
}
}
else
{
lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; uint8_t x_2740; 
lean_dec(x_2528);
lean_dec(x_2527);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2737 = lean_ctor_get(x_2529, 0);
lean_inc(x_2737);
x_2738 = lean_ctor_get(x_2529, 1);
lean_inc(x_2738);
if (lean_is_exclusive(x_2529)) {
 lean_ctor_release(x_2529, 0);
 lean_ctor_release(x_2529, 1);
 x_2739 = x_2529;
} else {
 lean_dec_ref(x_2529);
 x_2739 = lean_box(0);
}
x_2740 = l_Lean_Exception_isInterrupt(x_2737);
if (x_2740 == 0)
{
uint8_t x_2741; 
x_2741 = l_Lean_Exception_isRuntime(x_2737);
if (x_2741 == 0)
{
lean_object* x_2742; lean_object* x_2743; 
lean_dec(x_2737);
x_2742 = lean_box(0);
if (lean_is_scalar(x_2739)) {
 x_2743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2743 = x_2739;
 lean_ctor_set_tag(x_2743, 0);
}
lean_ctor_set(x_2743, 0, x_2742);
lean_ctor_set(x_2743, 1, x_2738);
return x_2743;
}
else
{
lean_object* x_2744; 
if (lean_is_scalar(x_2739)) {
 x_2744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2744 = x_2739;
}
lean_ctor_set(x_2744, 0, x_2737);
lean_ctor_set(x_2744, 1, x_2738);
return x_2744;
}
}
else
{
lean_object* x_2745; 
if (lean_is_scalar(x_2739)) {
 x_2745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2745 = x_2739;
}
lean_ctor_set(x_2745, 0, x_2737);
lean_ctor_set(x_2745, 1, x_2738);
return x_2745;
}
}
}
else
{
lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; 
lean_dec(x_2525);
lean_dec(x_2524);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2746 = lean_ctor_get(x_2522, 1);
lean_inc(x_2746);
if (lean_is_exclusive(x_2522)) {
 lean_ctor_release(x_2522, 0);
 lean_ctor_release(x_2522, 1);
 x_2747 = x_2522;
} else {
 lean_dec_ref(x_2522);
 x_2747 = lean_box(0);
}
x_2748 = lean_box(0);
if (lean_is_scalar(x_2747)) {
 x_2749 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2749 = x_2747;
}
lean_ctor_set(x_2749, 0, x_2748);
lean_ctor_set(x_2749, 1, x_2746);
return x_2749;
}
}
else
{
lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; 
lean_dec(x_2524);
lean_dec(x_2523);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2750 = lean_ctor_get(x_2522, 1);
lean_inc(x_2750);
if (lean_is_exclusive(x_2522)) {
 lean_ctor_release(x_2522, 0);
 lean_ctor_release(x_2522, 1);
 x_2751 = x_2522;
} else {
 lean_dec_ref(x_2522);
 x_2751 = lean_box(0);
}
x_2752 = lean_box(0);
if (lean_is_scalar(x_2751)) {
 x_2753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2753 = x_2751;
}
lean_ctor_set(x_2753, 0, x_2752);
lean_ctor_set(x_2753, 1, x_2750);
return x_2753;
}
}
else
{
lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; lean_object* x_2757; 
lean_dec(x_2523);
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2754 = lean_ctor_get(x_2522, 1);
lean_inc(x_2754);
if (lean_is_exclusive(x_2522)) {
 lean_ctor_release(x_2522, 0);
 lean_ctor_release(x_2522, 1);
 x_2755 = x_2522;
} else {
 lean_dec_ref(x_2522);
 x_2755 = lean_box(0);
}
x_2756 = lean_box(0);
if (lean_is_scalar(x_2755)) {
 x_2757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2757 = x_2755;
}
lean_ctor_set(x_2757, 0, x_2756);
lean_ctor_set(x_2757, 1, x_2754);
return x_2757;
}
}
else
{
lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; uint8_t x_2761; 
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2758 = lean_ctor_get(x_2522, 0);
lean_inc(x_2758);
x_2759 = lean_ctor_get(x_2522, 1);
lean_inc(x_2759);
if (lean_is_exclusive(x_2522)) {
 lean_ctor_release(x_2522, 0);
 lean_ctor_release(x_2522, 1);
 x_2760 = x_2522;
} else {
 lean_dec_ref(x_2522);
 x_2760 = lean_box(0);
}
x_2761 = l_Lean_Exception_isInterrupt(x_2758);
if (x_2761 == 0)
{
uint8_t x_2762; 
x_2762 = l_Lean_Exception_isRuntime(x_2758);
if (x_2762 == 0)
{
lean_object* x_2763; lean_object* x_2764; 
lean_dec(x_2758);
x_2763 = lean_box(0);
if (lean_is_scalar(x_2760)) {
 x_2764 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2764 = x_2760;
 lean_ctor_set_tag(x_2764, 0);
}
lean_ctor_set(x_2764, 0, x_2763);
lean_ctor_set(x_2764, 1, x_2759);
return x_2764;
}
else
{
lean_object* x_2765; 
if (lean_is_scalar(x_2760)) {
 x_2765 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2765 = x_2760;
}
lean_ctor_set(x_2765, 0, x_2758);
lean_ctor_set(x_2765, 1, x_2759);
return x_2765;
}
}
else
{
lean_object* x_2766; 
if (lean_is_scalar(x_2760)) {
 x_2766 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2766 = x_2760;
}
lean_ctor_set(x_2766, 0, x_2758);
lean_ctor_set(x_2766, 1, x_2759);
return x_2766;
}
}
}
else
{
lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; uint8_t x_2770; 
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2767 = lean_ctor_get(x_2519, 0);
lean_inc(x_2767);
x_2768 = lean_ctor_get(x_2519, 1);
lean_inc(x_2768);
if (lean_is_exclusive(x_2519)) {
 lean_ctor_release(x_2519, 0);
 lean_ctor_release(x_2519, 1);
 x_2769 = x_2519;
} else {
 lean_dec_ref(x_2519);
 x_2769 = lean_box(0);
}
x_2770 = l_Lean_Exception_isInterrupt(x_2767);
if (x_2770 == 0)
{
uint8_t x_2771; 
x_2771 = l_Lean_Exception_isRuntime(x_2767);
if (x_2771 == 0)
{
lean_object* x_2772; lean_object* x_2773; 
lean_dec(x_2767);
x_2772 = lean_box(0);
if (lean_is_scalar(x_2769)) {
 x_2773 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2773 = x_2769;
 lean_ctor_set_tag(x_2773, 0);
}
lean_ctor_set(x_2773, 0, x_2772);
lean_ctor_set(x_2773, 1, x_2768);
return x_2773;
}
else
{
lean_object* x_2774; 
if (lean_is_scalar(x_2769)) {
 x_2774 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2774 = x_2769;
}
lean_ctor_set(x_2774, 0, x_2767);
lean_ctor_set(x_2774, 1, x_2768);
return x_2774;
}
}
else
{
lean_object* x_2775; 
if (lean_is_scalar(x_2769)) {
 x_2775 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2775 = x_2769;
}
lean_ctor_set(x_2775, 0, x_2767);
lean_ctor_set(x_2775, 1, x_2768);
return x_2775;
}
}
}
}
else
{
lean_object* x_2776; lean_object* x_2777; 
lean_dec(x_26);
lean_dec(x_19);
x_2776 = lean_ctor_get(x_2509, 1);
lean_inc(x_2776);
lean_dec(x_2509);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2777 = l_Lean_Meta_isMonad_x3f(x_40, x_3, x_4, x_5, x_6, x_2776);
if (lean_obj_tag(x_2777) == 0)
{
lean_object* x_2778; 
x_2778 = lean_ctor_get(x_2777, 0);
lean_inc(x_2778);
if (lean_obj_tag(x_2778) == 0)
{
lean_object* x_2779; lean_object* x_2780; lean_object* x_2781; lean_object* x_2782; lean_object* x_2783; lean_object* x_2784; 
lean_dec(x_2508);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_1);
x_2779 = lean_ctor_get(x_2777, 1);
lean_inc(x_2779);
lean_dec(x_2777);
x_2780 = l_Lean_Meta_SavedState_restore(x_2506, x_3, x_4, x_5, x_6, x_2779);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2506);
x_2781 = lean_ctor_get(x_2780, 1);
lean_inc(x_2781);
if (lean_is_exclusive(x_2780)) {
 lean_ctor_release(x_2780, 0);
 lean_ctor_release(x_2780, 1);
 x_2782 = x_2780;
} else {
 lean_dec_ref(x_2780);
 x_2782 = lean_box(0);
}
x_2783 = lean_box(0);
if (lean_is_scalar(x_2782)) {
 x_2784 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2784 = x_2782;
}
lean_ctor_set(x_2784, 0, x_2783);
lean_ctor_set(x_2784, 1, x_2781);
return x_2784;
}
else
{
lean_object* x_2785; lean_object* x_2786; lean_object* x_2787; lean_object* x_2788; lean_object* x_2789; lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; lean_object* x_2799; lean_object* x_2800; lean_object* x_2810; lean_object* x_2811; 
x_2785 = lean_ctor_get(x_2777, 1);
lean_inc(x_2785);
if (lean_is_exclusive(x_2777)) {
 lean_ctor_release(x_2777, 0);
 lean_ctor_release(x_2777, 1);
 x_2786 = x_2777;
} else {
 lean_dec_ref(x_2777);
 x_2786 = lean_box(0);
}
x_2787 = lean_ctor_get(x_2778, 0);
lean_inc(x_2787);
if (lean_is_exclusive(x_2778)) {
 lean_ctor_release(x_2778, 0);
 x_2788 = x_2778;
} else {
 lean_dec_ref(x_2778);
 x_2788 = lean_box(0);
}
if (lean_is_scalar(x_2788)) {
 x_2789 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2789 = x_2788;
}
lean_ctor_set(x_2789, 0, x_2502);
x_2790 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2790, 0, x_2503);
lean_ctor_set(x_29, 0, x_41);
x_2791 = lean_box(0);
x_2792 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2792, 0, x_2787);
x_2793 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2793, 0, x_1);
x_2794 = lean_box(0);
if (lean_is_scalar(x_2508)) {
 x_2795 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2795 = x_2508;
 lean_ctor_set_tag(x_2795, 1);
}
lean_ctor_set(x_2795, 0, x_2793);
lean_ctor_set(x_2795, 1, x_2794);
if (lean_is_scalar(x_2504)) {
 x_2796 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2796 = x_2504;
 lean_ctor_set_tag(x_2796, 1);
}
lean_ctor_set(x_2796, 0, x_2792);
lean_ctor_set(x_2796, 1, x_2795);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_2796);
lean_ctor_set(x_37, 0, x_2791);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_29);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_2790);
x_2797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2797, 0, x_2789);
lean_ctor_set(x_2797, 1, x_17);
x_2798 = lean_array_mk(x_2797);
x_2810 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2811 = l_Lean_Meta_mkAppOptM(x_2810, x_2798, x_3, x_4, x_5, x_6, x_2785);
if (lean_obj_tag(x_2811) == 0)
{
lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; 
x_2812 = lean_ctor_get(x_2811, 0);
lean_inc(x_2812);
x_2813 = lean_ctor_get(x_2811, 1);
lean_inc(x_2813);
lean_dec(x_2811);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2814 = l_Lean_Meta_expandCoe(x_2812, x_3, x_4, x_5, x_6, x_2813);
if (lean_obj_tag(x_2814) == 0)
{
lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; 
lean_dec(x_2786);
lean_dec(x_2506);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2815 = lean_ctor_get(x_2814, 0);
lean_inc(x_2815);
x_2816 = lean_ctor_get(x_2814, 1);
lean_inc(x_2816);
if (lean_is_exclusive(x_2814)) {
 lean_ctor_release(x_2814, 0);
 lean_ctor_release(x_2814, 1);
 x_2817 = x_2814;
} else {
 lean_dec_ref(x_2814);
 x_2817 = lean_box(0);
}
x_2818 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2818, 0, x_2815);
if (lean_is_scalar(x_2817)) {
 x_2819 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2819 = x_2817;
}
lean_ctor_set(x_2819, 0, x_2818);
lean_ctor_set(x_2819, 1, x_2816);
return x_2819;
}
else
{
lean_object* x_2820; lean_object* x_2821; 
x_2820 = lean_ctor_get(x_2814, 0);
lean_inc(x_2820);
x_2821 = lean_ctor_get(x_2814, 1);
lean_inc(x_2821);
lean_dec(x_2814);
x_2799 = x_2820;
x_2800 = x_2821;
goto block_2809;
}
}
else
{
lean_object* x_2822; lean_object* x_2823; 
x_2822 = lean_ctor_get(x_2811, 0);
lean_inc(x_2822);
x_2823 = lean_ctor_get(x_2811, 1);
lean_inc(x_2823);
lean_dec(x_2811);
x_2799 = x_2822;
x_2800 = x_2823;
goto block_2809;
}
block_2809:
{
uint8_t x_2801; 
x_2801 = l_Lean_Exception_isInterrupt(x_2799);
if (x_2801 == 0)
{
uint8_t x_2802; 
x_2802 = l_Lean_Exception_isRuntime(x_2799);
if (x_2802 == 0)
{
lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; 
lean_dec(x_2799);
lean_dec(x_2786);
x_2803 = l_Lean_Meta_SavedState_restore(x_2506, x_3, x_4, x_5, x_6, x_2800);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2506);
x_2804 = lean_ctor_get(x_2803, 1);
lean_inc(x_2804);
if (lean_is_exclusive(x_2803)) {
 lean_ctor_release(x_2803, 0);
 lean_ctor_release(x_2803, 1);
 x_2805 = x_2803;
} else {
 lean_dec_ref(x_2803);
 x_2805 = lean_box(0);
}
if (lean_is_scalar(x_2805)) {
 x_2806 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2806 = x_2805;
}
lean_ctor_set(x_2806, 0, x_2791);
lean_ctor_set(x_2806, 1, x_2804);
return x_2806;
}
else
{
lean_object* x_2807; 
lean_dec(x_2506);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_2786)) {
 x_2807 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2807 = x_2786;
 lean_ctor_set_tag(x_2807, 1);
}
lean_ctor_set(x_2807, 0, x_2799);
lean_ctor_set(x_2807, 1, x_2800);
return x_2807;
}
}
else
{
lean_object* x_2808; 
lean_dec(x_2506);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_2786)) {
 x_2808 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2808 = x_2786;
 lean_ctor_set_tag(x_2808, 1);
}
lean_ctor_set(x_2808, 0, x_2799);
lean_ctor_set(x_2808, 1, x_2800);
return x_2808;
}
}
}
}
else
{
lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; 
lean_dec(x_2508);
lean_dec(x_2506);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2824 = lean_ctor_get(x_2777, 0);
lean_inc(x_2824);
x_2825 = lean_ctor_get(x_2777, 1);
lean_inc(x_2825);
if (lean_is_exclusive(x_2777)) {
 lean_ctor_release(x_2777, 0);
 lean_ctor_release(x_2777, 1);
 x_2826 = x_2777;
} else {
 lean_dec_ref(x_2777);
 x_2826 = lean_box(0);
}
if (lean_is_scalar(x_2826)) {
 x_2827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2827 = x_2826;
}
lean_ctor_set(x_2827, 0, x_2824);
lean_ctor_set(x_2827, 1, x_2825);
return x_2827;
}
}
}
else
{
lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; 
lean_dec(x_2508);
lean_dec(x_2506);
lean_dec(x_2504);
lean_dec(x_2503);
lean_dec(x_2502);
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2828 = lean_ctor_get(x_2509, 0);
lean_inc(x_2828);
x_2829 = lean_ctor_get(x_2509, 1);
lean_inc(x_2829);
if (lean_is_exclusive(x_2509)) {
 lean_ctor_release(x_2509, 0);
 lean_ctor_release(x_2509, 1);
 x_2830 = x_2509;
} else {
 lean_dec_ref(x_2509);
 x_2830 = lean_box(0);
}
if (lean_is_scalar(x_2830)) {
 x_2831 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2831 = x_2830;
}
lean_ctor_set(x_2831, 0, x_2828);
lean_ctor_set(x_2831, 1, x_2829);
return x_2831;
}
}
}
}
else
{
uint8_t x_2832; 
lean_free_object(x_37);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2832 = !lean_is_exclusive(x_42);
if (x_2832 == 0)
{
return x_42;
}
else
{
lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; 
x_2833 = lean_ctor_get(x_42, 0);
x_2834 = lean_ctor_get(x_42, 1);
lean_inc(x_2834);
lean_inc(x_2833);
lean_dec(x_42);
x_2835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2835, 0, x_2833);
lean_ctor_set(x_2835, 1, x_2834);
return x_2835;
}
}
}
else
{
lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; 
x_2836 = lean_ctor_get(x_37, 0);
x_2837 = lean_ctor_get(x_37, 1);
lean_inc(x_2837);
lean_inc(x_2836);
lean_dec(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_2838 = l_Lean_Meta_isTypeApp_x3f(x_26, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_2838) == 0)
{
lean_object* x_2839; 
x_2839 = lean_ctor_get(x_2838, 0);
lean_inc(x_2839);
if (lean_obj_tag(x_2839) == 0)
{
lean_object* x_2840; lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; 
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2840 = lean_ctor_get(x_2838, 1);
lean_inc(x_2840);
if (lean_is_exclusive(x_2838)) {
 lean_ctor_release(x_2838, 0);
 lean_ctor_release(x_2838, 1);
 x_2841 = x_2838;
} else {
 lean_dec_ref(x_2838);
 x_2841 = lean_box(0);
}
x_2842 = lean_box(0);
if (lean_is_scalar(x_2841)) {
 x_2843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2843 = x_2841;
}
lean_ctor_set(x_2843, 0, x_2842);
lean_ctor_set(x_2843, 1, x_2840);
return x_2843;
}
else
{
lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; 
x_2844 = lean_ctor_get(x_2839, 0);
lean_inc(x_2844);
if (lean_is_exclusive(x_2839)) {
 lean_ctor_release(x_2839, 0);
 x_2845 = x_2839;
} else {
 lean_dec_ref(x_2839);
 x_2845 = lean_box(0);
}
x_2846 = lean_ctor_get(x_2838, 1);
lean_inc(x_2846);
lean_dec(x_2838);
x_2847 = lean_ctor_get(x_2844, 0);
lean_inc(x_2847);
x_2848 = lean_ctor_get(x_2844, 1);
lean_inc(x_2848);
if (lean_is_exclusive(x_2844)) {
 lean_ctor_release(x_2844, 0);
 lean_ctor_release(x_2844, 1);
 x_2849 = x_2844;
} else {
 lean_dec_ref(x_2844);
 x_2849 = lean_box(0);
}
x_2850 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_2846);
x_2851 = lean_ctor_get(x_2850, 0);
lean_inc(x_2851);
x_2852 = lean_ctor_get(x_2850, 1);
lean_inc(x_2852);
if (lean_is_exclusive(x_2850)) {
 lean_ctor_release(x_2850, 0);
 lean_ctor_release(x_2850, 1);
 x_2853 = x_2850;
} else {
 lean_dec_ref(x_2850);
 x_2853 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2836);
lean_inc(x_2847);
x_2854 = l_Lean_Meta_isExprDefEq(x_2847, x_2836, x_3, x_4, x_5, x_6, x_2852);
if (lean_obj_tag(x_2854) == 0)
{
lean_object* x_2855; uint8_t x_2856; 
x_2855 = lean_ctor_get(x_2854, 0);
lean_inc(x_2855);
x_2856 = lean_unbox(x_2855);
lean_dec(x_2855);
if (x_2856 == 0)
{
lean_object* x_2857; lean_object* x_2858; lean_object* x_2859; lean_object* x_2860; uint8_t x_2861; 
lean_dec(x_2851);
lean_free_object(x_29);
x_2857 = lean_ctor_get(x_2854, 1);
lean_inc(x_2857);
if (lean_is_exclusive(x_2854)) {
 lean_ctor_release(x_2854, 0);
 lean_ctor_release(x_2854, 1);
 x_2858 = x_2854;
} else {
 lean_dec_ref(x_2854);
 x_2858 = lean_box(0);
}
x_2859 = lean_ctor_get(x_5, 2);
lean_inc(x_2859);
x_2860 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_2861 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2859, x_2860);
lean_dec(x_2859);
if (x_2861 == 0)
{
lean_object* x_2862; lean_object* x_2863; 
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2862 = lean_box(0);
if (lean_is_scalar(x_2858)) {
 x_2863 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2863 = x_2858;
}
lean_ctor_set(x_2863, 0, x_2862);
lean_ctor_set(x_2863, 1, x_2857);
return x_2863;
}
else
{
lean_object* x_2864; 
lean_dec(x_2858);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2847);
x_2864 = lean_infer_type(x_2847, x_3, x_4, x_5, x_6, x_2857);
if (lean_obj_tag(x_2864) == 0)
{
lean_object* x_2865; lean_object* x_2866; lean_object* x_2867; 
x_2865 = lean_ctor_get(x_2864, 0);
lean_inc(x_2865);
x_2866 = lean_ctor_get(x_2864, 1);
lean_inc(x_2866);
lean_dec(x_2864);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2867 = lean_whnf(x_2865, x_3, x_4, x_5, x_6, x_2866);
if (lean_obj_tag(x_2867) == 0)
{
lean_object* x_2868; 
x_2868 = lean_ctor_get(x_2867, 0);
lean_inc(x_2868);
if (lean_obj_tag(x_2868) == 7)
{
lean_object* x_2869; 
x_2869 = lean_ctor_get(x_2868, 1);
lean_inc(x_2869);
if (lean_obj_tag(x_2869) == 3)
{
lean_object* x_2870; 
x_2870 = lean_ctor_get(x_2868, 2);
lean_inc(x_2870);
lean_dec(x_2868);
if (lean_obj_tag(x_2870) == 3)
{
lean_object* x_2871; lean_object* x_2872; lean_object* x_2873; lean_object* x_2874; 
x_2871 = lean_ctor_get(x_2867, 1);
lean_inc(x_2871);
lean_dec(x_2867);
x_2872 = lean_ctor_get(x_2869, 0);
lean_inc(x_2872);
lean_dec(x_2869);
x_2873 = lean_ctor_get(x_2870, 0);
lean_inc(x_2873);
lean_dec(x_2870);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2836);
x_2874 = lean_infer_type(x_2836, x_3, x_4, x_5, x_6, x_2871);
if (lean_obj_tag(x_2874) == 0)
{
lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; 
x_2875 = lean_ctor_get(x_2874, 0);
lean_inc(x_2875);
x_2876 = lean_ctor_get(x_2874, 1);
lean_inc(x_2876);
lean_dec(x_2874);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2877 = lean_whnf(x_2875, x_3, x_4, x_5, x_6, x_2876);
if (lean_obj_tag(x_2877) == 0)
{
lean_object* x_2878; 
x_2878 = lean_ctor_get(x_2877, 0);
lean_inc(x_2878);
if (lean_obj_tag(x_2878) == 7)
{
lean_object* x_2879; 
x_2879 = lean_ctor_get(x_2878, 1);
lean_inc(x_2879);
if (lean_obj_tag(x_2879) == 3)
{
lean_object* x_2880; 
x_2880 = lean_ctor_get(x_2878, 2);
lean_inc(x_2880);
lean_dec(x_2878);
if (lean_obj_tag(x_2880) == 3)
{
lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; 
x_2881 = lean_ctor_get(x_2877, 1);
lean_inc(x_2881);
lean_dec(x_2877);
x_2882 = lean_ctor_get(x_2879, 0);
lean_inc(x_2882);
lean_dec(x_2879);
x_2883 = lean_ctor_get(x_2880, 0);
lean_inc(x_2883);
lean_dec(x_2880);
x_2884 = l_Lean_Meta_decLevel(x_2872, x_3, x_4, x_5, x_6, x_2881);
if (lean_obj_tag(x_2884) == 0)
{
lean_object* x_2885; lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; 
x_2885 = lean_ctor_get(x_2884, 0);
lean_inc(x_2885);
x_2886 = lean_ctor_get(x_2884, 1);
lean_inc(x_2886);
if (lean_is_exclusive(x_2884)) {
 lean_ctor_release(x_2884, 0);
 lean_ctor_release(x_2884, 1);
 x_2887 = x_2884;
} else {
 lean_dec_ref(x_2884);
 x_2887 = lean_box(0);
}
x_2888 = l_Lean_Meta_decLevel(x_2882, x_3, x_4, x_5, x_6, x_2886);
if (lean_obj_tag(x_2888) == 0)
{
lean_object* x_2889; lean_object* x_2890; lean_object* x_2891; uint8_t x_2892; lean_object* x_2893; 
x_2889 = lean_ctor_get(x_2888, 0);
lean_inc(x_2889);
x_2890 = lean_ctor_get(x_2888, 1);
lean_inc(x_2890);
if (lean_is_exclusive(x_2888)) {
 lean_ctor_release(x_2888, 0);
 lean_ctor_release(x_2888, 1);
 x_2891 = x_2888;
} else {
 lean_dec_ref(x_2888);
 x_2891 = lean_box(0);
}
x_2892 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2885);
x_2893 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_2885, x_2889, x_2892, x_3, x_4, x_5, x_6, x_2890);
if (lean_obj_tag(x_2893) == 0)
{
lean_object* x_2894; uint8_t x_2895; 
x_2894 = lean_ctor_get(x_2893, 0);
lean_inc(x_2894);
x_2895 = lean_unbox(x_2894);
lean_dec(x_2894);
if (x_2895 == 0)
{
lean_object* x_2896; lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; 
lean_dec(x_2891);
lean_dec(x_2887);
lean_dec(x_2885);
lean_dec(x_2883);
lean_dec(x_2873);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2896 = lean_ctor_get(x_2893, 1);
lean_inc(x_2896);
if (lean_is_exclusive(x_2893)) {
 lean_ctor_release(x_2893, 0);
 lean_ctor_release(x_2893, 1);
 x_2897 = x_2893;
} else {
 lean_dec_ref(x_2893);
 x_2897 = lean_box(0);
}
x_2898 = lean_box(0);
if (lean_is_scalar(x_2897)) {
 x_2899 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2899 = x_2897;
}
lean_ctor_set(x_2899, 0, x_2898);
lean_ctor_set(x_2899, 1, x_2896);
return x_2899;
}
else
{
lean_object* x_2900; lean_object* x_2901; 
x_2900 = lean_ctor_get(x_2893, 1);
lean_inc(x_2900);
lean_dec(x_2893);
x_2901 = l_Lean_Meta_decLevel(x_2873, x_3, x_4, x_5, x_6, x_2900);
if (lean_obj_tag(x_2901) == 0)
{
lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; lean_object* x_2905; 
x_2902 = lean_ctor_get(x_2901, 0);
lean_inc(x_2902);
x_2903 = lean_ctor_get(x_2901, 1);
lean_inc(x_2903);
if (lean_is_exclusive(x_2901)) {
 lean_ctor_release(x_2901, 0);
 lean_ctor_release(x_2901, 1);
 x_2904 = x_2901;
} else {
 lean_dec_ref(x_2901);
 x_2904 = lean_box(0);
}
x_2905 = l_Lean_Meta_decLevel(x_2883, x_3, x_4, x_5, x_6, x_2903);
if (lean_obj_tag(x_2905) == 0)
{
lean_object* x_2906; lean_object* x_2907; lean_object* x_2908; lean_object* x_2909; lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; 
x_2906 = lean_ctor_get(x_2905, 0);
lean_inc(x_2906);
x_2907 = lean_ctor_get(x_2905, 1);
lean_inc(x_2907);
if (lean_is_exclusive(x_2905)) {
 lean_ctor_release(x_2905, 0);
 lean_ctor_release(x_2905, 1);
 x_2908 = x_2905;
} else {
 lean_dec_ref(x_2905);
 x_2908 = lean_box(0);
}
x_2909 = lean_box(0);
if (lean_is_scalar(x_2908)) {
 x_2910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2910 = x_2908;
 lean_ctor_set_tag(x_2910, 1);
}
lean_ctor_set(x_2910, 0, x_2906);
lean_ctor_set(x_2910, 1, x_2909);
if (lean_is_scalar(x_2904)) {
 x_2911 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2911 = x_2904;
 lean_ctor_set_tag(x_2911, 1);
}
lean_ctor_set(x_2911, 0, x_2902);
lean_ctor_set(x_2911, 1, x_2910);
if (lean_is_scalar(x_2891)) {
 x_2912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2912 = x_2891;
 lean_ctor_set_tag(x_2912, 1);
}
lean_ctor_set(x_2912, 0, x_2885);
lean_ctor_set(x_2912, 1, x_2911);
x_2913 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2914 = l_Lean_Expr_const___override(x_2913, x_2912);
lean_inc(x_2836);
if (lean_is_scalar(x_2887)) {
 x_2915 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2915 = x_2887;
 lean_ctor_set_tag(x_2915, 1);
}
lean_ctor_set(x_2915, 0, x_2836);
lean_ctor_set(x_2915, 1, x_2909);
lean_inc(x_2847);
if (lean_is_scalar(x_2853)) {
 x_2916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2916 = x_2853;
 lean_ctor_set_tag(x_2916, 1);
}
lean_ctor_set(x_2916, 0, x_2847);
lean_ctor_set(x_2916, 1, x_2915);
x_2917 = lean_array_mk(x_2916);
x_2918 = l_Lean_mkAppN(x_2914, x_2917);
lean_dec(x_2917);
x_2919 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2920 = l_Lean_Meta_trySynthInstance(x_2918, x_2919, x_3, x_4, x_5, x_6, x_2907);
if (lean_obj_tag(x_2920) == 0)
{
lean_object* x_2921; 
x_2921 = lean_ctor_get(x_2920, 0);
lean_inc(x_2921);
if (lean_obj_tag(x_2921) == 1)
{
lean_object* x_2922; lean_object* x_2923; lean_object* x_2924; 
x_2922 = lean_ctor_get(x_2920, 1);
lean_inc(x_2922);
lean_dec(x_2920);
x_2923 = lean_ctor_get(x_2921, 0);
lean_inc(x_2923);
lean_dec(x_2921);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2848);
x_2924 = l_Lean_Meta_getDecLevel(x_2848, x_3, x_4, x_5, x_6, x_2922);
if (lean_obj_tag(x_2924) == 0)
{
lean_object* x_2925; lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; 
x_2925 = lean_ctor_get(x_2924, 0);
lean_inc(x_2925);
x_2926 = lean_ctor_get(x_2924, 1);
lean_inc(x_2926);
if (lean_is_exclusive(x_2924)) {
 lean_ctor_release(x_2924, 0);
 lean_ctor_release(x_2924, 1);
 x_2927 = x_2924;
} else {
 lean_dec_ref(x_2924);
 x_2927 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2928 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_2926);
if (lean_obj_tag(x_2928) == 0)
{
lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; 
x_2929 = lean_ctor_get(x_2928, 0);
lean_inc(x_2929);
x_2930 = lean_ctor_get(x_2928, 1);
lean_inc(x_2930);
if (lean_is_exclusive(x_2928)) {
 lean_ctor_release(x_2928, 0);
 lean_ctor_release(x_2928, 1);
 x_2931 = x_2928;
} else {
 lean_dec_ref(x_2928);
 x_2931 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_2932 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_2930);
if (lean_obj_tag(x_2932) == 0)
{
lean_object* x_2933; lean_object* x_2934; lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; lean_object* x_2941; lean_object* x_2942; lean_object* x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; 
x_2933 = lean_ctor_get(x_2932, 0);
lean_inc(x_2933);
x_2934 = lean_ctor_get(x_2932, 1);
lean_inc(x_2934);
if (lean_is_exclusive(x_2932)) {
 lean_ctor_release(x_2932, 0);
 lean_ctor_release(x_2932, 1);
 x_2935 = x_2932;
} else {
 lean_dec_ref(x_2932);
 x_2935 = lean_box(0);
}
if (lean_is_scalar(x_2935)) {
 x_2936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2936 = x_2935;
 lean_ctor_set_tag(x_2936, 1);
}
lean_ctor_set(x_2936, 0, x_2933);
lean_ctor_set(x_2936, 1, x_2909);
if (lean_is_scalar(x_2931)) {
 x_2937 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2937 = x_2931;
 lean_ctor_set_tag(x_2937, 1);
}
lean_ctor_set(x_2937, 0, x_2929);
lean_ctor_set(x_2937, 1, x_2936);
if (lean_is_scalar(x_2927)) {
 x_2938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2938 = x_2927;
 lean_ctor_set_tag(x_2938, 1);
}
lean_ctor_set(x_2938, 0, x_2925);
lean_ctor_set(x_2938, 1, x_2937);
x_2939 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_2938);
x_2940 = l_Lean_Expr_const___override(x_2939, x_2938);
if (lean_is_scalar(x_2849)) {
 x_2941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2941 = x_2849;
 lean_ctor_set_tag(x_2941, 1);
}
lean_ctor_set(x_2941, 0, x_1);
lean_ctor_set(x_2941, 1, x_2909);
lean_inc(x_2941);
lean_inc(x_2848);
x_2942 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2942, 0, x_2848);
lean_ctor_set(x_2942, 1, x_2941);
lean_inc(x_2923);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_2942);
lean_ctor_set(x_24, 0, x_2923);
lean_inc(x_2836);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_2836);
lean_inc(x_2847);
x_2943 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2943, 0, x_2847);
lean_ctor_set(x_2943, 1, x_17);
x_2944 = lean_array_mk(x_2943);
x_2945 = l_Lean_mkAppN(x_2940, x_2944);
lean_dec(x_2944);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2945);
x_2946 = lean_infer_type(x_2945, x_3, x_4, x_5, x_6, x_2934);
if (lean_obj_tag(x_2946) == 0)
{
lean_object* x_2947; lean_object* x_2948; lean_object* x_2949; lean_object* x_2950; 
x_2947 = lean_ctor_get(x_2946, 0);
lean_inc(x_2947);
x_2948 = lean_ctor_get(x_2946, 1);
lean_inc(x_2948);
if (lean_is_exclusive(x_2946)) {
 lean_ctor_release(x_2946, 0);
 lean_ctor_release(x_2946, 1);
 x_2949 = x_2946;
} else {
 lean_dec_ref(x_2946);
 x_2949 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_2950 = l_Lean_Meta_isExprDefEq(x_19, x_2947, x_3, x_4, x_5, x_6, x_2948);
if (lean_obj_tag(x_2950) == 0)
{
lean_object* x_2951; uint8_t x_2952; 
x_2951 = lean_ctor_get(x_2950, 0);
lean_inc(x_2951);
x_2952 = lean_unbox(x_2951);
lean_dec(x_2951);
if (x_2952 == 0)
{
lean_object* x_2953; lean_object* x_2954; 
lean_dec(x_2945);
lean_dec(x_2845);
x_2953 = lean_ctor_get(x_2950, 1);
lean_inc(x_2953);
lean_dec(x_2950);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2836);
x_2954 = l_Lean_Meta_isMonad_x3f(x_2836, x_3, x_4, x_5, x_6, x_2953);
if (lean_obj_tag(x_2954) == 0)
{
lean_object* x_2955; 
x_2955 = lean_ctor_get(x_2954, 0);
lean_inc(x_2955);
if (lean_obj_tag(x_2955) == 0)
{
lean_object* x_2956; lean_object* x_2957; lean_object* x_2958; 
lean_dec(x_2949);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2956 = lean_ctor_get(x_2954, 1);
lean_inc(x_2956);
if (lean_is_exclusive(x_2954)) {
 lean_ctor_release(x_2954, 0);
 lean_ctor_release(x_2954, 1);
 x_2957 = x_2954;
} else {
 lean_dec_ref(x_2954);
 x_2957 = lean_box(0);
}
if (lean_is_scalar(x_2957)) {
 x_2958 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2958 = x_2957;
}
lean_ctor_set(x_2958, 0, x_2919);
lean_ctor_set(x_2958, 1, x_2956);
return x_2958;
}
else
{
lean_object* x_2959; lean_object* x_2960; lean_object* x_2961; 
x_2959 = lean_ctor_get(x_2954, 1);
lean_inc(x_2959);
lean_dec(x_2954);
x_2960 = lean_ctor_get(x_2955, 0);
lean_inc(x_2960);
lean_dec(x_2955);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2848);
x_2961 = l_Lean_Meta_getLevel(x_2848, x_3, x_4, x_5, x_6, x_2959);
if (lean_obj_tag(x_2961) == 0)
{
lean_object* x_2962; lean_object* x_2963; lean_object* x_2964; lean_object* x_2965; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2837);
x_2965 = l_Lean_Meta_getLevel(x_2837, x_3, x_4, x_5, x_6, x_2963);
if (lean_obj_tag(x_2965) == 0)
{
lean_object* x_2966; lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; uint8_t x_2980; lean_object* x_2981; lean_object* x_2982; 
x_2966 = lean_ctor_get(x_2965, 0);
lean_inc(x_2966);
x_2967 = lean_ctor_get(x_2965, 1);
lean_inc(x_2967);
if (lean_is_exclusive(x_2965)) {
 lean_ctor_release(x_2965, 0);
 lean_ctor_release(x_2965, 1);
 x_2968 = x_2965;
} else {
 lean_dec_ref(x_2965);
 x_2968 = lean_box(0);
}
if (lean_is_scalar(x_2968)) {
 x_2969 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2969 = x_2968;
 lean_ctor_set_tag(x_2969, 1);
}
lean_ctor_set(x_2969, 0, x_2966);
lean_ctor_set(x_2969, 1, x_2909);
if (lean_is_scalar(x_2964)) {
 x_2970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2970 = x_2964;
 lean_ctor_set_tag(x_2970, 1);
}
lean_ctor_set(x_2970, 0, x_2962);
lean_ctor_set(x_2970, 1, x_2969);
x_2971 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_2972 = l_Lean_Expr_const___override(x_2971, x_2970);
lean_inc(x_2837);
if (lean_is_scalar(x_2949)) {
 x_2973 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2973 = x_2949;
 lean_ctor_set_tag(x_2973, 1);
}
lean_ctor_set(x_2973, 0, x_2837);
lean_ctor_set(x_2973, 1, x_2909);
x_2974 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_2975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2975, 0, x_2974);
lean_ctor_set(x_2975, 1, x_2973);
lean_inc(x_2848);
x_2976 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2976, 0, x_2848);
lean_ctor_set(x_2976, 1, x_2975);
x_2977 = lean_array_mk(x_2976);
x_2978 = l_Lean_mkAppN(x_2972, x_2977);
lean_dec(x_2977);
x_2979 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_2980 = 0;
lean_inc(x_2848);
x_2981 = l_Lean_Expr_forallE___override(x_2979, x_2848, x_2978, x_2980);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2982 = l_Lean_Meta_trySynthInstance(x_2981, x_2919, x_3, x_4, x_5, x_6, x_2967);
if (lean_obj_tag(x_2982) == 0)
{
lean_object* x_2983; 
x_2983 = lean_ctor_get(x_2982, 0);
lean_inc(x_2983);
if (lean_obj_tag(x_2983) == 1)
{
lean_object* x_2984; lean_object* x_2985; lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; lean_object* x_2989; lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; 
x_2984 = lean_ctor_get(x_2982, 1);
lean_inc(x_2984);
lean_dec(x_2982);
x_2985 = lean_ctor_get(x_2983, 0);
lean_inc(x_2985);
lean_dec(x_2983);
x_2986 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_2987 = l_Lean_Expr_const___override(x_2986, x_2938);
x_2988 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2988, 0, x_2960);
lean_ctor_set(x_2988, 1, x_2941);
x_2989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2989, 0, x_2985);
lean_ctor_set(x_2989, 1, x_2988);
x_2990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2990, 0, x_2923);
lean_ctor_set(x_2990, 1, x_2989);
x_2991 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2991, 0, x_2837);
lean_ctor_set(x_2991, 1, x_2990);
x_2992 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2992, 0, x_2848);
lean_ctor_set(x_2992, 1, x_2991);
x_2993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2993, 0, x_2836);
lean_ctor_set(x_2993, 1, x_2992);
x_2994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2994, 0, x_2847);
lean_ctor_set(x_2994, 1, x_2993);
x_2995 = lean_array_mk(x_2994);
x_2996 = l_Lean_mkAppN(x_2987, x_2995);
lean_dec(x_2995);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2997 = l_Lean_Meta_expandCoe(x_2996, x_3, x_4, x_5, x_6, x_2984);
if (lean_obj_tag(x_2997) == 0)
{
lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; 
x_2998 = lean_ctor_get(x_2997, 0);
lean_inc(x_2998);
x_2999 = lean_ctor_get(x_2997, 1);
lean_inc(x_2999);
lean_dec(x_2997);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2998);
x_3000 = lean_infer_type(x_2998, x_3, x_4, x_5, x_6, x_2999);
if (lean_obj_tag(x_3000) == 0)
{
lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; 
x_3001 = lean_ctor_get(x_3000, 0);
lean_inc(x_3001);
x_3002 = lean_ctor_get(x_3000, 1);
lean_inc(x_3002);
lean_dec(x_3000);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3003 = l_Lean_Meta_isExprDefEq(x_19, x_3001, x_3, x_4, x_5, x_6, x_3002);
if (lean_obj_tag(x_3003) == 0)
{
lean_object* x_3004; uint8_t x_3005; 
x_3004 = lean_ctor_get(x_3003, 0);
lean_inc(x_3004);
x_3005 = lean_unbox(x_3004);
lean_dec(x_3004);
if (x_3005 == 0)
{
lean_object* x_3006; lean_object* x_3007; lean_object* x_3008; 
lean_dec(x_2998);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3006 = lean_ctor_get(x_3003, 1);
lean_inc(x_3006);
if (lean_is_exclusive(x_3003)) {
 lean_ctor_release(x_3003, 0);
 lean_ctor_release(x_3003, 1);
 x_3007 = x_3003;
} else {
 lean_dec_ref(x_3003);
 x_3007 = lean_box(0);
}
if (lean_is_scalar(x_3007)) {
 x_3008 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3008 = x_3007;
}
lean_ctor_set(x_3008, 0, x_2919);
lean_ctor_set(x_3008, 1, x_3006);
return x_3008;
}
else
{
lean_object* x_3009; lean_object* x_3010; lean_object* x_3011; lean_object* x_3012; lean_object* x_3013; lean_object* x_3014; lean_object* x_3015; 
x_3009 = lean_ctor_get(x_3003, 1);
lean_inc(x_3009);
lean_dec(x_3003);
x_3010 = lean_box(0);
x_3011 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2998, x_3010, x_3, x_4, x_5, x_6, x_3009);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3012 = lean_ctor_get(x_3011, 0);
lean_inc(x_3012);
x_3013 = lean_ctor_get(x_3011, 1);
lean_inc(x_3013);
if (lean_is_exclusive(x_3011)) {
 lean_ctor_release(x_3011, 0);
 lean_ctor_release(x_3011, 1);
 x_3014 = x_3011;
} else {
 lean_dec_ref(x_3011);
 x_3014 = lean_box(0);
}
if (lean_is_scalar(x_3014)) {
 x_3015 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3015 = x_3014;
}
lean_ctor_set(x_3015, 0, x_3012);
lean_ctor_set(x_3015, 1, x_3013);
return x_3015;
}
}
else
{
lean_object* x_3016; lean_object* x_3017; 
lean_dec(x_2998);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3016 = lean_ctor_get(x_3003, 0);
lean_inc(x_3016);
x_3017 = lean_ctor_get(x_3003, 1);
lean_inc(x_3017);
lean_dec(x_3003);
x_8 = x_3016;
x_9 = x_3017;
goto block_16;
}
}
else
{
lean_object* x_3018; lean_object* x_3019; 
lean_dec(x_2998);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3018 = lean_ctor_get(x_3000, 0);
lean_inc(x_3018);
x_3019 = lean_ctor_get(x_3000, 1);
lean_inc(x_3019);
lean_dec(x_3000);
x_8 = x_3018;
x_9 = x_3019;
goto block_16;
}
}
else
{
lean_object* x_3020; lean_object* x_3021; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3020 = lean_ctor_get(x_2997, 0);
lean_inc(x_3020);
x_3021 = lean_ctor_get(x_2997, 1);
lean_inc(x_3021);
lean_dec(x_2997);
x_8 = x_3020;
x_9 = x_3021;
goto block_16;
}
}
else
{
lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; 
lean_dec(x_2983);
lean_dec(x_2960);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3022 = lean_ctor_get(x_2982, 1);
lean_inc(x_3022);
if (lean_is_exclusive(x_2982)) {
 lean_ctor_release(x_2982, 0);
 lean_ctor_release(x_2982, 1);
 x_3023 = x_2982;
} else {
 lean_dec_ref(x_2982);
 x_3023 = lean_box(0);
}
if (lean_is_scalar(x_3023)) {
 x_3024 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3024 = x_3023;
}
lean_ctor_set(x_3024, 0, x_2919);
lean_ctor_set(x_3024, 1, x_3022);
return x_3024;
}
}
else
{
lean_object* x_3025; lean_object* x_3026; 
lean_dec(x_2960);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3025 = lean_ctor_get(x_2982, 0);
lean_inc(x_3025);
x_3026 = lean_ctor_get(x_2982, 1);
lean_inc(x_3026);
lean_dec(x_2982);
x_8 = x_3025;
x_9 = x_3026;
goto block_16;
}
}
else
{
lean_object* x_3027; lean_object* x_3028; 
lean_dec(x_2964);
lean_dec(x_2962);
lean_dec(x_2960);
lean_dec(x_2949);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3027 = lean_ctor_get(x_2965, 0);
lean_inc(x_3027);
x_3028 = lean_ctor_get(x_2965, 1);
lean_inc(x_3028);
lean_dec(x_2965);
x_8 = x_3027;
x_9 = x_3028;
goto block_16;
}
}
else
{
lean_object* x_3029; lean_object* x_3030; 
lean_dec(x_2960);
lean_dec(x_2949);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3029 = lean_ctor_get(x_2961, 0);
lean_inc(x_3029);
x_3030 = lean_ctor_get(x_2961, 1);
lean_inc(x_3030);
lean_dec(x_2961);
x_8 = x_3029;
x_9 = x_3030;
goto block_16;
}
}
}
else
{
lean_object* x_3031; lean_object* x_3032; 
lean_dec(x_2949);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3031 = lean_ctor_get(x_2954, 0);
lean_inc(x_3031);
x_3032 = lean_ctor_get(x_2954, 1);
lean_inc(x_3032);
lean_dec(x_2954);
x_8 = x_3031;
x_9 = x_3032;
goto block_16;
}
}
else
{
lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; 
lean_dec(x_2949);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3033 = lean_ctor_get(x_2950, 1);
lean_inc(x_3033);
if (lean_is_exclusive(x_2950)) {
 lean_ctor_release(x_2950, 0);
 lean_ctor_release(x_2950, 1);
 x_3034 = x_2950;
} else {
 lean_dec_ref(x_2950);
 x_3034 = lean_box(0);
}
if (lean_is_scalar(x_2845)) {
 x_3035 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3035 = x_2845;
}
lean_ctor_set(x_3035, 0, x_2945);
if (lean_is_scalar(x_3034)) {
 x_3036 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3036 = x_3034;
}
lean_ctor_set(x_3036, 0, x_3035);
lean_ctor_set(x_3036, 1, x_3033);
return x_3036;
}
}
else
{
lean_object* x_3037; lean_object* x_3038; 
lean_dec(x_2949);
lean_dec(x_2945);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3037 = lean_ctor_get(x_2950, 0);
lean_inc(x_3037);
x_3038 = lean_ctor_get(x_2950, 1);
lean_inc(x_3038);
lean_dec(x_2950);
x_8 = x_3037;
x_9 = x_3038;
goto block_16;
}
}
else
{
lean_object* x_3039; lean_object* x_3040; 
lean_dec(x_2945);
lean_dec(x_2941);
lean_dec(x_2938);
lean_dec(x_2923);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3039 = lean_ctor_get(x_2946, 0);
lean_inc(x_3039);
x_3040 = lean_ctor_get(x_2946, 1);
lean_inc(x_3040);
lean_dec(x_2946);
x_8 = x_3039;
x_9 = x_3040;
goto block_16;
}
}
else
{
lean_object* x_3041; lean_object* x_3042; 
lean_dec(x_2931);
lean_dec(x_2929);
lean_dec(x_2927);
lean_dec(x_2925);
lean_dec(x_2923);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3041 = lean_ctor_get(x_2932, 0);
lean_inc(x_3041);
x_3042 = lean_ctor_get(x_2932, 1);
lean_inc(x_3042);
lean_dec(x_2932);
x_8 = x_3041;
x_9 = x_3042;
goto block_16;
}
}
else
{
lean_object* x_3043; lean_object* x_3044; 
lean_dec(x_2927);
lean_dec(x_2925);
lean_dec(x_2923);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3043 = lean_ctor_get(x_2928, 0);
lean_inc(x_3043);
x_3044 = lean_ctor_get(x_2928, 1);
lean_inc(x_3044);
lean_dec(x_2928);
x_8 = x_3043;
x_9 = x_3044;
goto block_16;
}
}
else
{
lean_object* x_3045; lean_object* x_3046; 
lean_dec(x_2923);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3045 = lean_ctor_get(x_2924, 0);
lean_inc(x_3045);
x_3046 = lean_ctor_get(x_2924, 1);
lean_inc(x_3046);
lean_dec(x_2924);
x_8 = x_3045;
x_9 = x_3046;
goto block_16;
}
}
else
{
lean_object* x_3047; lean_object* x_3048; lean_object* x_3049; 
lean_dec(x_2921);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3047 = lean_ctor_get(x_2920, 1);
lean_inc(x_3047);
if (lean_is_exclusive(x_2920)) {
 lean_ctor_release(x_2920, 0);
 lean_ctor_release(x_2920, 1);
 x_3048 = x_2920;
} else {
 lean_dec_ref(x_2920);
 x_3048 = lean_box(0);
}
if (lean_is_scalar(x_3048)) {
 x_3049 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3049 = x_3048;
}
lean_ctor_set(x_3049, 0, x_2919);
lean_ctor_set(x_3049, 1, x_3047);
return x_3049;
}
}
else
{
lean_object* x_3050; lean_object* x_3051; 
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3050 = lean_ctor_get(x_2920, 0);
lean_inc(x_3050);
x_3051 = lean_ctor_get(x_2920, 1);
lean_inc(x_3051);
lean_dec(x_2920);
x_8 = x_3050;
x_9 = x_3051;
goto block_16;
}
}
else
{
lean_object* x_3052; lean_object* x_3053; 
lean_dec(x_2904);
lean_dec(x_2902);
lean_dec(x_2891);
lean_dec(x_2887);
lean_dec(x_2885);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3052 = lean_ctor_get(x_2905, 0);
lean_inc(x_3052);
x_3053 = lean_ctor_get(x_2905, 1);
lean_inc(x_3053);
lean_dec(x_2905);
x_8 = x_3052;
x_9 = x_3053;
goto block_16;
}
}
else
{
lean_object* x_3054; lean_object* x_3055; 
lean_dec(x_2891);
lean_dec(x_2887);
lean_dec(x_2885);
lean_dec(x_2883);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3054 = lean_ctor_get(x_2901, 0);
lean_inc(x_3054);
x_3055 = lean_ctor_get(x_2901, 1);
lean_inc(x_3055);
lean_dec(x_2901);
x_8 = x_3054;
x_9 = x_3055;
goto block_16;
}
}
}
else
{
lean_object* x_3056; lean_object* x_3057; 
lean_dec(x_2891);
lean_dec(x_2887);
lean_dec(x_2885);
lean_dec(x_2883);
lean_dec(x_2873);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3056 = lean_ctor_get(x_2893, 0);
lean_inc(x_3056);
x_3057 = lean_ctor_get(x_2893, 1);
lean_inc(x_3057);
lean_dec(x_2893);
x_8 = x_3056;
x_9 = x_3057;
goto block_16;
}
}
else
{
lean_object* x_3058; lean_object* x_3059; 
lean_dec(x_2887);
lean_dec(x_2885);
lean_dec(x_2883);
lean_dec(x_2873);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3058 = lean_ctor_get(x_2888, 0);
lean_inc(x_3058);
x_3059 = lean_ctor_get(x_2888, 1);
lean_inc(x_3059);
lean_dec(x_2888);
x_8 = x_3058;
x_9 = x_3059;
goto block_16;
}
}
else
{
lean_object* x_3060; lean_object* x_3061; 
lean_dec(x_2883);
lean_dec(x_2882);
lean_dec(x_2873);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3060 = lean_ctor_get(x_2884, 0);
lean_inc(x_3060);
x_3061 = lean_ctor_get(x_2884, 1);
lean_inc(x_3061);
lean_dec(x_2884);
x_8 = x_3060;
x_9 = x_3061;
goto block_16;
}
}
else
{
lean_object* x_3062; lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; 
lean_dec(x_2880);
lean_dec(x_2879);
lean_dec(x_2873);
lean_dec(x_2872);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3062 = lean_ctor_get(x_2877, 1);
lean_inc(x_3062);
if (lean_is_exclusive(x_2877)) {
 lean_ctor_release(x_2877, 0);
 lean_ctor_release(x_2877, 1);
 x_3063 = x_2877;
} else {
 lean_dec_ref(x_2877);
 x_3063 = lean_box(0);
}
x_3064 = lean_box(0);
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
lean_object* x_3066; lean_object* x_3067; lean_object* x_3068; lean_object* x_3069; 
lean_dec(x_2879);
lean_dec(x_2878);
lean_dec(x_2873);
lean_dec(x_2872);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3066 = lean_ctor_get(x_2877, 1);
lean_inc(x_3066);
if (lean_is_exclusive(x_2877)) {
 lean_ctor_release(x_2877, 0);
 lean_ctor_release(x_2877, 1);
 x_3067 = x_2877;
} else {
 lean_dec_ref(x_2877);
 x_3067 = lean_box(0);
}
x_3068 = lean_box(0);
if (lean_is_scalar(x_3067)) {
 x_3069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3069 = x_3067;
}
lean_ctor_set(x_3069, 0, x_3068);
lean_ctor_set(x_3069, 1, x_3066);
return x_3069;
}
}
else
{
lean_object* x_3070; lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; 
lean_dec(x_2878);
lean_dec(x_2873);
lean_dec(x_2872);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3070 = lean_ctor_get(x_2877, 1);
lean_inc(x_3070);
if (lean_is_exclusive(x_2877)) {
 lean_ctor_release(x_2877, 0);
 lean_ctor_release(x_2877, 1);
 x_3071 = x_2877;
} else {
 lean_dec_ref(x_2877);
 x_3071 = lean_box(0);
}
x_3072 = lean_box(0);
if (lean_is_scalar(x_3071)) {
 x_3073 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3073 = x_3071;
}
lean_ctor_set(x_3073, 0, x_3072);
lean_ctor_set(x_3073, 1, x_3070);
return x_3073;
}
}
else
{
lean_object* x_3074; lean_object* x_3075; lean_object* x_3076; uint8_t x_3077; 
lean_dec(x_2873);
lean_dec(x_2872);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3074 = lean_ctor_get(x_2877, 0);
lean_inc(x_3074);
x_3075 = lean_ctor_get(x_2877, 1);
lean_inc(x_3075);
if (lean_is_exclusive(x_2877)) {
 lean_ctor_release(x_2877, 0);
 lean_ctor_release(x_2877, 1);
 x_3076 = x_2877;
} else {
 lean_dec_ref(x_2877);
 x_3076 = lean_box(0);
}
x_3077 = l_Lean_Exception_isInterrupt(x_3074);
if (x_3077 == 0)
{
uint8_t x_3078; 
x_3078 = l_Lean_Exception_isRuntime(x_3074);
if (x_3078 == 0)
{
lean_object* x_3079; lean_object* x_3080; 
lean_dec(x_3074);
x_3079 = lean_box(0);
if (lean_is_scalar(x_3076)) {
 x_3080 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3080 = x_3076;
 lean_ctor_set_tag(x_3080, 0);
}
lean_ctor_set(x_3080, 0, x_3079);
lean_ctor_set(x_3080, 1, x_3075);
return x_3080;
}
else
{
lean_object* x_3081; 
if (lean_is_scalar(x_3076)) {
 x_3081 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3081 = x_3076;
}
lean_ctor_set(x_3081, 0, x_3074);
lean_ctor_set(x_3081, 1, x_3075);
return x_3081;
}
}
else
{
lean_object* x_3082; 
if (lean_is_scalar(x_3076)) {
 x_3082 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3082 = x_3076;
}
lean_ctor_set(x_3082, 0, x_3074);
lean_ctor_set(x_3082, 1, x_3075);
return x_3082;
}
}
}
else
{
lean_object* x_3083; lean_object* x_3084; lean_object* x_3085; uint8_t x_3086; 
lean_dec(x_2873);
lean_dec(x_2872);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3083 = lean_ctor_get(x_2874, 0);
lean_inc(x_3083);
x_3084 = lean_ctor_get(x_2874, 1);
lean_inc(x_3084);
if (lean_is_exclusive(x_2874)) {
 lean_ctor_release(x_2874, 0);
 lean_ctor_release(x_2874, 1);
 x_3085 = x_2874;
} else {
 lean_dec_ref(x_2874);
 x_3085 = lean_box(0);
}
x_3086 = l_Lean_Exception_isInterrupt(x_3083);
if (x_3086 == 0)
{
uint8_t x_3087; 
x_3087 = l_Lean_Exception_isRuntime(x_3083);
if (x_3087 == 0)
{
lean_object* x_3088; lean_object* x_3089; 
lean_dec(x_3083);
x_3088 = lean_box(0);
if (lean_is_scalar(x_3085)) {
 x_3089 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3089 = x_3085;
 lean_ctor_set_tag(x_3089, 0);
}
lean_ctor_set(x_3089, 0, x_3088);
lean_ctor_set(x_3089, 1, x_3084);
return x_3089;
}
else
{
lean_object* x_3090; 
if (lean_is_scalar(x_3085)) {
 x_3090 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3090 = x_3085;
}
lean_ctor_set(x_3090, 0, x_3083);
lean_ctor_set(x_3090, 1, x_3084);
return x_3090;
}
}
else
{
lean_object* x_3091; 
if (lean_is_scalar(x_3085)) {
 x_3091 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3091 = x_3085;
}
lean_ctor_set(x_3091, 0, x_3083);
lean_ctor_set(x_3091, 1, x_3084);
return x_3091;
}
}
}
else
{
lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; lean_object* x_3095; 
lean_dec(x_2870);
lean_dec(x_2869);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3092 = lean_ctor_get(x_2867, 1);
lean_inc(x_3092);
if (lean_is_exclusive(x_2867)) {
 lean_ctor_release(x_2867, 0);
 lean_ctor_release(x_2867, 1);
 x_3093 = x_2867;
} else {
 lean_dec_ref(x_2867);
 x_3093 = lean_box(0);
}
x_3094 = lean_box(0);
if (lean_is_scalar(x_3093)) {
 x_3095 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3095 = x_3093;
}
lean_ctor_set(x_3095, 0, x_3094);
lean_ctor_set(x_3095, 1, x_3092);
return x_3095;
}
}
else
{
lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; 
lean_dec(x_2869);
lean_dec(x_2868);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3096 = lean_ctor_get(x_2867, 1);
lean_inc(x_3096);
if (lean_is_exclusive(x_2867)) {
 lean_ctor_release(x_2867, 0);
 lean_ctor_release(x_2867, 1);
 x_3097 = x_2867;
} else {
 lean_dec_ref(x_2867);
 x_3097 = lean_box(0);
}
x_3098 = lean_box(0);
if (lean_is_scalar(x_3097)) {
 x_3099 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3099 = x_3097;
}
lean_ctor_set(x_3099, 0, x_3098);
lean_ctor_set(x_3099, 1, x_3096);
return x_3099;
}
}
else
{
lean_object* x_3100; lean_object* x_3101; lean_object* x_3102; lean_object* x_3103; 
lean_dec(x_2868);
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3100 = lean_ctor_get(x_2867, 1);
lean_inc(x_3100);
if (lean_is_exclusive(x_2867)) {
 lean_ctor_release(x_2867, 0);
 lean_ctor_release(x_2867, 1);
 x_3101 = x_2867;
} else {
 lean_dec_ref(x_2867);
 x_3101 = lean_box(0);
}
x_3102 = lean_box(0);
if (lean_is_scalar(x_3101)) {
 x_3103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3103 = x_3101;
}
lean_ctor_set(x_3103, 0, x_3102);
lean_ctor_set(x_3103, 1, x_3100);
return x_3103;
}
}
else
{
lean_object* x_3104; lean_object* x_3105; lean_object* x_3106; uint8_t x_3107; 
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3104 = lean_ctor_get(x_2867, 0);
lean_inc(x_3104);
x_3105 = lean_ctor_get(x_2867, 1);
lean_inc(x_3105);
if (lean_is_exclusive(x_2867)) {
 lean_ctor_release(x_2867, 0);
 lean_ctor_release(x_2867, 1);
 x_3106 = x_2867;
} else {
 lean_dec_ref(x_2867);
 x_3106 = lean_box(0);
}
x_3107 = l_Lean_Exception_isInterrupt(x_3104);
if (x_3107 == 0)
{
uint8_t x_3108; 
x_3108 = l_Lean_Exception_isRuntime(x_3104);
if (x_3108 == 0)
{
lean_object* x_3109; lean_object* x_3110; 
lean_dec(x_3104);
x_3109 = lean_box(0);
if (lean_is_scalar(x_3106)) {
 x_3110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3110 = x_3106;
 lean_ctor_set_tag(x_3110, 0);
}
lean_ctor_set(x_3110, 0, x_3109);
lean_ctor_set(x_3110, 1, x_3105);
return x_3110;
}
else
{
lean_object* x_3111; 
if (lean_is_scalar(x_3106)) {
 x_3111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3111 = x_3106;
}
lean_ctor_set(x_3111, 0, x_3104);
lean_ctor_set(x_3111, 1, x_3105);
return x_3111;
}
}
else
{
lean_object* x_3112; 
if (lean_is_scalar(x_3106)) {
 x_3112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3112 = x_3106;
}
lean_ctor_set(x_3112, 0, x_3104);
lean_ctor_set(x_3112, 1, x_3105);
return x_3112;
}
}
}
else
{
lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; uint8_t x_3116; 
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3113 = lean_ctor_get(x_2864, 0);
lean_inc(x_3113);
x_3114 = lean_ctor_get(x_2864, 1);
lean_inc(x_3114);
if (lean_is_exclusive(x_2864)) {
 lean_ctor_release(x_2864, 0);
 lean_ctor_release(x_2864, 1);
 x_3115 = x_2864;
} else {
 lean_dec_ref(x_2864);
 x_3115 = lean_box(0);
}
x_3116 = l_Lean_Exception_isInterrupt(x_3113);
if (x_3116 == 0)
{
uint8_t x_3117; 
x_3117 = l_Lean_Exception_isRuntime(x_3113);
if (x_3117 == 0)
{
lean_object* x_3118; lean_object* x_3119; 
lean_dec(x_3113);
x_3118 = lean_box(0);
if (lean_is_scalar(x_3115)) {
 x_3119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3119 = x_3115;
 lean_ctor_set_tag(x_3119, 0);
}
lean_ctor_set(x_3119, 0, x_3118);
lean_ctor_set(x_3119, 1, x_3114);
return x_3119;
}
else
{
lean_object* x_3120; 
if (lean_is_scalar(x_3115)) {
 x_3120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3120 = x_3115;
}
lean_ctor_set(x_3120, 0, x_3113);
lean_ctor_set(x_3120, 1, x_3114);
return x_3120;
}
}
else
{
lean_object* x_3121; 
if (lean_is_scalar(x_3115)) {
 x_3121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3121 = x_3115;
}
lean_ctor_set(x_3121, 0, x_3113);
lean_ctor_set(x_3121, 1, x_3114);
return x_3121;
}
}
}
}
else
{
lean_object* x_3122; lean_object* x_3123; 
lean_dec(x_26);
lean_dec(x_19);
x_3122 = lean_ctor_get(x_2854, 1);
lean_inc(x_3122);
lean_dec(x_2854);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3123 = l_Lean_Meta_isMonad_x3f(x_2836, x_3, x_4, x_5, x_6, x_3122);
if (lean_obj_tag(x_3123) == 0)
{
lean_object* x_3124; 
x_3124 = lean_ctor_get(x_3123, 0);
lean_inc(x_3124);
if (lean_obj_tag(x_3124) == 0)
{
lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; 
lean_dec(x_2853);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_1);
x_3125 = lean_ctor_get(x_3123, 1);
lean_inc(x_3125);
lean_dec(x_3123);
x_3126 = l_Lean_Meta_SavedState_restore(x_2851, x_3, x_4, x_5, x_6, x_3125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2851);
x_3127 = lean_ctor_get(x_3126, 1);
lean_inc(x_3127);
if (lean_is_exclusive(x_3126)) {
 lean_ctor_release(x_3126, 0);
 lean_ctor_release(x_3126, 1);
 x_3128 = x_3126;
} else {
 lean_dec_ref(x_3126);
 x_3128 = lean_box(0);
}
x_3129 = lean_box(0);
if (lean_is_scalar(x_3128)) {
 x_3130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3130 = x_3128;
}
lean_ctor_set(x_3130, 0, x_3129);
lean_ctor_set(x_3130, 1, x_3127);
return x_3130;
}
else
{
lean_object* x_3131; lean_object* x_3132; lean_object* x_3133; lean_object* x_3134; lean_object* x_3135; lean_object* x_3136; lean_object* x_3137; lean_object* x_3138; lean_object* x_3139; lean_object* x_3140; lean_object* x_3141; lean_object* x_3142; lean_object* x_3143; lean_object* x_3144; lean_object* x_3145; lean_object* x_3146; lean_object* x_3147; lean_object* x_3157; lean_object* x_3158; 
x_3131 = lean_ctor_get(x_3123, 1);
lean_inc(x_3131);
if (lean_is_exclusive(x_3123)) {
 lean_ctor_release(x_3123, 0);
 lean_ctor_release(x_3123, 1);
 x_3132 = x_3123;
} else {
 lean_dec_ref(x_3123);
 x_3132 = lean_box(0);
}
x_3133 = lean_ctor_get(x_3124, 0);
lean_inc(x_3133);
if (lean_is_exclusive(x_3124)) {
 lean_ctor_release(x_3124, 0);
 x_3134 = x_3124;
} else {
 lean_dec_ref(x_3124);
 x_3134 = lean_box(0);
}
if (lean_is_scalar(x_3134)) {
 x_3135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3135 = x_3134;
}
lean_ctor_set(x_3135, 0, x_2847);
if (lean_is_scalar(x_2845)) {
 x_3136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3136 = x_2845;
}
lean_ctor_set(x_3136, 0, x_2848);
lean_ctor_set(x_29, 0, x_2837);
x_3137 = lean_box(0);
x_3138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3138, 0, x_3133);
x_3139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3139, 0, x_1);
x_3140 = lean_box(0);
if (lean_is_scalar(x_2853)) {
 x_3141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3141 = x_2853;
 lean_ctor_set_tag(x_3141, 1);
}
lean_ctor_set(x_3141, 0, x_3139);
lean_ctor_set(x_3141, 1, x_3140);
if (lean_is_scalar(x_2849)) {
 x_3142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3142 = x_2849;
 lean_ctor_set_tag(x_3142, 1);
}
lean_ctor_set(x_3142, 0, x_3138);
lean_ctor_set(x_3142, 1, x_3141);
x_3143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3143, 0, x_3137);
lean_ctor_set(x_3143, 1, x_3142);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_3143);
lean_ctor_set(x_24, 0, x_29);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_3136);
x_3144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3144, 0, x_3135);
lean_ctor_set(x_3144, 1, x_17);
x_3145 = lean_array_mk(x_3144);
x_3157 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3158 = l_Lean_Meta_mkAppOptM(x_3157, x_3145, x_3, x_4, x_5, x_6, x_3131);
if (lean_obj_tag(x_3158) == 0)
{
lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; 
x_3159 = lean_ctor_get(x_3158, 0);
lean_inc(x_3159);
x_3160 = lean_ctor_get(x_3158, 1);
lean_inc(x_3160);
lean_dec(x_3158);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3161 = l_Lean_Meta_expandCoe(x_3159, x_3, x_4, x_5, x_6, x_3160);
if (lean_obj_tag(x_3161) == 0)
{
lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; lean_object* x_3165; lean_object* x_3166; 
lean_dec(x_3132);
lean_dec(x_2851);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3162 = lean_ctor_get(x_3161, 0);
lean_inc(x_3162);
x_3163 = lean_ctor_get(x_3161, 1);
lean_inc(x_3163);
if (lean_is_exclusive(x_3161)) {
 lean_ctor_release(x_3161, 0);
 lean_ctor_release(x_3161, 1);
 x_3164 = x_3161;
} else {
 lean_dec_ref(x_3161);
 x_3164 = lean_box(0);
}
x_3165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3165, 0, x_3162);
if (lean_is_scalar(x_3164)) {
 x_3166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3166 = x_3164;
}
lean_ctor_set(x_3166, 0, x_3165);
lean_ctor_set(x_3166, 1, x_3163);
return x_3166;
}
else
{
lean_object* x_3167; lean_object* x_3168; 
x_3167 = lean_ctor_get(x_3161, 0);
lean_inc(x_3167);
x_3168 = lean_ctor_get(x_3161, 1);
lean_inc(x_3168);
lean_dec(x_3161);
x_3146 = x_3167;
x_3147 = x_3168;
goto block_3156;
}
}
else
{
lean_object* x_3169; lean_object* x_3170; 
x_3169 = lean_ctor_get(x_3158, 0);
lean_inc(x_3169);
x_3170 = lean_ctor_get(x_3158, 1);
lean_inc(x_3170);
lean_dec(x_3158);
x_3146 = x_3169;
x_3147 = x_3170;
goto block_3156;
}
block_3156:
{
uint8_t x_3148; 
x_3148 = l_Lean_Exception_isInterrupt(x_3146);
if (x_3148 == 0)
{
uint8_t x_3149; 
x_3149 = l_Lean_Exception_isRuntime(x_3146);
if (x_3149 == 0)
{
lean_object* x_3150; lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; 
lean_dec(x_3146);
lean_dec(x_3132);
x_3150 = l_Lean_Meta_SavedState_restore(x_2851, x_3, x_4, x_5, x_6, x_3147);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2851);
x_3151 = lean_ctor_get(x_3150, 1);
lean_inc(x_3151);
if (lean_is_exclusive(x_3150)) {
 lean_ctor_release(x_3150, 0);
 lean_ctor_release(x_3150, 1);
 x_3152 = x_3150;
} else {
 lean_dec_ref(x_3150);
 x_3152 = lean_box(0);
}
if (lean_is_scalar(x_3152)) {
 x_3153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3153 = x_3152;
}
lean_ctor_set(x_3153, 0, x_3137);
lean_ctor_set(x_3153, 1, x_3151);
return x_3153;
}
else
{
lean_object* x_3154; 
lean_dec(x_2851);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_3132)) {
 x_3154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3154 = x_3132;
 lean_ctor_set_tag(x_3154, 1);
}
lean_ctor_set(x_3154, 0, x_3146);
lean_ctor_set(x_3154, 1, x_3147);
return x_3154;
}
}
else
{
lean_object* x_3155; 
lean_dec(x_2851);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_3132)) {
 x_3155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3155 = x_3132;
 lean_ctor_set_tag(x_3155, 1);
}
lean_ctor_set(x_3155, 0, x_3146);
lean_ctor_set(x_3155, 1, x_3147);
return x_3155;
}
}
}
}
else
{
lean_object* x_3171; lean_object* x_3172; lean_object* x_3173; lean_object* x_3174; 
lean_dec(x_2853);
lean_dec(x_2851);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_free_object(x_29);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3171 = lean_ctor_get(x_3123, 0);
lean_inc(x_3171);
x_3172 = lean_ctor_get(x_3123, 1);
lean_inc(x_3172);
if (lean_is_exclusive(x_3123)) {
 lean_ctor_release(x_3123, 0);
 lean_ctor_release(x_3123, 1);
 x_3173 = x_3123;
} else {
 lean_dec_ref(x_3123);
 x_3173 = lean_box(0);
}
if (lean_is_scalar(x_3173)) {
 x_3174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3174 = x_3173;
}
lean_ctor_set(x_3174, 0, x_3171);
lean_ctor_set(x_3174, 1, x_3172);
return x_3174;
}
}
}
else
{
lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; lean_object* x_3178; 
lean_dec(x_2853);
lean_dec(x_2851);
lean_dec(x_2849);
lean_dec(x_2848);
lean_dec(x_2847);
lean_dec(x_2845);
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3175 = lean_ctor_get(x_2854, 0);
lean_inc(x_3175);
x_3176 = lean_ctor_get(x_2854, 1);
lean_inc(x_3176);
if (lean_is_exclusive(x_2854)) {
 lean_ctor_release(x_2854, 0);
 lean_ctor_release(x_2854, 1);
 x_3177 = x_2854;
} else {
 lean_dec_ref(x_2854);
 x_3177 = lean_box(0);
}
if (lean_is_scalar(x_3177)) {
 x_3178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3178 = x_3177;
}
lean_ctor_set(x_3178, 0, x_3175);
lean_ctor_set(x_3178, 1, x_3176);
return x_3178;
}
}
}
else
{
lean_object* x_3179; lean_object* x_3180; lean_object* x_3181; lean_object* x_3182; 
lean_dec(x_2837);
lean_dec(x_2836);
lean_free_object(x_29);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3179 = lean_ctor_get(x_2838, 0);
lean_inc(x_3179);
x_3180 = lean_ctor_get(x_2838, 1);
lean_inc(x_3180);
if (lean_is_exclusive(x_2838)) {
 lean_ctor_release(x_2838, 0);
 lean_ctor_release(x_2838, 1);
 x_3181 = x_2838;
} else {
 lean_dec_ref(x_2838);
 x_3181 = lean_box(0);
}
if (lean_is_scalar(x_3181)) {
 x_3182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3182 = x_3181;
}
lean_ctor_set(x_3182, 0, x_3179);
lean_ctor_set(x_3182, 1, x_3180);
return x_3182;
}
}
}
else
{
lean_object* x_3183; lean_object* x_3184; lean_object* x_3185; lean_object* x_3186; lean_object* x_3187; lean_object* x_3188; 
x_3183 = lean_ctor_get(x_29, 0);
lean_inc(x_3183);
lean_dec(x_29);
x_3184 = lean_ctor_get(x_28, 1);
lean_inc(x_3184);
lean_dec(x_28);
x_3185 = lean_ctor_get(x_3183, 0);
lean_inc(x_3185);
x_3186 = lean_ctor_get(x_3183, 1);
lean_inc(x_3186);
if (lean_is_exclusive(x_3183)) {
 lean_ctor_release(x_3183, 0);
 lean_ctor_release(x_3183, 1);
 x_3187 = x_3183;
} else {
 lean_dec_ref(x_3183);
 x_3187 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_3188 = l_Lean_Meta_isTypeApp_x3f(x_26, x_3, x_4, x_5, x_6, x_3184);
if (lean_obj_tag(x_3188) == 0)
{
lean_object* x_3189; 
x_3189 = lean_ctor_get(x_3188, 0);
lean_inc(x_3189);
if (lean_obj_tag(x_3189) == 0)
{
lean_object* x_3190; lean_object* x_3191; lean_object* x_3192; lean_object* x_3193; 
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3190 = lean_ctor_get(x_3188, 1);
lean_inc(x_3190);
if (lean_is_exclusive(x_3188)) {
 lean_ctor_release(x_3188, 0);
 lean_ctor_release(x_3188, 1);
 x_3191 = x_3188;
} else {
 lean_dec_ref(x_3188);
 x_3191 = lean_box(0);
}
x_3192 = lean_box(0);
if (lean_is_scalar(x_3191)) {
 x_3193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3193 = x_3191;
}
lean_ctor_set(x_3193, 0, x_3192);
lean_ctor_set(x_3193, 1, x_3190);
return x_3193;
}
else
{
lean_object* x_3194; lean_object* x_3195; lean_object* x_3196; lean_object* x_3197; lean_object* x_3198; lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; 
x_3194 = lean_ctor_get(x_3189, 0);
lean_inc(x_3194);
if (lean_is_exclusive(x_3189)) {
 lean_ctor_release(x_3189, 0);
 x_3195 = x_3189;
} else {
 lean_dec_ref(x_3189);
 x_3195 = lean_box(0);
}
x_3196 = lean_ctor_get(x_3188, 1);
lean_inc(x_3196);
lean_dec(x_3188);
x_3197 = lean_ctor_get(x_3194, 0);
lean_inc(x_3197);
x_3198 = lean_ctor_get(x_3194, 1);
lean_inc(x_3198);
if (lean_is_exclusive(x_3194)) {
 lean_ctor_release(x_3194, 0);
 lean_ctor_release(x_3194, 1);
 x_3199 = x_3194;
} else {
 lean_dec_ref(x_3194);
 x_3199 = lean_box(0);
}
x_3200 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_3196);
x_3201 = lean_ctor_get(x_3200, 0);
lean_inc(x_3201);
x_3202 = lean_ctor_get(x_3200, 1);
lean_inc(x_3202);
if (lean_is_exclusive(x_3200)) {
 lean_ctor_release(x_3200, 0);
 lean_ctor_release(x_3200, 1);
 x_3203 = x_3200;
} else {
 lean_dec_ref(x_3200);
 x_3203 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3185);
lean_inc(x_3197);
x_3204 = l_Lean_Meta_isExprDefEq(x_3197, x_3185, x_3, x_4, x_5, x_6, x_3202);
if (lean_obj_tag(x_3204) == 0)
{
lean_object* x_3205; uint8_t x_3206; 
x_3205 = lean_ctor_get(x_3204, 0);
lean_inc(x_3205);
x_3206 = lean_unbox(x_3205);
lean_dec(x_3205);
if (x_3206 == 0)
{
lean_object* x_3207; lean_object* x_3208; lean_object* x_3209; lean_object* x_3210; uint8_t x_3211; 
lean_dec(x_3201);
x_3207 = lean_ctor_get(x_3204, 1);
lean_inc(x_3207);
if (lean_is_exclusive(x_3204)) {
 lean_ctor_release(x_3204, 0);
 lean_ctor_release(x_3204, 1);
 x_3208 = x_3204;
} else {
 lean_dec_ref(x_3204);
 x_3208 = lean_box(0);
}
x_3209 = lean_ctor_get(x_5, 2);
lean_inc(x_3209);
x_3210 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_3211 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_3209, x_3210);
lean_dec(x_3209);
if (x_3211 == 0)
{
lean_object* x_3212; lean_object* x_3213; 
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3212 = lean_box(0);
if (lean_is_scalar(x_3208)) {
 x_3213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3213 = x_3208;
}
lean_ctor_set(x_3213, 0, x_3212);
lean_ctor_set(x_3213, 1, x_3207);
return x_3213;
}
else
{
lean_object* x_3214; 
lean_dec(x_3208);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3197);
x_3214 = lean_infer_type(x_3197, x_3, x_4, x_5, x_6, x_3207);
if (lean_obj_tag(x_3214) == 0)
{
lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; 
x_3215 = lean_ctor_get(x_3214, 0);
lean_inc(x_3215);
x_3216 = lean_ctor_get(x_3214, 1);
lean_inc(x_3216);
lean_dec(x_3214);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3217 = lean_whnf(x_3215, x_3, x_4, x_5, x_6, x_3216);
if (lean_obj_tag(x_3217) == 0)
{
lean_object* x_3218; 
x_3218 = lean_ctor_get(x_3217, 0);
lean_inc(x_3218);
if (lean_obj_tag(x_3218) == 7)
{
lean_object* x_3219; 
x_3219 = lean_ctor_get(x_3218, 1);
lean_inc(x_3219);
if (lean_obj_tag(x_3219) == 3)
{
lean_object* x_3220; 
x_3220 = lean_ctor_get(x_3218, 2);
lean_inc(x_3220);
lean_dec(x_3218);
if (lean_obj_tag(x_3220) == 3)
{
lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; lean_object* x_3224; 
x_3221 = lean_ctor_get(x_3217, 1);
lean_inc(x_3221);
lean_dec(x_3217);
x_3222 = lean_ctor_get(x_3219, 0);
lean_inc(x_3222);
lean_dec(x_3219);
x_3223 = lean_ctor_get(x_3220, 0);
lean_inc(x_3223);
lean_dec(x_3220);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3185);
x_3224 = lean_infer_type(x_3185, x_3, x_4, x_5, x_6, x_3221);
if (lean_obj_tag(x_3224) == 0)
{
lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; 
x_3225 = lean_ctor_get(x_3224, 0);
lean_inc(x_3225);
x_3226 = lean_ctor_get(x_3224, 1);
lean_inc(x_3226);
lean_dec(x_3224);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3227 = lean_whnf(x_3225, x_3, x_4, x_5, x_6, x_3226);
if (lean_obj_tag(x_3227) == 0)
{
lean_object* x_3228; 
x_3228 = lean_ctor_get(x_3227, 0);
lean_inc(x_3228);
if (lean_obj_tag(x_3228) == 7)
{
lean_object* x_3229; 
x_3229 = lean_ctor_get(x_3228, 1);
lean_inc(x_3229);
if (lean_obj_tag(x_3229) == 3)
{
lean_object* x_3230; 
x_3230 = lean_ctor_get(x_3228, 2);
lean_inc(x_3230);
lean_dec(x_3228);
if (lean_obj_tag(x_3230) == 3)
{
lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; lean_object* x_3234; 
x_3231 = lean_ctor_get(x_3227, 1);
lean_inc(x_3231);
lean_dec(x_3227);
x_3232 = lean_ctor_get(x_3229, 0);
lean_inc(x_3232);
lean_dec(x_3229);
x_3233 = lean_ctor_get(x_3230, 0);
lean_inc(x_3233);
lean_dec(x_3230);
x_3234 = l_Lean_Meta_decLevel(x_3222, x_3, x_4, x_5, x_6, x_3231);
if (lean_obj_tag(x_3234) == 0)
{
lean_object* x_3235; lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; 
x_3235 = lean_ctor_get(x_3234, 0);
lean_inc(x_3235);
x_3236 = lean_ctor_get(x_3234, 1);
lean_inc(x_3236);
if (lean_is_exclusive(x_3234)) {
 lean_ctor_release(x_3234, 0);
 lean_ctor_release(x_3234, 1);
 x_3237 = x_3234;
} else {
 lean_dec_ref(x_3234);
 x_3237 = lean_box(0);
}
x_3238 = l_Lean_Meta_decLevel(x_3232, x_3, x_4, x_5, x_6, x_3236);
if (lean_obj_tag(x_3238) == 0)
{
lean_object* x_3239; lean_object* x_3240; lean_object* x_3241; uint8_t x_3242; lean_object* x_3243; 
x_3239 = lean_ctor_get(x_3238, 0);
lean_inc(x_3239);
x_3240 = lean_ctor_get(x_3238, 1);
lean_inc(x_3240);
if (lean_is_exclusive(x_3238)) {
 lean_ctor_release(x_3238, 0);
 lean_ctor_release(x_3238, 1);
 x_3241 = x_3238;
} else {
 lean_dec_ref(x_3238);
 x_3241 = lean_box(0);
}
x_3242 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3235);
x_3243 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_3235, x_3239, x_3242, x_3, x_4, x_5, x_6, x_3240);
if (lean_obj_tag(x_3243) == 0)
{
lean_object* x_3244; uint8_t x_3245; 
x_3244 = lean_ctor_get(x_3243, 0);
lean_inc(x_3244);
x_3245 = lean_unbox(x_3244);
lean_dec(x_3244);
if (x_3245 == 0)
{
lean_object* x_3246; lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; 
lean_dec(x_3241);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3233);
lean_dec(x_3223);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3246 = lean_ctor_get(x_3243, 1);
lean_inc(x_3246);
if (lean_is_exclusive(x_3243)) {
 lean_ctor_release(x_3243, 0);
 lean_ctor_release(x_3243, 1);
 x_3247 = x_3243;
} else {
 lean_dec_ref(x_3243);
 x_3247 = lean_box(0);
}
x_3248 = lean_box(0);
if (lean_is_scalar(x_3247)) {
 x_3249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3249 = x_3247;
}
lean_ctor_set(x_3249, 0, x_3248);
lean_ctor_set(x_3249, 1, x_3246);
return x_3249;
}
else
{
lean_object* x_3250; lean_object* x_3251; 
x_3250 = lean_ctor_get(x_3243, 1);
lean_inc(x_3250);
lean_dec(x_3243);
x_3251 = l_Lean_Meta_decLevel(x_3223, x_3, x_4, x_5, x_6, x_3250);
if (lean_obj_tag(x_3251) == 0)
{
lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; lean_object* x_3255; 
x_3252 = lean_ctor_get(x_3251, 0);
lean_inc(x_3252);
x_3253 = lean_ctor_get(x_3251, 1);
lean_inc(x_3253);
if (lean_is_exclusive(x_3251)) {
 lean_ctor_release(x_3251, 0);
 lean_ctor_release(x_3251, 1);
 x_3254 = x_3251;
} else {
 lean_dec_ref(x_3251);
 x_3254 = lean_box(0);
}
x_3255 = l_Lean_Meta_decLevel(x_3233, x_3, x_4, x_5, x_6, x_3253);
if (lean_obj_tag(x_3255) == 0)
{
lean_object* x_3256; lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; lean_object* x_3260; lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; lean_object* x_3266; lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; 
x_3256 = lean_ctor_get(x_3255, 0);
lean_inc(x_3256);
x_3257 = lean_ctor_get(x_3255, 1);
lean_inc(x_3257);
if (lean_is_exclusive(x_3255)) {
 lean_ctor_release(x_3255, 0);
 lean_ctor_release(x_3255, 1);
 x_3258 = x_3255;
} else {
 lean_dec_ref(x_3255);
 x_3258 = lean_box(0);
}
x_3259 = lean_box(0);
if (lean_is_scalar(x_3258)) {
 x_3260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3260 = x_3258;
 lean_ctor_set_tag(x_3260, 1);
}
lean_ctor_set(x_3260, 0, x_3256);
lean_ctor_set(x_3260, 1, x_3259);
if (lean_is_scalar(x_3254)) {
 x_3261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3261 = x_3254;
 lean_ctor_set_tag(x_3261, 1);
}
lean_ctor_set(x_3261, 0, x_3252);
lean_ctor_set(x_3261, 1, x_3260);
if (lean_is_scalar(x_3241)) {
 x_3262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3262 = x_3241;
 lean_ctor_set_tag(x_3262, 1);
}
lean_ctor_set(x_3262, 0, x_3235);
lean_ctor_set(x_3262, 1, x_3261);
x_3263 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_3264 = l_Lean_Expr_const___override(x_3263, x_3262);
lean_inc(x_3185);
if (lean_is_scalar(x_3237)) {
 x_3265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3265 = x_3237;
 lean_ctor_set_tag(x_3265, 1);
}
lean_ctor_set(x_3265, 0, x_3185);
lean_ctor_set(x_3265, 1, x_3259);
lean_inc(x_3197);
if (lean_is_scalar(x_3203)) {
 x_3266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3266 = x_3203;
 lean_ctor_set_tag(x_3266, 1);
}
lean_ctor_set(x_3266, 0, x_3197);
lean_ctor_set(x_3266, 1, x_3265);
x_3267 = lean_array_mk(x_3266);
x_3268 = l_Lean_mkAppN(x_3264, x_3267);
lean_dec(x_3267);
x_3269 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3270 = l_Lean_Meta_trySynthInstance(x_3268, x_3269, x_3, x_4, x_5, x_6, x_3257);
if (lean_obj_tag(x_3270) == 0)
{
lean_object* x_3271; 
x_3271 = lean_ctor_get(x_3270, 0);
lean_inc(x_3271);
if (lean_obj_tag(x_3271) == 1)
{
lean_object* x_3272; lean_object* x_3273; lean_object* x_3274; 
x_3272 = lean_ctor_get(x_3270, 1);
lean_inc(x_3272);
lean_dec(x_3270);
x_3273 = lean_ctor_get(x_3271, 0);
lean_inc(x_3273);
lean_dec(x_3271);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3198);
x_3274 = l_Lean_Meta_getDecLevel(x_3198, x_3, x_4, x_5, x_6, x_3272);
if (lean_obj_tag(x_3274) == 0)
{
lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3278 = l_Lean_Meta_getDecLevel(x_26, x_3, x_4, x_5, x_6, x_3276);
if (lean_obj_tag(x_3278) == 0)
{
lean_object* x_3279; lean_object* x_3280; lean_object* x_3281; lean_object* x_3282; 
x_3279 = lean_ctor_get(x_3278, 0);
lean_inc(x_3279);
x_3280 = lean_ctor_get(x_3278, 1);
lean_inc(x_3280);
if (lean_is_exclusive(x_3278)) {
 lean_ctor_release(x_3278, 0);
 lean_ctor_release(x_3278, 1);
 x_3281 = x_3278;
} else {
 lean_dec_ref(x_3278);
 x_3281 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_3282 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_3280);
if (lean_obj_tag(x_3282) == 0)
{
lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; lean_object* x_3287; lean_object* x_3288; lean_object* x_3289; lean_object* x_3290; lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; lean_object* x_3294; lean_object* x_3295; lean_object* x_3296; 
x_3283 = lean_ctor_get(x_3282, 0);
lean_inc(x_3283);
x_3284 = lean_ctor_get(x_3282, 1);
lean_inc(x_3284);
if (lean_is_exclusive(x_3282)) {
 lean_ctor_release(x_3282, 0);
 lean_ctor_release(x_3282, 1);
 x_3285 = x_3282;
} else {
 lean_dec_ref(x_3282);
 x_3285 = lean_box(0);
}
if (lean_is_scalar(x_3285)) {
 x_3286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3286 = x_3285;
 lean_ctor_set_tag(x_3286, 1);
}
lean_ctor_set(x_3286, 0, x_3283);
lean_ctor_set(x_3286, 1, x_3259);
if (lean_is_scalar(x_3281)) {
 x_3287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3287 = x_3281;
 lean_ctor_set_tag(x_3287, 1);
}
lean_ctor_set(x_3287, 0, x_3279);
lean_ctor_set(x_3287, 1, x_3286);
if (lean_is_scalar(x_3277)) {
 x_3288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3288 = x_3277;
 lean_ctor_set_tag(x_3288, 1);
}
lean_ctor_set(x_3288, 0, x_3275);
lean_ctor_set(x_3288, 1, x_3287);
x_3289 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_3288);
x_3290 = l_Lean_Expr_const___override(x_3289, x_3288);
if (lean_is_scalar(x_3199)) {
 x_3291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3291 = x_3199;
 lean_ctor_set_tag(x_3291, 1);
}
lean_ctor_set(x_3291, 0, x_1);
lean_ctor_set(x_3291, 1, x_3259);
lean_inc(x_3291);
lean_inc(x_3198);
if (lean_is_scalar(x_3187)) {
 x_3292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3292 = x_3187;
 lean_ctor_set_tag(x_3292, 1);
}
lean_ctor_set(x_3292, 0, x_3198);
lean_ctor_set(x_3292, 1, x_3291);
lean_inc(x_3273);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_3292);
lean_ctor_set(x_24, 0, x_3273);
lean_inc(x_3185);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_3185);
lean_inc(x_3197);
x_3293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3293, 0, x_3197);
lean_ctor_set(x_3293, 1, x_17);
x_3294 = lean_array_mk(x_3293);
x_3295 = l_Lean_mkAppN(x_3290, x_3294);
lean_dec(x_3294);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3295);
x_3296 = lean_infer_type(x_3295, x_3, x_4, x_5, x_6, x_3284);
if (lean_obj_tag(x_3296) == 0)
{
lean_object* x_3297; lean_object* x_3298; lean_object* x_3299; lean_object* x_3300; 
x_3297 = lean_ctor_get(x_3296, 0);
lean_inc(x_3297);
x_3298 = lean_ctor_get(x_3296, 1);
lean_inc(x_3298);
if (lean_is_exclusive(x_3296)) {
 lean_ctor_release(x_3296, 0);
 lean_ctor_release(x_3296, 1);
 x_3299 = x_3296;
} else {
 lean_dec_ref(x_3296);
 x_3299 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_3300 = l_Lean_Meta_isExprDefEq(x_19, x_3297, x_3, x_4, x_5, x_6, x_3298);
if (lean_obj_tag(x_3300) == 0)
{
lean_object* x_3301; uint8_t x_3302; 
x_3301 = lean_ctor_get(x_3300, 0);
lean_inc(x_3301);
x_3302 = lean_unbox(x_3301);
lean_dec(x_3301);
if (x_3302 == 0)
{
lean_object* x_3303; lean_object* x_3304; 
lean_dec(x_3295);
lean_dec(x_3195);
x_3303 = lean_ctor_get(x_3300, 1);
lean_inc(x_3303);
lean_dec(x_3300);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3185);
x_3304 = l_Lean_Meta_isMonad_x3f(x_3185, x_3, x_4, x_5, x_6, x_3303);
if (lean_obj_tag(x_3304) == 0)
{
lean_object* x_3305; 
x_3305 = lean_ctor_get(x_3304, 0);
lean_inc(x_3305);
if (lean_obj_tag(x_3305) == 0)
{
lean_object* x_3306; lean_object* x_3307; lean_object* x_3308; 
lean_dec(x_3299);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3306 = lean_ctor_get(x_3304, 1);
lean_inc(x_3306);
if (lean_is_exclusive(x_3304)) {
 lean_ctor_release(x_3304, 0);
 lean_ctor_release(x_3304, 1);
 x_3307 = x_3304;
} else {
 lean_dec_ref(x_3304);
 x_3307 = lean_box(0);
}
if (lean_is_scalar(x_3307)) {
 x_3308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3308 = x_3307;
}
lean_ctor_set(x_3308, 0, x_3269);
lean_ctor_set(x_3308, 1, x_3306);
return x_3308;
}
else
{
lean_object* x_3309; lean_object* x_3310; lean_object* x_3311; 
x_3309 = lean_ctor_get(x_3304, 1);
lean_inc(x_3309);
lean_dec(x_3304);
x_3310 = lean_ctor_get(x_3305, 0);
lean_inc(x_3310);
lean_dec(x_3305);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3198);
x_3311 = l_Lean_Meta_getLevel(x_3198, x_3, x_4, x_5, x_6, x_3309);
if (lean_obj_tag(x_3311) == 0)
{
lean_object* x_3312; lean_object* x_3313; lean_object* x_3314; lean_object* x_3315; 
x_3312 = lean_ctor_get(x_3311, 0);
lean_inc(x_3312);
x_3313 = lean_ctor_get(x_3311, 1);
lean_inc(x_3313);
if (lean_is_exclusive(x_3311)) {
 lean_ctor_release(x_3311, 0);
 lean_ctor_release(x_3311, 1);
 x_3314 = x_3311;
} else {
 lean_dec_ref(x_3311);
 x_3314 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3186);
x_3315 = l_Lean_Meta_getLevel(x_3186, x_3, x_4, x_5, x_6, x_3313);
if (lean_obj_tag(x_3315) == 0)
{
lean_object* x_3316; lean_object* x_3317; lean_object* x_3318; lean_object* x_3319; lean_object* x_3320; lean_object* x_3321; lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; lean_object* x_3329; uint8_t x_3330; lean_object* x_3331; lean_object* x_3332; 
x_3316 = lean_ctor_get(x_3315, 0);
lean_inc(x_3316);
x_3317 = lean_ctor_get(x_3315, 1);
lean_inc(x_3317);
if (lean_is_exclusive(x_3315)) {
 lean_ctor_release(x_3315, 0);
 lean_ctor_release(x_3315, 1);
 x_3318 = x_3315;
} else {
 lean_dec_ref(x_3315);
 x_3318 = lean_box(0);
}
if (lean_is_scalar(x_3318)) {
 x_3319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3319 = x_3318;
 lean_ctor_set_tag(x_3319, 1);
}
lean_ctor_set(x_3319, 0, x_3316);
lean_ctor_set(x_3319, 1, x_3259);
if (lean_is_scalar(x_3314)) {
 x_3320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3320 = x_3314;
 lean_ctor_set_tag(x_3320, 1);
}
lean_ctor_set(x_3320, 0, x_3312);
lean_ctor_set(x_3320, 1, x_3319);
x_3321 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_3322 = l_Lean_Expr_const___override(x_3321, x_3320);
lean_inc(x_3186);
if (lean_is_scalar(x_3299)) {
 x_3323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3323 = x_3299;
 lean_ctor_set_tag(x_3323, 1);
}
lean_ctor_set(x_3323, 0, x_3186);
lean_ctor_set(x_3323, 1, x_3259);
x_3324 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_3325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3325, 0, x_3324);
lean_ctor_set(x_3325, 1, x_3323);
lean_inc(x_3198);
x_3326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3326, 0, x_3198);
lean_ctor_set(x_3326, 1, x_3325);
x_3327 = lean_array_mk(x_3326);
x_3328 = l_Lean_mkAppN(x_3322, x_3327);
lean_dec(x_3327);
x_3329 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_3330 = 0;
lean_inc(x_3198);
x_3331 = l_Lean_Expr_forallE___override(x_3329, x_3198, x_3328, x_3330);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3332 = l_Lean_Meta_trySynthInstance(x_3331, x_3269, x_3, x_4, x_5, x_6, x_3317);
if (lean_obj_tag(x_3332) == 0)
{
lean_object* x_3333; 
x_3333 = lean_ctor_get(x_3332, 0);
lean_inc(x_3333);
if (lean_obj_tag(x_3333) == 1)
{
lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; lean_object* x_3346; lean_object* x_3347; 
x_3334 = lean_ctor_get(x_3332, 1);
lean_inc(x_3334);
lean_dec(x_3332);
x_3335 = lean_ctor_get(x_3333, 0);
lean_inc(x_3335);
lean_dec(x_3333);
x_3336 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_3337 = l_Lean_Expr_const___override(x_3336, x_3288);
x_3338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3338, 0, x_3310);
lean_ctor_set(x_3338, 1, x_3291);
x_3339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3339, 0, x_3335);
lean_ctor_set(x_3339, 1, x_3338);
x_3340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3340, 0, x_3273);
lean_ctor_set(x_3340, 1, x_3339);
x_3341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3341, 0, x_3186);
lean_ctor_set(x_3341, 1, x_3340);
x_3342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3342, 0, x_3198);
lean_ctor_set(x_3342, 1, x_3341);
x_3343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3343, 0, x_3185);
lean_ctor_set(x_3343, 1, x_3342);
x_3344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3344, 0, x_3197);
lean_ctor_set(x_3344, 1, x_3343);
x_3345 = lean_array_mk(x_3344);
x_3346 = l_Lean_mkAppN(x_3337, x_3345);
lean_dec(x_3345);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3347 = l_Lean_Meta_expandCoe(x_3346, x_3, x_4, x_5, x_6, x_3334);
if (lean_obj_tag(x_3347) == 0)
{
lean_object* x_3348; lean_object* x_3349; lean_object* x_3350; 
x_3348 = lean_ctor_get(x_3347, 0);
lean_inc(x_3348);
x_3349 = lean_ctor_get(x_3347, 1);
lean_inc(x_3349);
lean_dec(x_3347);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3348);
x_3350 = lean_infer_type(x_3348, x_3, x_4, x_5, x_6, x_3349);
if (lean_obj_tag(x_3350) == 0)
{
lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; 
x_3351 = lean_ctor_get(x_3350, 0);
lean_inc(x_3351);
x_3352 = lean_ctor_get(x_3350, 1);
lean_inc(x_3352);
lean_dec(x_3350);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3353 = l_Lean_Meta_isExprDefEq(x_19, x_3351, x_3, x_4, x_5, x_6, x_3352);
if (lean_obj_tag(x_3353) == 0)
{
lean_object* x_3354; uint8_t x_3355; 
x_3354 = lean_ctor_get(x_3353, 0);
lean_inc(x_3354);
x_3355 = lean_unbox(x_3354);
lean_dec(x_3354);
if (x_3355 == 0)
{
lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; 
lean_dec(x_3348);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3356 = lean_ctor_get(x_3353, 1);
lean_inc(x_3356);
if (lean_is_exclusive(x_3353)) {
 lean_ctor_release(x_3353, 0);
 lean_ctor_release(x_3353, 1);
 x_3357 = x_3353;
} else {
 lean_dec_ref(x_3353);
 x_3357 = lean_box(0);
}
if (lean_is_scalar(x_3357)) {
 x_3358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3358 = x_3357;
}
lean_ctor_set(x_3358, 0, x_3269);
lean_ctor_set(x_3358, 1, x_3356);
return x_3358;
}
else
{
lean_object* x_3359; lean_object* x_3360; lean_object* x_3361; lean_object* x_3362; lean_object* x_3363; lean_object* x_3364; lean_object* x_3365; 
x_3359 = lean_ctor_get(x_3353, 1);
lean_inc(x_3359);
lean_dec(x_3353);
x_3360 = lean_box(0);
x_3361 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_3348, x_3360, x_3, x_4, x_5, x_6, x_3359);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3362 = lean_ctor_get(x_3361, 0);
lean_inc(x_3362);
x_3363 = lean_ctor_get(x_3361, 1);
lean_inc(x_3363);
if (lean_is_exclusive(x_3361)) {
 lean_ctor_release(x_3361, 0);
 lean_ctor_release(x_3361, 1);
 x_3364 = x_3361;
} else {
 lean_dec_ref(x_3361);
 x_3364 = lean_box(0);
}
if (lean_is_scalar(x_3364)) {
 x_3365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3365 = x_3364;
}
lean_ctor_set(x_3365, 0, x_3362);
lean_ctor_set(x_3365, 1, x_3363);
return x_3365;
}
}
else
{
lean_object* x_3366; lean_object* x_3367; 
lean_dec(x_3348);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3366 = lean_ctor_get(x_3353, 0);
lean_inc(x_3366);
x_3367 = lean_ctor_get(x_3353, 1);
lean_inc(x_3367);
lean_dec(x_3353);
x_8 = x_3366;
x_9 = x_3367;
goto block_16;
}
}
else
{
lean_object* x_3368; lean_object* x_3369; 
lean_dec(x_3348);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3368 = lean_ctor_get(x_3350, 0);
lean_inc(x_3368);
x_3369 = lean_ctor_get(x_3350, 1);
lean_inc(x_3369);
lean_dec(x_3350);
x_8 = x_3368;
x_9 = x_3369;
goto block_16;
}
}
else
{
lean_object* x_3370; lean_object* x_3371; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3370 = lean_ctor_get(x_3347, 0);
lean_inc(x_3370);
x_3371 = lean_ctor_get(x_3347, 1);
lean_inc(x_3371);
lean_dec(x_3347);
x_8 = x_3370;
x_9 = x_3371;
goto block_16;
}
}
else
{
lean_object* x_3372; lean_object* x_3373; lean_object* x_3374; 
lean_dec(x_3333);
lean_dec(x_3310);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3372 = lean_ctor_get(x_3332, 1);
lean_inc(x_3372);
if (lean_is_exclusive(x_3332)) {
 lean_ctor_release(x_3332, 0);
 lean_ctor_release(x_3332, 1);
 x_3373 = x_3332;
} else {
 lean_dec_ref(x_3332);
 x_3373 = lean_box(0);
}
if (lean_is_scalar(x_3373)) {
 x_3374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3374 = x_3373;
}
lean_ctor_set(x_3374, 0, x_3269);
lean_ctor_set(x_3374, 1, x_3372);
return x_3374;
}
}
else
{
lean_object* x_3375; lean_object* x_3376; 
lean_dec(x_3310);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3375 = lean_ctor_get(x_3332, 0);
lean_inc(x_3375);
x_3376 = lean_ctor_get(x_3332, 1);
lean_inc(x_3376);
lean_dec(x_3332);
x_8 = x_3375;
x_9 = x_3376;
goto block_16;
}
}
else
{
lean_object* x_3377; lean_object* x_3378; 
lean_dec(x_3314);
lean_dec(x_3312);
lean_dec(x_3310);
lean_dec(x_3299);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3377 = lean_ctor_get(x_3315, 0);
lean_inc(x_3377);
x_3378 = lean_ctor_get(x_3315, 1);
lean_inc(x_3378);
lean_dec(x_3315);
x_8 = x_3377;
x_9 = x_3378;
goto block_16;
}
}
else
{
lean_object* x_3379; lean_object* x_3380; 
lean_dec(x_3310);
lean_dec(x_3299);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3379 = lean_ctor_get(x_3311, 0);
lean_inc(x_3379);
x_3380 = lean_ctor_get(x_3311, 1);
lean_inc(x_3380);
lean_dec(x_3311);
x_8 = x_3379;
x_9 = x_3380;
goto block_16;
}
}
}
else
{
lean_object* x_3381; lean_object* x_3382; 
lean_dec(x_3299);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3381 = lean_ctor_get(x_3304, 0);
lean_inc(x_3381);
x_3382 = lean_ctor_get(x_3304, 1);
lean_inc(x_3382);
lean_dec(x_3304);
x_8 = x_3381;
x_9 = x_3382;
goto block_16;
}
}
else
{
lean_object* x_3383; lean_object* x_3384; lean_object* x_3385; lean_object* x_3386; 
lean_dec(x_3299);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3383 = lean_ctor_get(x_3300, 1);
lean_inc(x_3383);
if (lean_is_exclusive(x_3300)) {
 lean_ctor_release(x_3300, 0);
 lean_ctor_release(x_3300, 1);
 x_3384 = x_3300;
} else {
 lean_dec_ref(x_3300);
 x_3384 = lean_box(0);
}
if (lean_is_scalar(x_3195)) {
 x_3385 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3385 = x_3195;
}
lean_ctor_set(x_3385, 0, x_3295);
if (lean_is_scalar(x_3384)) {
 x_3386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3386 = x_3384;
}
lean_ctor_set(x_3386, 0, x_3385);
lean_ctor_set(x_3386, 1, x_3383);
return x_3386;
}
}
else
{
lean_object* x_3387; lean_object* x_3388; 
lean_dec(x_3299);
lean_dec(x_3295);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3387 = lean_ctor_get(x_3300, 0);
lean_inc(x_3387);
x_3388 = lean_ctor_get(x_3300, 1);
lean_inc(x_3388);
lean_dec(x_3300);
x_8 = x_3387;
x_9 = x_3388;
goto block_16;
}
}
else
{
lean_object* x_3389; lean_object* x_3390; 
lean_dec(x_3295);
lean_dec(x_3291);
lean_dec(x_3288);
lean_dec(x_3273);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3186);
lean_dec(x_3185);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3389 = lean_ctor_get(x_3296, 0);
lean_inc(x_3389);
x_3390 = lean_ctor_get(x_3296, 1);
lean_inc(x_3390);
lean_dec(x_3296);
x_8 = x_3389;
x_9 = x_3390;
goto block_16;
}
}
else
{
lean_object* x_3391; lean_object* x_3392; 
lean_dec(x_3281);
lean_dec(x_3279);
lean_dec(x_3277);
lean_dec(x_3275);
lean_dec(x_3273);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3391 = lean_ctor_get(x_3282, 0);
lean_inc(x_3391);
x_3392 = lean_ctor_get(x_3282, 1);
lean_inc(x_3392);
lean_dec(x_3282);
x_8 = x_3391;
x_9 = x_3392;
goto block_16;
}
}
else
{
lean_object* x_3393; lean_object* x_3394; 
lean_dec(x_3277);
lean_dec(x_3275);
lean_dec(x_3273);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3393 = lean_ctor_get(x_3278, 0);
lean_inc(x_3393);
x_3394 = lean_ctor_get(x_3278, 1);
lean_inc(x_3394);
lean_dec(x_3278);
x_8 = x_3393;
x_9 = x_3394;
goto block_16;
}
}
else
{
lean_object* x_3395; lean_object* x_3396; 
lean_dec(x_3273);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3395 = lean_ctor_get(x_3274, 0);
lean_inc(x_3395);
x_3396 = lean_ctor_get(x_3274, 1);
lean_inc(x_3396);
lean_dec(x_3274);
x_8 = x_3395;
x_9 = x_3396;
goto block_16;
}
}
else
{
lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; 
lean_dec(x_3271);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3397 = lean_ctor_get(x_3270, 1);
lean_inc(x_3397);
if (lean_is_exclusive(x_3270)) {
 lean_ctor_release(x_3270, 0);
 lean_ctor_release(x_3270, 1);
 x_3398 = x_3270;
} else {
 lean_dec_ref(x_3270);
 x_3398 = lean_box(0);
}
if (lean_is_scalar(x_3398)) {
 x_3399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3399 = x_3398;
}
lean_ctor_set(x_3399, 0, x_3269);
lean_ctor_set(x_3399, 1, x_3397);
return x_3399;
}
}
else
{
lean_object* x_3400; lean_object* x_3401; 
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3400 = lean_ctor_get(x_3270, 0);
lean_inc(x_3400);
x_3401 = lean_ctor_get(x_3270, 1);
lean_inc(x_3401);
lean_dec(x_3270);
x_8 = x_3400;
x_9 = x_3401;
goto block_16;
}
}
else
{
lean_object* x_3402; lean_object* x_3403; 
lean_dec(x_3254);
lean_dec(x_3252);
lean_dec(x_3241);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3402 = lean_ctor_get(x_3255, 0);
lean_inc(x_3402);
x_3403 = lean_ctor_get(x_3255, 1);
lean_inc(x_3403);
lean_dec(x_3255);
x_8 = x_3402;
x_9 = x_3403;
goto block_16;
}
}
else
{
lean_object* x_3404; lean_object* x_3405; 
lean_dec(x_3241);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3233);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3404 = lean_ctor_get(x_3251, 0);
lean_inc(x_3404);
x_3405 = lean_ctor_get(x_3251, 1);
lean_inc(x_3405);
lean_dec(x_3251);
x_8 = x_3404;
x_9 = x_3405;
goto block_16;
}
}
}
else
{
lean_object* x_3406; lean_object* x_3407; 
lean_dec(x_3241);
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3233);
lean_dec(x_3223);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3406 = lean_ctor_get(x_3243, 0);
lean_inc(x_3406);
x_3407 = lean_ctor_get(x_3243, 1);
lean_inc(x_3407);
lean_dec(x_3243);
x_8 = x_3406;
x_9 = x_3407;
goto block_16;
}
}
else
{
lean_object* x_3408; lean_object* x_3409; 
lean_dec(x_3237);
lean_dec(x_3235);
lean_dec(x_3233);
lean_dec(x_3223);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3408 = lean_ctor_get(x_3238, 0);
lean_inc(x_3408);
x_3409 = lean_ctor_get(x_3238, 1);
lean_inc(x_3409);
lean_dec(x_3238);
x_8 = x_3408;
x_9 = x_3409;
goto block_16;
}
}
else
{
lean_object* x_3410; lean_object* x_3411; 
lean_dec(x_3233);
lean_dec(x_3232);
lean_dec(x_3223);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3410 = lean_ctor_get(x_3234, 0);
lean_inc(x_3410);
x_3411 = lean_ctor_get(x_3234, 1);
lean_inc(x_3411);
lean_dec(x_3234);
x_8 = x_3410;
x_9 = x_3411;
goto block_16;
}
}
else
{
lean_object* x_3412; lean_object* x_3413; lean_object* x_3414; lean_object* x_3415; 
lean_dec(x_3230);
lean_dec(x_3229);
lean_dec(x_3223);
lean_dec(x_3222);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3412 = lean_ctor_get(x_3227, 1);
lean_inc(x_3412);
if (lean_is_exclusive(x_3227)) {
 lean_ctor_release(x_3227, 0);
 lean_ctor_release(x_3227, 1);
 x_3413 = x_3227;
} else {
 lean_dec_ref(x_3227);
 x_3413 = lean_box(0);
}
x_3414 = lean_box(0);
if (lean_is_scalar(x_3413)) {
 x_3415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3415 = x_3413;
}
lean_ctor_set(x_3415, 0, x_3414);
lean_ctor_set(x_3415, 1, x_3412);
return x_3415;
}
}
else
{
lean_object* x_3416; lean_object* x_3417; lean_object* x_3418; lean_object* x_3419; 
lean_dec(x_3229);
lean_dec(x_3228);
lean_dec(x_3223);
lean_dec(x_3222);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3416 = lean_ctor_get(x_3227, 1);
lean_inc(x_3416);
if (lean_is_exclusive(x_3227)) {
 lean_ctor_release(x_3227, 0);
 lean_ctor_release(x_3227, 1);
 x_3417 = x_3227;
} else {
 lean_dec_ref(x_3227);
 x_3417 = lean_box(0);
}
x_3418 = lean_box(0);
if (lean_is_scalar(x_3417)) {
 x_3419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3419 = x_3417;
}
lean_ctor_set(x_3419, 0, x_3418);
lean_ctor_set(x_3419, 1, x_3416);
return x_3419;
}
}
else
{
lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; 
lean_dec(x_3228);
lean_dec(x_3223);
lean_dec(x_3222);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3420 = lean_ctor_get(x_3227, 1);
lean_inc(x_3420);
if (lean_is_exclusive(x_3227)) {
 lean_ctor_release(x_3227, 0);
 lean_ctor_release(x_3227, 1);
 x_3421 = x_3227;
} else {
 lean_dec_ref(x_3227);
 x_3421 = lean_box(0);
}
x_3422 = lean_box(0);
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
lean_object* x_3424; lean_object* x_3425; lean_object* x_3426; uint8_t x_3427; 
lean_dec(x_3223);
lean_dec(x_3222);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3424 = lean_ctor_get(x_3227, 0);
lean_inc(x_3424);
x_3425 = lean_ctor_get(x_3227, 1);
lean_inc(x_3425);
if (lean_is_exclusive(x_3227)) {
 lean_ctor_release(x_3227, 0);
 lean_ctor_release(x_3227, 1);
 x_3426 = x_3227;
} else {
 lean_dec_ref(x_3227);
 x_3426 = lean_box(0);
}
x_3427 = l_Lean_Exception_isInterrupt(x_3424);
if (x_3427 == 0)
{
uint8_t x_3428; 
x_3428 = l_Lean_Exception_isRuntime(x_3424);
if (x_3428 == 0)
{
lean_object* x_3429; lean_object* x_3430; 
lean_dec(x_3424);
x_3429 = lean_box(0);
if (lean_is_scalar(x_3426)) {
 x_3430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3430 = x_3426;
 lean_ctor_set_tag(x_3430, 0);
}
lean_ctor_set(x_3430, 0, x_3429);
lean_ctor_set(x_3430, 1, x_3425);
return x_3430;
}
else
{
lean_object* x_3431; 
if (lean_is_scalar(x_3426)) {
 x_3431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3431 = x_3426;
}
lean_ctor_set(x_3431, 0, x_3424);
lean_ctor_set(x_3431, 1, x_3425);
return x_3431;
}
}
else
{
lean_object* x_3432; 
if (lean_is_scalar(x_3426)) {
 x_3432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3432 = x_3426;
}
lean_ctor_set(x_3432, 0, x_3424);
lean_ctor_set(x_3432, 1, x_3425);
return x_3432;
}
}
}
else
{
lean_object* x_3433; lean_object* x_3434; lean_object* x_3435; uint8_t x_3436; 
lean_dec(x_3223);
lean_dec(x_3222);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3433 = lean_ctor_get(x_3224, 0);
lean_inc(x_3433);
x_3434 = lean_ctor_get(x_3224, 1);
lean_inc(x_3434);
if (lean_is_exclusive(x_3224)) {
 lean_ctor_release(x_3224, 0);
 lean_ctor_release(x_3224, 1);
 x_3435 = x_3224;
} else {
 lean_dec_ref(x_3224);
 x_3435 = lean_box(0);
}
x_3436 = l_Lean_Exception_isInterrupt(x_3433);
if (x_3436 == 0)
{
uint8_t x_3437; 
x_3437 = l_Lean_Exception_isRuntime(x_3433);
if (x_3437 == 0)
{
lean_object* x_3438; lean_object* x_3439; 
lean_dec(x_3433);
x_3438 = lean_box(0);
if (lean_is_scalar(x_3435)) {
 x_3439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3439 = x_3435;
 lean_ctor_set_tag(x_3439, 0);
}
lean_ctor_set(x_3439, 0, x_3438);
lean_ctor_set(x_3439, 1, x_3434);
return x_3439;
}
else
{
lean_object* x_3440; 
if (lean_is_scalar(x_3435)) {
 x_3440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3440 = x_3435;
}
lean_ctor_set(x_3440, 0, x_3433);
lean_ctor_set(x_3440, 1, x_3434);
return x_3440;
}
}
else
{
lean_object* x_3441; 
if (lean_is_scalar(x_3435)) {
 x_3441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3441 = x_3435;
}
lean_ctor_set(x_3441, 0, x_3433);
lean_ctor_set(x_3441, 1, x_3434);
return x_3441;
}
}
}
else
{
lean_object* x_3442; lean_object* x_3443; lean_object* x_3444; lean_object* x_3445; 
lean_dec(x_3220);
lean_dec(x_3219);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3442 = lean_ctor_get(x_3217, 1);
lean_inc(x_3442);
if (lean_is_exclusive(x_3217)) {
 lean_ctor_release(x_3217, 0);
 lean_ctor_release(x_3217, 1);
 x_3443 = x_3217;
} else {
 lean_dec_ref(x_3217);
 x_3443 = lean_box(0);
}
x_3444 = lean_box(0);
if (lean_is_scalar(x_3443)) {
 x_3445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3445 = x_3443;
}
lean_ctor_set(x_3445, 0, x_3444);
lean_ctor_set(x_3445, 1, x_3442);
return x_3445;
}
}
else
{
lean_object* x_3446; lean_object* x_3447; lean_object* x_3448; lean_object* x_3449; 
lean_dec(x_3219);
lean_dec(x_3218);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3446 = lean_ctor_get(x_3217, 1);
lean_inc(x_3446);
if (lean_is_exclusive(x_3217)) {
 lean_ctor_release(x_3217, 0);
 lean_ctor_release(x_3217, 1);
 x_3447 = x_3217;
} else {
 lean_dec_ref(x_3217);
 x_3447 = lean_box(0);
}
x_3448 = lean_box(0);
if (lean_is_scalar(x_3447)) {
 x_3449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3449 = x_3447;
}
lean_ctor_set(x_3449, 0, x_3448);
lean_ctor_set(x_3449, 1, x_3446);
return x_3449;
}
}
else
{
lean_object* x_3450; lean_object* x_3451; lean_object* x_3452; lean_object* x_3453; 
lean_dec(x_3218);
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3450 = lean_ctor_get(x_3217, 1);
lean_inc(x_3450);
if (lean_is_exclusive(x_3217)) {
 lean_ctor_release(x_3217, 0);
 lean_ctor_release(x_3217, 1);
 x_3451 = x_3217;
} else {
 lean_dec_ref(x_3217);
 x_3451 = lean_box(0);
}
x_3452 = lean_box(0);
if (lean_is_scalar(x_3451)) {
 x_3453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3453 = x_3451;
}
lean_ctor_set(x_3453, 0, x_3452);
lean_ctor_set(x_3453, 1, x_3450);
return x_3453;
}
}
else
{
lean_object* x_3454; lean_object* x_3455; lean_object* x_3456; uint8_t x_3457; 
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3454 = lean_ctor_get(x_3217, 0);
lean_inc(x_3454);
x_3455 = lean_ctor_get(x_3217, 1);
lean_inc(x_3455);
if (lean_is_exclusive(x_3217)) {
 lean_ctor_release(x_3217, 0);
 lean_ctor_release(x_3217, 1);
 x_3456 = x_3217;
} else {
 lean_dec_ref(x_3217);
 x_3456 = lean_box(0);
}
x_3457 = l_Lean_Exception_isInterrupt(x_3454);
if (x_3457 == 0)
{
uint8_t x_3458; 
x_3458 = l_Lean_Exception_isRuntime(x_3454);
if (x_3458 == 0)
{
lean_object* x_3459; lean_object* x_3460; 
lean_dec(x_3454);
x_3459 = lean_box(0);
if (lean_is_scalar(x_3456)) {
 x_3460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3460 = x_3456;
 lean_ctor_set_tag(x_3460, 0);
}
lean_ctor_set(x_3460, 0, x_3459);
lean_ctor_set(x_3460, 1, x_3455);
return x_3460;
}
else
{
lean_object* x_3461; 
if (lean_is_scalar(x_3456)) {
 x_3461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3461 = x_3456;
}
lean_ctor_set(x_3461, 0, x_3454);
lean_ctor_set(x_3461, 1, x_3455);
return x_3461;
}
}
else
{
lean_object* x_3462; 
if (lean_is_scalar(x_3456)) {
 x_3462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3462 = x_3456;
}
lean_ctor_set(x_3462, 0, x_3454);
lean_ctor_set(x_3462, 1, x_3455);
return x_3462;
}
}
}
else
{
lean_object* x_3463; lean_object* x_3464; lean_object* x_3465; uint8_t x_3466; 
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3463 = lean_ctor_get(x_3214, 0);
lean_inc(x_3463);
x_3464 = lean_ctor_get(x_3214, 1);
lean_inc(x_3464);
if (lean_is_exclusive(x_3214)) {
 lean_ctor_release(x_3214, 0);
 lean_ctor_release(x_3214, 1);
 x_3465 = x_3214;
} else {
 lean_dec_ref(x_3214);
 x_3465 = lean_box(0);
}
x_3466 = l_Lean_Exception_isInterrupt(x_3463);
if (x_3466 == 0)
{
uint8_t x_3467; 
x_3467 = l_Lean_Exception_isRuntime(x_3463);
if (x_3467 == 0)
{
lean_object* x_3468; lean_object* x_3469; 
lean_dec(x_3463);
x_3468 = lean_box(0);
if (lean_is_scalar(x_3465)) {
 x_3469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3469 = x_3465;
 lean_ctor_set_tag(x_3469, 0);
}
lean_ctor_set(x_3469, 0, x_3468);
lean_ctor_set(x_3469, 1, x_3464);
return x_3469;
}
else
{
lean_object* x_3470; 
if (lean_is_scalar(x_3465)) {
 x_3470 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3470 = x_3465;
}
lean_ctor_set(x_3470, 0, x_3463);
lean_ctor_set(x_3470, 1, x_3464);
return x_3470;
}
}
else
{
lean_object* x_3471; 
if (lean_is_scalar(x_3465)) {
 x_3471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3471 = x_3465;
}
lean_ctor_set(x_3471, 0, x_3463);
lean_ctor_set(x_3471, 1, x_3464);
return x_3471;
}
}
}
}
else
{
lean_object* x_3472; lean_object* x_3473; 
lean_dec(x_26);
lean_dec(x_19);
x_3472 = lean_ctor_get(x_3204, 1);
lean_inc(x_3472);
lean_dec(x_3204);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3473 = l_Lean_Meta_isMonad_x3f(x_3185, x_3, x_4, x_5, x_6, x_3472);
if (lean_obj_tag(x_3473) == 0)
{
lean_object* x_3474; 
x_3474 = lean_ctor_get(x_3473, 0);
lean_inc(x_3474);
if (lean_obj_tag(x_3474) == 0)
{
lean_object* x_3475; lean_object* x_3476; lean_object* x_3477; lean_object* x_3478; lean_object* x_3479; lean_object* x_3480; 
lean_dec(x_3203);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_1);
x_3475 = lean_ctor_get(x_3473, 1);
lean_inc(x_3475);
lean_dec(x_3473);
x_3476 = l_Lean_Meta_SavedState_restore(x_3201, x_3, x_4, x_5, x_6, x_3475);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_3201);
x_3477 = lean_ctor_get(x_3476, 1);
lean_inc(x_3477);
if (lean_is_exclusive(x_3476)) {
 lean_ctor_release(x_3476, 0);
 lean_ctor_release(x_3476, 1);
 x_3478 = x_3476;
} else {
 lean_dec_ref(x_3476);
 x_3478 = lean_box(0);
}
x_3479 = lean_box(0);
if (lean_is_scalar(x_3478)) {
 x_3480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3480 = x_3478;
}
lean_ctor_set(x_3480, 0, x_3479);
lean_ctor_set(x_3480, 1, x_3477);
return x_3480;
}
else
{
lean_object* x_3481; lean_object* x_3482; lean_object* x_3483; lean_object* x_3484; lean_object* x_3485; lean_object* x_3486; lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; lean_object* x_3490; lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; lean_object* x_3494; lean_object* x_3495; lean_object* x_3496; lean_object* x_3497; lean_object* x_3498; lean_object* x_3508; lean_object* x_3509; 
x_3481 = lean_ctor_get(x_3473, 1);
lean_inc(x_3481);
if (lean_is_exclusive(x_3473)) {
 lean_ctor_release(x_3473, 0);
 lean_ctor_release(x_3473, 1);
 x_3482 = x_3473;
} else {
 lean_dec_ref(x_3473);
 x_3482 = lean_box(0);
}
x_3483 = lean_ctor_get(x_3474, 0);
lean_inc(x_3483);
if (lean_is_exclusive(x_3474)) {
 lean_ctor_release(x_3474, 0);
 x_3484 = x_3474;
} else {
 lean_dec_ref(x_3474);
 x_3484 = lean_box(0);
}
if (lean_is_scalar(x_3484)) {
 x_3485 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3485 = x_3484;
}
lean_ctor_set(x_3485, 0, x_3197);
if (lean_is_scalar(x_3195)) {
 x_3486 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3486 = x_3195;
}
lean_ctor_set(x_3486, 0, x_3198);
x_3487 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3487, 0, x_3186);
x_3488 = lean_box(0);
x_3489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3489, 0, x_3483);
x_3490 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3490, 0, x_1);
x_3491 = lean_box(0);
if (lean_is_scalar(x_3203)) {
 x_3492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3492 = x_3203;
 lean_ctor_set_tag(x_3492, 1);
}
lean_ctor_set(x_3492, 0, x_3490);
lean_ctor_set(x_3492, 1, x_3491);
if (lean_is_scalar(x_3199)) {
 x_3493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3493 = x_3199;
 lean_ctor_set_tag(x_3493, 1);
}
lean_ctor_set(x_3493, 0, x_3489);
lean_ctor_set(x_3493, 1, x_3492);
if (lean_is_scalar(x_3187)) {
 x_3494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3494 = x_3187;
 lean_ctor_set_tag(x_3494, 1);
}
lean_ctor_set(x_3494, 0, x_3488);
lean_ctor_set(x_3494, 1, x_3493);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_3494);
lean_ctor_set(x_24, 0, x_3487);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_3486);
x_3495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3495, 0, x_3485);
lean_ctor_set(x_3495, 1, x_17);
x_3496 = lean_array_mk(x_3495);
x_3508 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3509 = l_Lean_Meta_mkAppOptM(x_3508, x_3496, x_3, x_4, x_5, x_6, x_3481);
if (lean_obj_tag(x_3509) == 0)
{
lean_object* x_3510; lean_object* x_3511; lean_object* x_3512; 
x_3510 = lean_ctor_get(x_3509, 0);
lean_inc(x_3510);
x_3511 = lean_ctor_get(x_3509, 1);
lean_inc(x_3511);
lean_dec(x_3509);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3512 = l_Lean_Meta_expandCoe(x_3510, x_3, x_4, x_5, x_6, x_3511);
if (lean_obj_tag(x_3512) == 0)
{
lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; lean_object* x_3516; lean_object* x_3517; 
lean_dec(x_3482);
lean_dec(x_3201);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3513 = lean_ctor_get(x_3512, 0);
lean_inc(x_3513);
x_3514 = lean_ctor_get(x_3512, 1);
lean_inc(x_3514);
if (lean_is_exclusive(x_3512)) {
 lean_ctor_release(x_3512, 0);
 lean_ctor_release(x_3512, 1);
 x_3515 = x_3512;
} else {
 lean_dec_ref(x_3512);
 x_3515 = lean_box(0);
}
x_3516 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3516, 0, x_3513);
if (lean_is_scalar(x_3515)) {
 x_3517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3517 = x_3515;
}
lean_ctor_set(x_3517, 0, x_3516);
lean_ctor_set(x_3517, 1, x_3514);
return x_3517;
}
else
{
lean_object* x_3518; lean_object* x_3519; 
x_3518 = lean_ctor_get(x_3512, 0);
lean_inc(x_3518);
x_3519 = lean_ctor_get(x_3512, 1);
lean_inc(x_3519);
lean_dec(x_3512);
x_3497 = x_3518;
x_3498 = x_3519;
goto block_3507;
}
}
else
{
lean_object* x_3520; lean_object* x_3521; 
x_3520 = lean_ctor_get(x_3509, 0);
lean_inc(x_3520);
x_3521 = lean_ctor_get(x_3509, 1);
lean_inc(x_3521);
lean_dec(x_3509);
x_3497 = x_3520;
x_3498 = x_3521;
goto block_3507;
}
block_3507:
{
uint8_t x_3499; 
x_3499 = l_Lean_Exception_isInterrupt(x_3497);
if (x_3499 == 0)
{
uint8_t x_3500; 
x_3500 = l_Lean_Exception_isRuntime(x_3497);
if (x_3500 == 0)
{
lean_object* x_3501; lean_object* x_3502; lean_object* x_3503; lean_object* x_3504; 
lean_dec(x_3497);
lean_dec(x_3482);
x_3501 = l_Lean_Meta_SavedState_restore(x_3201, x_3, x_4, x_5, x_6, x_3498);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_3201);
x_3502 = lean_ctor_get(x_3501, 1);
lean_inc(x_3502);
if (lean_is_exclusive(x_3501)) {
 lean_ctor_release(x_3501, 0);
 lean_ctor_release(x_3501, 1);
 x_3503 = x_3501;
} else {
 lean_dec_ref(x_3501);
 x_3503 = lean_box(0);
}
if (lean_is_scalar(x_3503)) {
 x_3504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3504 = x_3503;
}
lean_ctor_set(x_3504, 0, x_3488);
lean_ctor_set(x_3504, 1, x_3502);
return x_3504;
}
else
{
lean_object* x_3505; 
lean_dec(x_3201);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_3482)) {
 x_3505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3505 = x_3482;
 lean_ctor_set_tag(x_3505, 1);
}
lean_ctor_set(x_3505, 0, x_3497);
lean_ctor_set(x_3505, 1, x_3498);
return x_3505;
}
}
else
{
lean_object* x_3506; 
lean_dec(x_3201);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_3482)) {
 x_3506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3506 = x_3482;
 lean_ctor_set_tag(x_3506, 1);
}
lean_ctor_set(x_3506, 0, x_3497);
lean_ctor_set(x_3506, 1, x_3498);
return x_3506;
}
}
}
}
else
{
lean_object* x_3522; lean_object* x_3523; lean_object* x_3524; lean_object* x_3525; 
lean_dec(x_3203);
lean_dec(x_3201);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_free_object(x_24);
lean_free_object(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3522 = lean_ctor_get(x_3473, 0);
lean_inc(x_3522);
x_3523 = lean_ctor_get(x_3473, 1);
lean_inc(x_3523);
if (lean_is_exclusive(x_3473)) {
 lean_ctor_release(x_3473, 0);
 lean_ctor_release(x_3473, 1);
 x_3524 = x_3473;
} else {
 lean_dec_ref(x_3473);
 x_3524 = lean_box(0);
}
if (lean_is_scalar(x_3524)) {
 x_3525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3525 = x_3524;
}
lean_ctor_set(x_3525, 0, x_3522);
lean_ctor_set(x_3525, 1, x_3523);
return x_3525;
}
}
}
else
{
lean_object* x_3526; lean_object* x_3527; lean_object* x_3528; lean_object* x_3529; 
lean_dec(x_3203);
lean_dec(x_3201);
lean_dec(x_3199);
lean_dec(x_3198);
lean_dec(x_3197);
lean_dec(x_3195);
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3526 = lean_ctor_get(x_3204, 0);
lean_inc(x_3526);
x_3527 = lean_ctor_get(x_3204, 1);
lean_inc(x_3527);
if (lean_is_exclusive(x_3204)) {
 lean_ctor_release(x_3204, 0);
 lean_ctor_release(x_3204, 1);
 x_3528 = x_3204;
} else {
 lean_dec_ref(x_3204);
 x_3528 = lean_box(0);
}
if (lean_is_scalar(x_3528)) {
 x_3529 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3529 = x_3528;
}
lean_ctor_set(x_3529, 0, x_3526);
lean_ctor_set(x_3529, 1, x_3527);
return x_3529;
}
}
}
else
{
lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; 
lean_dec(x_3187);
lean_dec(x_3186);
lean_dec(x_3185);
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3530 = lean_ctor_get(x_3188, 0);
lean_inc(x_3530);
x_3531 = lean_ctor_get(x_3188, 1);
lean_inc(x_3531);
if (lean_is_exclusive(x_3188)) {
 lean_ctor_release(x_3188, 0);
 lean_ctor_release(x_3188, 1);
 x_3532 = x_3188;
} else {
 lean_dec_ref(x_3188);
 x_3532 = lean_box(0);
}
if (lean_is_scalar(x_3532)) {
 x_3533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3533 = x_3532;
}
lean_ctor_set(x_3533, 0, x_3530);
lean_ctor_set(x_3533, 1, x_3531);
return x_3533;
}
}
}
}
else
{
uint8_t x_3534; 
lean_free_object(x_24);
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3534 = !lean_is_exclusive(x_28);
if (x_3534 == 0)
{
return x_28;
}
else
{
lean_object* x_3535; lean_object* x_3536; lean_object* x_3537; 
x_3535 = lean_ctor_get(x_28, 0);
x_3536 = lean_ctor_get(x_28, 1);
lean_inc(x_3536);
lean_inc(x_3535);
lean_dec(x_28);
x_3537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3537, 0, x_3535);
lean_ctor_set(x_3537, 1, x_3536);
return x_3537;
}
}
}
else
{
lean_object* x_3538; lean_object* x_3539; lean_object* x_3540; 
x_3538 = lean_ctor_get(x_24, 0);
x_3539 = lean_ctor_get(x_24, 1);
lean_inc(x_3539);
lean_inc(x_3538);
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_3540 = l_Lean_Meta_isTypeApp_x3f(x_19, x_3, x_4, x_5, x_6, x_3539);
if (lean_obj_tag(x_3540) == 0)
{
lean_object* x_3541; 
x_3541 = lean_ctor_get(x_3540, 0);
lean_inc(x_3541);
if (lean_obj_tag(x_3541) == 0)
{
lean_object* x_3542; lean_object* x_3543; lean_object* x_3544; lean_object* x_3545; 
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3542 = lean_ctor_get(x_3540, 1);
lean_inc(x_3542);
if (lean_is_exclusive(x_3540)) {
 lean_ctor_release(x_3540, 0);
 lean_ctor_release(x_3540, 1);
 x_3543 = x_3540;
} else {
 lean_dec_ref(x_3540);
 x_3543 = lean_box(0);
}
x_3544 = lean_box(0);
if (lean_is_scalar(x_3543)) {
 x_3545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3545 = x_3543;
}
lean_ctor_set(x_3545, 0, x_3544);
lean_ctor_set(x_3545, 1, x_3542);
return x_3545;
}
else
{
lean_object* x_3546; lean_object* x_3547; lean_object* x_3548; lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; 
x_3546 = lean_ctor_get(x_3541, 0);
lean_inc(x_3546);
if (lean_is_exclusive(x_3541)) {
 lean_ctor_release(x_3541, 0);
 x_3547 = x_3541;
} else {
 lean_dec_ref(x_3541);
 x_3547 = lean_box(0);
}
x_3548 = lean_ctor_get(x_3540, 1);
lean_inc(x_3548);
lean_dec(x_3540);
x_3549 = lean_ctor_get(x_3546, 0);
lean_inc(x_3549);
x_3550 = lean_ctor_get(x_3546, 1);
lean_inc(x_3550);
if (lean_is_exclusive(x_3546)) {
 lean_ctor_release(x_3546, 0);
 lean_ctor_release(x_3546, 1);
 x_3551 = x_3546;
} else {
 lean_dec_ref(x_3546);
 x_3551 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3538);
x_3552 = l_Lean_Meta_isTypeApp_x3f(x_3538, x_3, x_4, x_5, x_6, x_3548);
if (lean_obj_tag(x_3552) == 0)
{
lean_object* x_3553; 
x_3553 = lean_ctor_get(x_3552, 0);
lean_inc(x_3553);
if (lean_obj_tag(x_3553) == 0)
{
lean_object* x_3554; lean_object* x_3555; lean_object* x_3556; lean_object* x_3557; 
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3547);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3554 = lean_ctor_get(x_3552, 1);
lean_inc(x_3554);
if (lean_is_exclusive(x_3552)) {
 lean_ctor_release(x_3552, 0);
 lean_ctor_release(x_3552, 1);
 x_3555 = x_3552;
} else {
 lean_dec_ref(x_3552);
 x_3555 = lean_box(0);
}
x_3556 = lean_box(0);
if (lean_is_scalar(x_3555)) {
 x_3557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3557 = x_3555;
}
lean_ctor_set(x_3557, 0, x_3556);
lean_ctor_set(x_3557, 1, x_3554);
return x_3557;
}
else
{
lean_object* x_3558; lean_object* x_3559; lean_object* x_3560; lean_object* x_3561; lean_object* x_3562; lean_object* x_3563; lean_object* x_3564; lean_object* x_3565; lean_object* x_3566; lean_object* x_3567; lean_object* x_3568; 
x_3558 = lean_ctor_get(x_3553, 0);
lean_inc(x_3558);
if (lean_is_exclusive(x_3553)) {
 lean_ctor_release(x_3553, 0);
 x_3559 = x_3553;
} else {
 lean_dec_ref(x_3553);
 x_3559 = lean_box(0);
}
x_3560 = lean_ctor_get(x_3552, 1);
lean_inc(x_3560);
lean_dec(x_3552);
x_3561 = lean_ctor_get(x_3558, 0);
lean_inc(x_3561);
x_3562 = lean_ctor_get(x_3558, 1);
lean_inc(x_3562);
if (lean_is_exclusive(x_3558)) {
 lean_ctor_release(x_3558, 0);
 lean_ctor_release(x_3558, 1);
 x_3563 = x_3558;
} else {
 lean_dec_ref(x_3558);
 x_3563 = lean_box(0);
}
x_3564 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_3560);
x_3565 = lean_ctor_get(x_3564, 0);
lean_inc(x_3565);
x_3566 = lean_ctor_get(x_3564, 1);
lean_inc(x_3566);
if (lean_is_exclusive(x_3564)) {
 lean_ctor_release(x_3564, 0);
 lean_ctor_release(x_3564, 1);
 x_3567 = x_3564;
} else {
 lean_dec_ref(x_3564);
 x_3567 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3549);
lean_inc(x_3561);
x_3568 = l_Lean_Meta_isExprDefEq(x_3561, x_3549, x_3, x_4, x_5, x_6, x_3566);
if (lean_obj_tag(x_3568) == 0)
{
lean_object* x_3569; uint8_t x_3570; 
x_3569 = lean_ctor_get(x_3568, 0);
lean_inc(x_3569);
x_3570 = lean_unbox(x_3569);
lean_dec(x_3569);
if (x_3570 == 0)
{
lean_object* x_3571; lean_object* x_3572; lean_object* x_3573; lean_object* x_3574; uint8_t x_3575; 
lean_dec(x_3565);
lean_dec(x_3547);
x_3571 = lean_ctor_get(x_3568, 1);
lean_inc(x_3571);
if (lean_is_exclusive(x_3568)) {
 lean_ctor_release(x_3568, 0);
 lean_ctor_release(x_3568, 1);
 x_3572 = x_3568;
} else {
 lean_dec_ref(x_3568);
 x_3572 = lean_box(0);
}
x_3573 = lean_ctor_get(x_5, 2);
lean_inc(x_3573);
x_3574 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_3575 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_3573, x_3574);
lean_dec(x_3573);
if (x_3575 == 0)
{
lean_object* x_3576; lean_object* x_3577; 
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3576 = lean_box(0);
if (lean_is_scalar(x_3572)) {
 x_3577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3577 = x_3572;
}
lean_ctor_set(x_3577, 0, x_3576);
lean_ctor_set(x_3577, 1, x_3571);
return x_3577;
}
else
{
lean_object* x_3578; 
lean_dec(x_3572);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3561);
x_3578 = lean_infer_type(x_3561, x_3, x_4, x_5, x_6, x_3571);
if (lean_obj_tag(x_3578) == 0)
{
lean_object* x_3579; lean_object* x_3580; lean_object* x_3581; 
x_3579 = lean_ctor_get(x_3578, 0);
lean_inc(x_3579);
x_3580 = lean_ctor_get(x_3578, 1);
lean_inc(x_3580);
lean_dec(x_3578);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3581 = lean_whnf(x_3579, x_3, x_4, x_5, x_6, x_3580);
if (lean_obj_tag(x_3581) == 0)
{
lean_object* x_3582; 
x_3582 = lean_ctor_get(x_3581, 0);
lean_inc(x_3582);
if (lean_obj_tag(x_3582) == 7)
{
lean_object* x_3583; 
x_3583 = lean_ctor_get(x_3582, 1);
lean_inc(x_3583);
if (lean_obj_tag(x_3583) == 3)
{
lean_object* x_3584; 
x_3584 = lean_ctor_get(x_3582, 2);
lean_inc(x_3584);
lean_dec(x_3582);
if (lean_obj_tag(x_3584) == 3)
{
lean_object* x_3585; lean_object* x_3586; lean_object* x_3587; lean_object* x_3588; 
x_3585 = lean_ctor_get(x_3581, 1);
lean_inc(x_3585);
lean_dec(x_3581);
x_3586 = lean_ctor_get(x_3583, 0);
lean_inc(x_3586);
lean_dec(x_3583);
x_3587 = lean_ctor_get(x_3584, 0);
lean_inc(x_3587);
lean_dec(x_3584);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3549);
x_3588 = lean_infer_type(x_3549, x_3, x_4, x_5, x_6, x_3585);
if (lean_obj_tag(x_3588) == 0)
{
lean_object* x_3589; lean_object* x_3590; lean_object* x_3591; 
x_3589 = lean_ctor_get(x_3588, 0);
lean_inc(x_3589);
x_3590 = lean_ctor_get(x_3588, 1);
lean_inc(x_3590);
lean_dec(x_3588);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3591 = lean_whnf(x_3589, x_3, x_4, x_5, x_6, x_3590);
if (lean_obj_tag(x_3591) == 0)
{
lean_object* x_3592; 
x_3592 = lean_ctor_get(x_3591, 0);
lean_inc(x_3592);
if (lean_obj_tag(x_3592) == 7)
{
lean_object* x_3593; 
x_3593 = lean_ctor_get(x_3592, 1);
lean_inc(x_3593);
if (lean_obj_tag(x_3593) == 3)
{
lean_object* x_3594; 
x_3594 = lean_ctor_get(x_3592, 2);
lean_inc(x_3594);
lean_dec(x_3592);
if (lean_obj_tag(x_3594) == 3)
{
lean_object* x_3595; lean_object* x_3596; lean_object* x_3597; lean_object* x_3598; 
x_3595 = lean_ctor_get(x_3591, 1);
lean_inc(x_3595);
lean_dec(x_3591);
x_3596 = lean_ctor_get(x_3593, 0);
lean_inc(x_3596);
lean_dec(x_3593);
x_3597 = lean_ctor_get(x_3594, 0);
lean_inc(x_3597);
lean_dec(x_3594);
x_3598 = l_Lean_Meta_decLevel(x_3586, x_3, x_4, x_5, x_6, x_3595);
if (lean_obj_tag(x_3598) == 0)
{
lean_object* x_3599; lean_object* x_3600; lean_object* x_3601; lean_object* x_3602; 
x_3599 = lean_ctor_get(x_3598, 0);
lean_inc(x_3599);
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
x_3602 = l_Lean_Meta_decLevel(x_3596, x_3, x_4, x_5, x_6, x_3600);
if (lean_obj_tag(x_3602) == 0)
{
lean_object* x_3603; lean_object* x_3604; lean_object* x_3605; uint8_t x_3606; lean_object* x_3607; 
x_3603 = lean_ctor_get(x_3602, 0);
lean_inc(x_3603);
x_3604 = lean_ctor_get(x_3602, 1);
lean_inc(x_3604);
if (lean_is_exclusive(x_3602)) {
 lean_ctor_release(x_3602, 0);
 lean_ctor_release(x_3602, 1);
 x_3605 = x_3602;
} else {
 lean_dec_ref(x_3602);
 x_3605 = lean_box(0);
}
x_3606 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3599);
x_3607 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_3599, x_3603, x_3606, x_3, x_4, x_5, x_6, x_3604);
if (lean_obj_tag(x_3607) == 0)
{
lean_object* x_3608; uint8_t x_3609; 
x_3608 = lean_ctor_get(x_3607, 0);
lean_inc(x_3608);
x_3609 = lean_unbox(x_3608);
lean_dec(x_3608);
if (x_3609 == 0)
{
lean_object* x_3610; lean_object* x_3611; lean_object* x_3612; lean_object* x_3613; 
lean_dec(x_3605);
lean_dec(x_3601);
lean_dec(x_3599);
lean_dec(x_3597);
lean_dec(x_3587);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3610 = lean_ctor_get(x_3607, 1);
lean_inc(x_3610);
if (lean_is_exclusive(x_3607)) {
 lean_ctor_release(x_3607, 0);
 lean_ctor_release(x_3607, 1);
 x_3611 = x_3607;
} else {
 lean_dec_ref(x_3607);
 x_3611 = lean_box(0);
}
x_3612 = lean_box(0);
if (lean_is_scalar(x_3611)) {
 x_3613 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3613 = x_3611;
}
lean_ctor_set(x_3613, 0, x_3612);
lean_ctor_set(x_3613, 1, x_3610);
return x_3613;
}
else
{
lean_object* x_3614; lean_object* x_3615; 
x_3614 = lean_ctor_get(x_3607, 1);
lean_inc(x_3614);
lean_dec(x_3607);
x_3615 = l_Lean_Meta_decLevel(x_3587, x_3, x_4, x_5, x_6, x_3614);
if (lean_obj_tag(x_3615) == 0)
{
lean_object* x_3616; lean_object* x_3617; lean_object* x_3618; lean_object* x_3619; 
x_3616 = lean_ctor_get(x_3615, 0);
lean_inc(x_3616);
x_3617 = lean_ctor_get(x_3615, 1);
lean_inc(x_3617);
if (lean_is_exclusive(x_3615)) {
 lean_ctor_release(x_3615, 0);
 lean_ctor_release(x_3615, 1);
 x_3618 = x_3615;
} else {
 lean_dec_ref(x_3615);
 x_3618 = lean_box(0);
}
x_3619 = l_Lean_Meta_decLevel(x_3597, x_3, x_4, x_5, x_6, x_3617);
if (lean_obj_tag(x_3619) == 0)
{
lean_object* x_3620; lean_object* x_3621; lean_object* x_3622; lean_object* x_3623; lean_object* x_3624; lean_object* x_3625; lean_object* x_3626; lean_object* x_3627; lean_object* x_3628; lean_object* x_3629; lean_object* x_3630; lean_object* x_3631; lean_object* x_3632; lean_object* x_3633; lean_object* x_3634; 
x_3620 = lean_ctor_get(x_3619, 0);
lean_inc(x_3620);
x_3621 = lean_ctor_get(x_3619, 1);
lean_inc(x_3621);
if (lean_is_exclusive(x_3619)) {
 lean_ctor_release(x_3619, 0);
 lean_ctor_release(x_3619, 1);
 x_3622 = x_3619;
} else {
 lean_dec_ref(x_3619);
 x_3622 = lean_box(0);
}
x_3623 = lean_box(0);
if (lean_is_scalar(x_3622)) {
 x_3624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3624 = x_3622;
 lean_ctor_set_tag(x_3624, 1);
}
lean_ctor_set(x_3624, 0, x_3620);
lean_ctor_set(x_3624, 1, x_3623);
if (lean_is_scalar(x_3618)) {
 x_3625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3625 = x_3618;
 lean_ctor_set_tag(x_3625, 1);
}
lean_ctor_set(x_3625, 0, x_3616);
lean_ctor_set(x_3625, 1, x_3624);
if (lean_is_scalar(x_3605)) {
 x_3626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3626 = x_3605;
 lean_ctor_set_tag(x_3626, 1);
}
lean_ctor_set(x_3626, 0, x_3599);
lean_ctor_set(x_3626, 1, x_3625);
x_3627 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_3628 = l_Lean_Expr_const___override(x_3627, x_3626);
lean_inc(x_3549);
if (lean_is_scalar(x_3601)) {
 x_3629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3629 = x_3601;
 lean_ctor_set_tag(x_3629, 1);
}
lean_ctor_set(x_3629, 0, x_3549);
lean_ctor_set(x_3629, 1, x_3623);
lean_inc(x_3561);
if (lean_is_scalar(x_3567)) {
 x_3630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3630 = x_3567;
 lean_ctor_set_tag(x_3630, 1);
}
lean_ctor_set(x_3630, 0, x_3561);
lean_ctor_set(x_3630, 1, x_3629);
x_3631 = lean_array_mk(x_3630);
x_3632 = l_Lean_mkAppN(x_3628, x_3631);
lean_dec(x_3631);
x_3633 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3634 = l_Lean_Meta_trySynthInstance(x_3632, x_3633, x_3, x_4, x_5, x_6, x_3621);
if (lean_obj_tag(x_3634) == 0)
{
lean_object* x_3635; 
x_3635 = lean_ctor_get(x_3634, 0);
lean_inc(x_3635);
if (lean_obj_tag(x_3635) == 1)
{
lean_object* x_3636; lean_object* x_3637; lean_object* x_3638; 
x_3636 = lean_ctor_get(x_3634, 1);
lean_inc(x_3636);
lean_dec(x_3634);
x_3637 = lean_ctor_get(x_3635, 0);
lean_inc(x_3637);
lean_dec(x_3635);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3562);
x_3638 = l_Lean_Meta_getDecLevel(x_3562, x_3, x_4, x_5, x_6, x_3636);
if (lean_obj_tag(x_3638) == 0)
{
lean_object* x_3639; lean_object* x_3640; lean_object* x_3641; lean_object* x_3642; 
x_3639 = lean_ctor_get(x_3638, 0);
lean_inc(x_3639);
x_3640 = lean_ctor_get(x_3638, 1);
lean_inc(x_3640);
if (lean_is_exclusive(x_3638)) {
 lean_ctor_release(x_3638, 0);
 lean_ctor_release(x_3638, 1);
 x_3641 = x_3638;
} else {
 lean_dec_ref(x_3638);
 x_3641 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3642 = l_Lean_Meta_getDecLevel(x_3538, x_3, x_4, x_5, x_6, x_3640);
if (lean_obj_tag(x_3642) == 0)
{
lean_object* x_3643; lean_object* x_3644; lean_object* x_3645; lean_object* x_3646; 
x_3643 = lean_ctor_get(x_3642, 0);
lean_inc(x_3643);
x_3644 = lean_ctor_get(x_3642, 1);
lean_inc(x_3644);
if (lean_is_exclusive(x_3642)) {
 lean_ctor_release(x_3642, 0);
 lean_ctor_release(x_3642, 1);
 x_3645 = x_3642;
} else {
 lean_dec_ref(x_3642);
 x_3645 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_3646 = l_Lean_Meta_getDecLevel(x_19, x_3, x_4, x_5, x_6, x_3644);
if (lean_obj_tag(x_3646) == 0)
{
lean_object* x_3647; lean_object* x_3648; lean_object* x_3649; lean_object* x_3650; lean_object* x_3651; lean_object* x_3652; lean_object* x_3653; lean_object* x_3654; lean_object* x_3655; lean_object* x_3656; lean_object* x_3657; lean_object* x_3658; lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; 
x_3647 = lean_ctor_get(x_3646, 0);
lean_inc(x_3647);
x_3648 = lean_ctor_get(x_3646, 1);
lean_inc(x_3648);
if (lean_is_exclusive(x_3646)) {
 lean_ctor_release(x_3646, 0);
 lean_ctor_release(x_3646, 1);
 x_3649 = x_3646;
} else {
 lean_dec_ref(x_3646);
 x_3649 = lean_box(0);
}
if (lean_is_scalar(x_3649)) {
 x_3650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3650 = x_3649;
 lean_ctor_set_tag(x_3650, 1);
}
lean_ctor_set(x_3650, 0, x_3647);
lean_ctor_set(x_3650, 1, x_3623);
if (lean_is_scalar(x_3645)) {
 x_3651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3651 = x_3645;
 lean_ctor_set_tag(x_3651, 1);
}
lean_ctor_set(x_3651, 0, x_3643);
lean_ctor_set(x_3651, 1, x_3650);
if (lean_is_scalar(x_3641)) {
 x_3652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3652 = x_3641;
 lean_ctor_set_tag(x_3652, 1);
}
lean_ctor_set(x_3652, 0, x_3639);
lean_ctor_set(x_3652, 1, x_3651);
x_3653 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_3652);
x_3654 = l_Lean_Expr_const___override(x_3653, x_3652);
if (lean_is_scalar(x_3563)) {
 x_3655 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3655 = x_3563;
 lean_ctor_set_tag(x_3655, 1);
}
lean_ctor_set(x_3655, 0, x_1);
lean_ctor_set(x_3655, 1, x_3623);
lean_inc(x_3655);
lean_inc(x_3562);
if (lean_is_scalar(x_3551)) {
 x_3656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3656 = x_3551;
 lean_ctor_set_tag(x_3656, 1);
}
lean_ctor_set(x_3656, 0, x_3562);
lean_ctor_set(x_3656, 1, x_3655);
lean_inc(x_3637);
x_3657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3657, 0, x_3637);
lean_ctor_set(x_3657, 1, x_3656);
lean_inc(x_3549);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_3657);
lean_ctor_set(x_17, 0, x_3549);
lean_inc(x_3561);
x_3658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3658, 0, x_3561);
lean_ctor_set(x_3658, 1, x_17);
x_3659 = lean_array_mk(x_3658);
x_3660 = l_Lean_mkAppN(x_3654, x_3659);
lean_dec(x_3659);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3660);
x_3661 = lean_infer_type(x_3660, x_3, x_4, x_5, x_6, x_3648);
if (lean_obj_tag(x_3661) == 0)
{
lean_object* x_3662; lean_object* x_3663; lean_object* x_3664; lean_object* x_3665; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_3665 = l_Lean_Meta_isExprDefEq(x_19, x_3662, x_3, x_4, x_5, x_6, x_3663);
if (lean_obj_tag(x_3665) == 0)
{
lean_object* x_3666; uint8_t x_3667; 
x_3666 = lean_ctor_get(x_3665, 0);
lean_inc(x_3666);
x_3667 = lean_unbox(x_3666);
lean_dec(x_3666);
if (x_3667 == 0)
{
lean_object* x_3668; lean_object* x_3669; 
lean_dec(x_3660);
lean_dec(x_3559);
x_3668 = lean_ctor_get(x_3665, 1);
lean_inc(x_3668);
lean_dec(x_3665);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3549);
x_3669 = l_Lean_Meta_isMonad_x3f(x_3549, x_3, x_4, x_5, x_6, x_3668);
if (lean_obj_tag(x_3669) == 0)
{
lean_object* x_3670; 
x_3670 = lean_ctor_get(x_3669, 0);
lean_inc(x_3670);
if (lean_obj_tag(x_3670) == 0)
{
lean_object* x_3671; lean_object* x_3672; lean_object* x_3673; 
lean_dec(x_3664);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3671 = lean_ctor_get(x_3669, 1);
lean_inc(x_3671);
if (lean_is_exclusive(x_3669)) {
 lean_ctor_release(x_3669, 0);
 lean_ctor_release(x_3669, 1);
 x_3672 = x_3669;
} else {
 lean_dec_ref(x_3669);
 x_3672 = lean_box(0);
}
if (lean_is_scalar(x_3672)) {
 x_3673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3673 = x_3672;
}
lean_ctor_set(x_3673, 0, x_3633);
lean_ctor_set(x_3673, 1, x_3671);
return x_3673;
}
else
{
lean_object* x_3674; lean_object* x_3675; lean_object* x_3676; 
x_3674 = lean_ctor_get(x_3669, 1);
lean_inc(x_3674);
lean_dec(x_3669);
x_3675 = lean_ctor_get(x_3670, 0);
lean_inc(x_3675);
lean_dec(x_3670);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3562);
x_3676 = l_Lean_Meta_getLevel(x_3562, x_3, x_4, x_5, x_6, x_3674);
if (lean_obj_tag(x_3676) == 0)
{
lean_object* x_3677; lean_object* x_3678; lean_object* x_3679; lean_object* x_3680; 
x_3677 = lean_ctor_get(x_3676, 0);
lean_inc(x_3677);
x_3678 = lean_ctor_get(x_3676, 1);
lean_inc(x_3678);
if (lean_is_exclusive(x_3676)) {
 lean_ctor_release(x_3676, 0);
 lean_ctor_release(x_3676, 1);
 x_3679 = x_3676;
} else {
 lean_dec_ref(x_3676);
 x_3679 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3550);
x_3680 = l_Lean_Meta_getLevel(x_3550, x_3, x_4, x_5, x_6, x_3678);
if (lean_obj_tag(x_3680) == 0)
{
lean_object* x_3681; lean_object* x_3682; lean_object* x_3683; lean_object* x_3684; lean_object* x_3685; lean_object* x_3686; lean_object* x_3687; lean_object* x_3688; lean_object* x_3689; lean_object* x_3690; lean_object* x_3691; lean_object* x_3692; lean_object* x_3693; lean_object* x_3694; uint8_t x_3695; lean_object* x_3696; lean_object* x_3697; 
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
if (lean_is_scalar(x_3683)) {
 x_3684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3684 = x_3683;
 lean_ctor_set_tag(x_3684, 1);
}
lean_ctor_set(x_3684, 0, x_3681);
lean_ctor_set(x_3684, 1, x_3623);
if (lean_is_scalar(x_3679)) {
 x_3685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3685 = x_3679;
 lean_ctor_set_tag(x_3685, 1);
}
lean_ctor_set(x_3685, 0, x_3677);
lean_ctor_set(x_3685, 1, x_3684);
x_3686 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_3687 = l_Lean_Expr_const___override(x_3686, x_3685);
lean_inc(x_3550);
if (lean_is_scalar(x_3664)) {
 x_3688 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3688 = x_3664;
 lean_ctor_set_tag(x_3688, 1);
}
lean_ctor_set(x_3688, 0, x_3550);
lean_ctor_set(x_3688, 1, x_3623);
x_3689 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_3690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3690, 0, x_3689);
lean_ctor_set(x_3690, 1, x_3688);
lean_inc(x_3562);
x_3691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3691, 0, x_3562);
lean_ctor_set(x_3691, 1, x_3690);
x_3692 = lean_array_mk(x_3691);
x_3693 = l_Lean_mkAppN(x_3687, x_3692);
lean_dec(x_3692);
x_3694 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_3695 = 0;
lean_inc(x_3562);
x_3696 = l_Lean_Expr_forallE___override(x_3694, x_3562, x_3693, x_3695);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3697 = l_Lean_Meta_trySynthInstance(x_3696, x_3633, x_3, x_4, x_5, x_6, x_3682);
if (lean_obj_tag(x_3697) == 0)
{
lean_object* x_3698; 
x_3698 = lean_ctor_get(x_3697, 0);
lean_inc(x_3698);
if (lean_obj_tag(x_3698) == 1)
{
lean_object* x_3699; lean_object* x_3700; lean_object* x_3701; lean_object* x_3702; lean_object* x_3703; lean_object* x_3704; lean_object* x_3705; lean_object* x_3706; lean_object* x_3707; lean_object* x_3708; lean_object* x_3709; lean_object* x_3710; lean_object* x_3711; lean_object* x_3712; 
x_3699 = lean_ctor_get(x_3697, 1);
lean_inc(x_3699);
lean_dec(x_3697);
x_3700 = lean_ctor_get(x_3698, 0);
lean_inc(x_3700);
lean_dec(x_3698);
x_3701 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_3702 = l_Lean_Expr_const___override(x_3701, x_3652);
x_3703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3703, 0, x_3675);
lean_ctor_set(x_3703, 1, x_3655);
x_3704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3704, 0, x_3700);
lean_ctor_set(x_3704, 1, x_3703);
x_3705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3705, 0, x_3637);
lean_ctor_set(x_3705, 1, x_3704);
x_3706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3706, 0, x_3550);
lean_ctor_set(x_3706, 1, x_3705);
x_3707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3707, 0, x_3562);
lean_ctor_set(x_3707, 1, x_3706);
x_3708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3708, 0, x_3549);
lean_ctor_set(x_3708, 1, x_3707);
x_3709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3709, 0, x_3561);
lean_ctor_set(x_3709, 1, x_3708);
x_3710 = lean_array_mk(x_3709);
x_3711 = l_Lean_mkAppN(x_3702, x_3710);
lean_dec(x_3710);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3712 = l_Lean_Meta_expandCoe(x_3711, x_3, x_4, x_5, x_6, x_3699);
if (lean_obj_tag(x_3712) == 0)
{
lean_object* x_3713; lean_object* x_3714; lean_object* x_3715; 
x_3713 = lean_ctor_get(x_3712, 0);
lean_inc(x_3713);
x_3714 = lean_ctor_get(x_3712, 1);
lean_inc(x_3714);
lean_dec(x_3712);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3713);
x_3715 = lean_infer_type(x_3713, x_3, x_4, x_5, x_6, x_3714);
if (lean_obj_tag(x_3715) == 0)
{
lean_object* x_3716; lean_object* x_3717; lean_object* x_3718; 
x_3716 = lean_ctor_get(x_3715, 0);
lean_inc(x_3716);
x_3717 = lean_ctor_get(x_3715, 1);
lean_inc(x_3717);
lean_dec(x_3715);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3718 = l_Lean_Meta_isExprDefEq(x_19, x_3716, x_3, x_4, x_5, x_6, x_3717);
if (lean_obj_tag(x_3718) == 0)
{
lean_object* x_3719; uint8_t x_3720; 
x_3719 = lean_ctor_get(x_3718, 0);
lean_inc(x_3719);
x_3720 = lean_unbox(x_3719);
lean_dec(x_3719);
if (x_3720 == 0)
{
lean_object* x_3721; lean_object* x_3722; lean_object* x_3723; 
lean_dec(x_3713);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3721 = lean_ctor_get(x_3718, 1);
lean_inc(x_3721);
if (lean_is_exclusive(x_3718)) {
 lean_ctor_release(x_3718, 0);
 lean_ctor_release(x_3718, 1);
 x_3722 = x_3718;
} else {
 lean_dec_ref(x_3718);
 x_3722 = lean_box(0);
}
if (lean_is_scalar(x_3722)) {
 x_3723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3723 = x_3722;
}
lean_ctor_set(x_3723, 0, x_3633);
lean_ctor_set(x_3723, 1, x_3721);
return x_3723;
}
else
{
lean_object* x_3724; lean_object* x_3725; lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; lean_object* x_3729; lean_object* x_3730; 
x_3724 = lean_ctor_get(x_3718, 1);
lean_inc(x_3724);
lean_dec(x_3718);
x_3725 = lean_box(0);
x_3726 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_3713, x_3725, x_3, x_4, x_5, x_6, x_3724);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3727 = lean_ctor_get(x_3726, 0);
lean_inc(x_3727);
x_3728 = lean_ctor_get(x_3726, 1);
lean_inc(x_3728);
if (lean_is_exclusive(x_3726)) {
 lean_ctor_release(x_3726, 0);
 lean_ctor_release(x_3726, 1);
 x_3729 = x_3726;
} else {
 lean_dec_ref(x_3726);
 x_3729 = lean_box(0);
}
if (lean_is_scalar(x_3729)) {
 x_3730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3730 = x_3729;
}
lean_ctor_set(x_3730, 0, x_3727);
lean_ctor_set(x_3730, 1, x_3728);
return x_3730;
}
}
else
{
lean_object* x_3731; lean_object* x_3732; 
lean_dec(x_3713);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3731 = lean_ctor_get(x_3718, 0);
lean_inc(x_3731);
x_3732 = lean_ctor_get(x_3718, 1);
lean_inc(x_3732);
lean_dec(x_3718);
x_8 = x_3731;
x_9 = x_3732;
goto block_16;
}
}
else
{
lean_object* x_3733; lean_object* x_3734; 
lean_dec(x_3713);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3733 = lean_ctor_get(x_3715, 0);
lean_inc(x_3733);
x_3734 = lean_ctor_get(x_3715, 1);
lean_inc(x_3734);
lean_dec(x_3715);
x_8 = x_3733;
x_9 = x_3734;
goto block_16;
}
}
else
{
lean_object* x_3735; lean_object* x_3736; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3735 = lean_ctor_get(x_3712, 0);
lean_inc(x_3735);
x_3736 = lean_ctor_get(x_3712, 1);
lean_inc(x_3736);
lean_dec(x_3712);
x_8 = x_3735;
x_9 = x_3736;
goto block_16;
}
}
else
{
lean_object* x_3737; lean_object* x_3738; lean_object* x_3739; 
lean_dec(x_3698);
lean_dec(x_3675);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3737 = lean_ctor_get(x_3697, 1);
lean_inc(x_3737);
if (lean_is_exclusive(x_3697)) {
 lean_ctor_release(x_3697, 0);
 lean_ctor_release(x_3697, 1);
 x_3738 = x_3697;
} else {
 lean_dec_ref(x_3697);
 x_3738 = lean_box(0);
}
if (lean_is_scalar(x_3738)) {
 x_3739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3739 = x_3738;
}
lean_ctor_set(x_3739, 0, x_3633);
lean_ctor_set(x_3739, 1, x_3737);
return x_3739;
}
}
else
{
lean_object* x_3740; lean_object* x_3741; 
lean_dec(x_3675);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3740 = lean_ctor_get(x_3697, 0);
lean_inc(x_3740);
x_3741 = lean_ctor_get(x_3697, 1);
lean_inc(x_3741);
lean_dec(x_3697);
x_8 = x_3740;
x_9 = x_3741;
goto block_16;
}
}
else
{
lean_object* x_3742; lean_object* x_3743; 
lean_dec(x_3679);
lean_dec(x_3677);
lean_dec(x_3675);
lean_dec(x_3664);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3742 = lean_ctor_get(x_3680, 0);
lean_inc(x_3742);
x_3743 = lean_ctor_get(x_3680, 1);
lean_inc(x_3743);
lean_dec(x_3680);
x_8 = x_3742;
x_9 = x_3743;
goto block_16;
}
}
else
{
lean_object* x_3744; lean_object* x_3745; 
lean_dec(x_3675);
lean_dec(x_3664);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3744 = lean_ctor_get(x_3676, 0);
lean_inc(x_3744);
x_3745 = lean_ctor_get(x_3676, 1);
lean_inc(x_3745);
lean_dec(x_3676);
x_8 = x_3744;
x_9 = x_3745;
goto block_16;
}
}
}
else
{
lean_object* x_3746; lean_object* x_3747; 
lean_dec(x_3664);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3746 = lean_ctor_get(x_3669, 0);
lean_inc(x_3746);
x_3747 = lean_ctor_get(x_3669, 1);
lean_inc(x_3747);
lean_dec(x_3669);
x_8 = x_3746;
x_9 = x_3747;
goto block_16;
}
}
else
{
lean_object* x_3748; lean_object* x_3749; lean_object* x_3750; lean_object* x_3751; 
lean_dec(x_3664);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3748 = lean_ctor_get(x_3665, 1);
lean_inc(x_3748);
if (lean_is_exclusive(x_3665)) {
 lean_ctor_release(x_3665, 0);
 lean_ctor_release(x_3665, 1);
 x_3749 = x_3665;
} else {
 lean_dec_ref(x_3665);
 x_3749 = lean_box(0);
}
if (lean_is_scalar(x_3559)) {
 x_3750 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3750 = x_3559;
}
lean_ctor_set(x_3750, 0, x_3660);
if (lean_is_scalar(x_3749)) {
 x_3751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3751 = x_3749;
}
lean_ctor_set(x_3751, 0, x_3750);
lean_ctor_set(x_3751, 1, x_3748);
return x_3751;
}
}
else
{
lean_object* x_3752; lean_object* x_3753; 
lean_dec(x_3664);
lean_dec(x_3660);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3752 = lean_ctor_get(x_3665, 0);
lean_inc(x_3752);
x_3753 = lean_ctor_get(x_3665, 1);
lean_inc(x_3753);
lean_dec(x_3665);
x_8 = x_3752;
x_9 = x_3753;
goto block_16;
}
}
else
{
lean_object* x_3754; lean_object* x_3755; 
lean_dec(x_3660);
lean_dec(x_3655);
lean_dec(x_3652);
lean_dec(x_3637);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3754 = lean_ctor_get(x_3661, 0);
lean_inc(x_3754);
x_3755 = lean_ctor_get(x_3661, 1);
lean_inc(x_3755);
lean_dec(x_3661);
x_8 = x_3754;
x_9 = x_3755;
goto block_16;
}
}
else
{
lean_object* x_3756; lean_object* x_3757; 
lean_dec(x_3645);
lean_dec(x_3643);
lean_dec(x_3641);
lean_dec(x_3639);
lean_dec(x_3637);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3756 = lean_ctor_get(x_3646, 0);
lean_inc(x_3756);
x_3757 = lean_ctor_get(x_3646, 1);
lean_inc(x_3757);
lean_dec(x_3646);
x_8 = x_3756;
x_9 = x_3757;
goto block_16;
}
}
else
{
lean_object* x_3758; lean_object* x_3759; 
lean_dec(x_3641);
lean_dec(x_3639);
lean_dec(x_3637);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3758 = lean_ctor_get(x_3642, 0);
lean_inc(x_3758);
x_3759 = lean_ctor_get(x_3642, 1);
lean_inc(x_3759);
lean_dec(x_3642);
x_8 = x_3758;
x_9 = x_3759;
goto block_16;
}
}
else
{
lean_object* x_3760; lean_object* x_3761; 
lean_dec(x_3637);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3760 = lean_ctor_get(x_3638, 0);
lean_inc(x_3760);
x_3761 = lean_ctor_get(x_3638, 1);
lean_inc(x_3761);
lean_dec(x_3638);
x_8 = x_3760;
x_9 = x_3761;
goto block_16;
}
}
else
{
lean_object* x_3762; lean_object* x_3763; lean_object* x_3764; 
lean_dec(x_3635);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3762 = lean_ctor_get(x_3634, 1);
lean_inc(x_3762);
if (lean_is_exclusive(x_3634)) {
 lean_ctor_release(x_3634, 0);
 lean_ctor_release(x_3634, 1);
 x_3763 = x_3634;
} else {
 lean_dec_ref(x_3634);
 x_3763 = lean_box(0);
}
if (lean_is_scalar(x_3763)) {
 x_3764 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3764 = x_3763;
}
lean_ctor_set(x_3764, 0, x_3633);
lean_ctor_set(x_3764, 1, x_3762);
return x_3764;
}
}
else
{
lean_object* x_3765; lean_object* x_3766; 
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3765 = lean_ctor_get(x_3634, 0);
lean_inc(x_3765);
x_3766 = lean_ctor_get(x_3634, 1);
lean_inc(x_3766);
lean_dec(x_3634);
x_8 = x_3765;
x_9 = x_3766;
goto block_16;
}
}
else
{
lean_object* x_3767; lean_object* x_3768; 
lean_dec(x_3618);
lean_dec(x_3616);
lean_dec(x_3605);
lean_dec(x_3601);
lean_dec(x_3599);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3767 = lean_ctor_get(x_3619, 0);
lean_inc(x_3767);
x_3768 = lean_ctor_get(x_3619, 1);
lean_inc(x_3768);
lean_dec(x_3619);
x_8 = x_3767;
x_9 = x_3768;
goto block_16;
}
}
else
{
lean_object* x_3769; lean_object* x_3770; 
lean_dec(x_3605);
lean_dec(x_3601);
lean_dec(x_3599);
lean_dec(x_3597);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3769 = lean_ctor_get(x_3615, 0);
lean_inc(x_3769);
x_3770 = lean_ctor_get(x_3615, 1);
lean_inc(x_3770);
lean_dec(x_3615);
x_8 = x_3769;
x_9 = x_3770;
goto block_16;
}
}
}
else
{
lean_object* x_3771; lean_object* x_3772; 
lean_dec(x_3605);
lean_dec(x_3601);
lean_dec(x_3599);
lean_dec(x_3597);
lean_dec(x_3587);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3771 = lean_ctor_get(x_3607, 0);
lean_inc(x_3771);
x_3772 = lean_ctor_get(x_3607, 1);
lean_inc(x_3772);
lean_dec(x_3607);
x_8 = x_3771;
x_9 = x_3772;
goto block_16;
}
}
else
{
lean_object* x_3773; lean_object* x_3774; 
lean_dec(x_3601);
lean_dec(x_3599);
lean_dec(x_3597);
lean_dec(x_3587);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3773 = lean_ctor_get(x_3602, 0);
lean_inc(x_3773);
x_3774 = lean_ctor_get(x_3602, 1);
lean_inc(x_3774);
lean_dec(x_3602);
x_8 = x_3773;
x_9 = x_3774;
goto block_16;
}
}
else
{
lean_object* x_3775; lean_object* x_3776; 
lean_dec(x_3597);
lean_dec(x_3596);
lean_dec(x_3587);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3775 = lean_ctor_get(x_3598, 0);
lean_inc(x_3775);
x_3776 = lean_ctor_get(x_3598, 1);
lean_inc(x_3776);
lean_dec(x_3598);
x_8 = x_3775;
x_9 = x_3776;
goto block_16;
}
}
else
{
lean_object* x_3777; lean_object* x_3778; lean_object* x_3779; lean_object* x_3780; 
lean_dec(x_3594);
lean_dec(x_3593);
lean_dec(x_3587);
lean_dec(x_3586);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3777 = lean_ctor_get(x_3591, 1);
lean_inc(x_3777);
if (lean_is_exclusive(x_3591)) {
 lean_ctor_release(x_3591, 0);
 lean_ctor_release(x_3591, 1);
 x_3778 = x_3591;
} else {
 lean_dec_ref(x_3591);
 x_3778 = lean_box(0);
}
x_3779 = lean_box(0);
if (lean_is_scalar(x_3778)) {
 x_3780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3780 = x_3778;
}
lean_ctor_set(x_3780, 0, x_3779);
lean_ctor_set(x_3780, 1, x_3777);
return x_3780;
}
}
else
{
lean_object* x_3781; lean_object* x_3782; lean_object* x_3783; lean_object* x_3784; 
lean_dec(x_3593);
lean_dec(x_3592);
lean_dec(x_3587);
lean_dec(x_3586);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3781 = lean_ctor_get(x_3591, 1);
lean_inc(x_3781);
if (lean_is_exclusive(x_3591)) {
 lean_ctor_release(x_3591, 0);
 lean_ctor_release(x_3591, 1);
 x_3782 = x_3591;
} else {
 lean_dec_ref(x_3591);
 x_3782 = lean_box(0);
}
x_3783 = lean_box(0);
if (lean_is_scalar(x_3782)) {
 x_3784 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3784 = x_3782;
}
lean_ctor_set(x_3784, 0, x_3783);
lean_ctor_set(x_3784, 1, x_3781);
return x_3784;
}
}
else
{
lean_object* x_3785; lean_object* x_3786; lean_object* x_3787; lean_object* x_3788; 
lean_dec(x_3592);
lean_dec(x_3587);
lean_dec(x_3586);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3785 = lean_ctor_get(x_3591, 1);
lean_inc(x_3785);
if (lean_is_exclusive(x_3591)) {
 lean_ctor_release(x_3591, 0);
 lean_ctor_release(x_3591, 1);
 x_3786 = x_3591;
} else {
 lean_dec_ref(x_3591);
 x_3786 = lean_box(0);
}
x_3787 = lean_box(0);
if (lean_is_scalar(x_3786)) {
 x_3788 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3788 = x_3786;
}
lean_ctor_set(x_3788, 0, x_3787);
lean_ctor_set(x_3788, 1, x_3785);
return x_3788;
}
}
else
{
lean_object* x_3789; lean_object* x_3790; lean_object* x_3791; uint8_t x_3792; 
lean_dec(x_3587);
lean_dec(x_3586);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3789 = lean_ctor_get(x_3591, 0);
lean_inc(x_3789);
x_3790 = lean_ctor_get(x_3591, 1);
lean_inc(x_3790);
if (lean_is_exclusive(x_3591)) {
 lean_ctor_release(x_3591, 0);
 lean_ctor_release(x_3591, 1);
 x_3791 = x_3591;
} else {
 lean_dec_ref(x_3591);
 x_3791 = lean_box(0);
}
x_3792 = l_Lean_Exception_isInterrupt(x_3789);
if (x_3792 == 0)
{
uint8_t x_3793; 
x_3793 = l_Lean_Exception_isRuntime(x_3789);
if (x_3793 == 0)
{
lean_object* x_3794; lean_object* x_3795; 
lean_dec(x_3789);
x_3794 = lean_box(0);
if (lean_is_scalar(x_3791)) {
 x_3795 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3795 = x_3791;
 lean_ctor_set_tag(x_3795, 0);
}
lean_ctor_set(x_3795, 0, x_3794);
lean_ctor_set(x_3795, 1, x_3790);
return x_3795;
}
else
{
lean_object* x_3796; 
if (lean_is_scalar(x_3791)) {
 x_3796 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3796 = x_3791;
}
lean_ctor_set(x_3796, 0, x_3789);
lean_ctor_set(x_3796, 1, x_3790);
return x_3796;
}
}
else
{
lean_object* x_3797; 
if (lean_is_scalar(x_3791)) {
 x_3797 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3797 = x_3791;
}
lean_ctor_set(x_3797, 0, x_3789);
lean_ctor_set(x_3797, 1, x_3790);
return x_3797;
}
}
}
else
{
lean_object* x_3798; lean_object* x_3799; lean_object* x_3800; uint8_t x_3801; 
lean_dec(x_3587);
lean_dec(x_3586);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3798 = lean_ctor_get(x_3588, 0);
lean_inc(x_3798);
x_3799 = lean_ctor_get(x_3588, 1);
lean_inc(x_3799);
if (lean_is_exclusive(x_3588)) {
 lean_ctor_release(x_3588, 0);
 lean_ctor_release(x_3588, 1);
 x_3800 = x_3588;
} else {
 lean_dec_ref(x_3588);
 x_3800 = lean_box(0);
}
x_3801 = l_Lean_Exception_isInterrupt(x_3798);
if (x_3801 == 0)
{
uint8_t x_3802; 
x_3802 = l_Lean_Exception_isRuntime(x_3798);
if (x_3802 == 0)
{
lean_object* x_3803; lean_object* x_3804; 
lean_dec(x_3798);
x_3803 = lean_box(0);
if (lean_is_scalar(x_3800)) {
 x_3804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3804 = x_3800;
 lean_ctor_set_tag(x_3804, 0);
}
lean_ctor_set(x_3804, 0, x_3803);
lean_ctor_set(x_3804, 1, x_3799);
return x_3804;
}
else
{
lean_object* x_3805; 
if (lean_is_scalar(x_3800)) {
 x_3805 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3805 = x_3800;
}
lean_ctor_set(x_3805, 0, x_3798);
lean_ctor_set(x_3805, 1, x_3799);
return x_3805;
}
}
else
{
lean_object* x_3806; 
if (lean_is_scalar(x_3800)) {
 x_3806 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3806 = x_3800;
}
lean_ctor_set(x_3806, 0, x_3798);
lean_ctor_set(x_3806, 1, x_3799);
return x_3806;
}
}
}
else
{
lean_object* x_3807; lean_object* x_3808; lean_object* x_3809; lean_object* x_3810; 
lean_dec(x_3584);
lean_dec(x_3583);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3807 = lean_ctor_get(x_3581, 1);
lean_inc(x_3807);
if (lean_is_exclusive(x_3581)) {
 lean_ctor_release(x_3581, 0);
 lean_ctor_release(x_3581, 1);
 x_3808 = x_3581;
} else {
 lean_dec_ref(x_3581);
 x_3808 = lean_box(0);
}
x_3809 = lean_box(0);
if (lean_is_scalar(x_3808)) {
 x_3810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3810 = x_3808;
}
lean_ctor_set(x_3810, 0, x_3809);
lean_ctor_set(x_3810, 1, x_3807);
return x_3810;
}
}
else
{
lean_object* x_3811; lean_object* x_3812; lean_object* x_3813; lean_object* x_3814; 
lean_dec(x_3583);
lean_dec(x_3582);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3811 = lean_ctor_get(x_3581, 1);
lean_inc(x_3811);
if (lean_is_exclusive(x_3581)) {
 lean_ctor_release(x_3581, 0);
 lean_ctor_release(x_3581, 1);
 x_3812 = x_3581;
} else {
 lean_dec_ref(x_3581);
 x_3812 = lean_box(0);
}
x_3813 = lean_box(0);
if (lean_is_scalar(x_3812)) {
 x_3814 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3814 = x_3812;
}
lean_ctor_set(x_3814, 0, x_3813);
lean_ctor_set(x_3814, 1, x_3811);
return x_3814;
}
}
else
{
lean_object* x_3815; lean_object* x_3816; lean_object* x_3817; lean_object* x_3818; 
lean_dec(x_3582);
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3815 = lean_ctor_get(x_3581, 1);
lean_inc(x_3815);
if (lean_is_exclusive(x_3581)) {
 lean_ctor_release(x_3581, 0);
 lean_ctor_release(x_3581, 1);
 x_3816 = x_3581;
} else {
 lean_dec_ref(x_3581);
 x_3816 = lean_box(0);
}
x_3817 = lean_box(0);
if (lean_is_scalar(x_3816)) {
 x_3818 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3818 = x_3816;
}
lean_ctor_set(x_3818, 0, x_3817);
lean_ctor_set(x_3818, 1, x_3815);
return x_3818;
}
}
else
{
lean_object* x_3819; lean_object* x_3820; lean_object* x_3821; uint8_t x_3822; 
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3819 = lean_ctor_get(x_3581, 0);
lean_inc(x_3819);
x_3820 = lean_ctor_get(x_3581, 1);
lean_inc(x_3820);
if (lean_is_exclusive(x_3581)) {
 lean_ctor_release(x_3581, 0);
 lean_ctor_release(x_3581, 1);
 x_3821 = x_3581;
} else {
 lean_dec_ref(x_3581);
 x_3821 = lean_box(0);
}
x_3822 = l_Lean_Exception_isInterrupt(x_3819);
if (x_3822 == 0)
{
uint8_t x_3823; 
x_3823 = l_Lean_Exception_isRuntime(x_3819);
if (x_3823 == 0)
{
lean_object* x_3824; lean_object* x_3825; 
lean_dec(x_3819);
x_3824 = lean_box(0);
if (lean_is_scalar(x_3821)) {
 x_3825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3825 = x_3821;
 lean_ctor_set_tag(x_3825, 0);
}
lean_ctor_set(x_3825, 0, x_3824);
lean_ctor_set(x_3825, 1, x_3820);
return x_3825;
}
else
{
lean_object* x_3826; 
if (lean_is_scalar(x_3821)) {
 x_3826 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3826 = x_3821;
}
lean_ctor_set(x_3826, 0, x_3819);
lean_ctor_set(x_3826, 1, x_3820);
return x_3826;
}
}
else
{
lean_object* x_3827; 
if (lean_is_scalar(x_3821)) {
 x_3827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3827 = x_3821;
}
lean_ctor_set(x_3827, 0, x_3819);
lean_ctor_set(x_3827, 1, x_3820);
return x_3827;
}
}
}
else
{
lean_object* x_3828; lean_object* x_3829; lean_object* x_3830; uint8_t x_3831; 
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3828 = lean_ctor_get(x_3578, 0);
lean_inc(x_3828);
x_3829 = lean_ctor_get(x_3578, 1);
lean_inc(x_3829);
if (lean_is_exclusive(x_3578)) {
 lean_ctor_release(x_3578, 0);
 lean_ctor_release(x_3578, 1);
 x_3830 = x_3578;
} else {
 lean_dec_ref(x_3578);
 x_3830 = lean_box(0);
}
x_3831 = l_Lean_Exception_isInterrupt(x_3828);
if (x_3831 == 0)
{
uint8_t x_3832; 
x_3832 = l_Lean_Exception_isRuntime(x_3828);
if (x_3832 == 0)
{
lean_object* x_3833; lean_object* x_3834; 
lean_dec(x_3828);
x_3833 = lean_box(0);
if (lean_is_scalar(x_3830)) {
 x_3834 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3834 = x_3830;
 lean_ctor_set_tag(x_3834, 0);
}
lean_ctor_set(x_3834, 0, x_3833);
lean_ctor_set(x_3834, 1, x_3829);
return x_3834;
}
else
{
lean_object* x_3835; 
if (lean_is_scalar(x_3830)) {
 x_3835 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3835 = x_3830;
}
lean_ctor_set(x_3835, 0, x_3828);
lean_ctor_set(x_3835, 1, x_3829);
return x_3835;
}
}
else
{
lean_object* x_3836; 
if (lean_is_scalar(x_3830)) {
 x_3836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3836 = x_3830;
}
lean_ctor_set(x_3836, 0, x_3828);
lean_ctor_set(x_3836, 1, x_3829);
return x_3836;
}
}
}
}
else
{
lean_object* x_3837; lean_object* x_3838; 
lean_dec(x_3538);
lean_dec(x_19);
x_3837 = lean_ctor_get(x_3568, 1);
lean_inc(x_3837);
lean_dec(x_3568);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3838 = l_Lean_Meta_isMonad_x3f(x_3549, x_3, x_4, x_5, x_6, x_3837);
if (lean_obj_tag(x_3838) == 0)
{
lean_object* x_3839; 
x_3839 = lean_ctor_get(x_3838, 0);
lean_inc(x_3839);
if (lean_obj_tag(x_3839) == 0)
{
lean_object* x_3840; lean_object* x_3841; lean_object* x_3842; lean_object* x_3843; lean_object* x_3844; lean_object* x_3845; 
lean_dec(x_3567);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3547);
lean_free_object(x_17);
lean_dec(x_1);
x_3840 = lean_ctor_get(x_3838, 1);
lean_inc(x_3840);
lean_dec(x_3838);
x_3841 = l_Lean_Meta_SavedState_restore(x_3565, x_3, x_4, x_5, x_6, x_3840);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_3565);
x_3842 = lean_ctor_get(x_3841, 1);
lean_inc(x_3842);
if (lean_is_exclusive(x_3841)) {
 lean_ctor_release(x_3841, 0);
 lean_ctor_release(x_3841, 1);
 x_3843 = x_3841;
} else {
 lean_dec_ref(x_3841);
 x_3843 = lean_box(0);
}
x_3844 = lean_box(0);
if (lean_is_scalar(x_3843)) {
 x_3845 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3845 = x_3843;
}
lean_ctor_set(x_3845, 0, x_3844);
lean_ctor_set(x_3845, 1, x_3842);
return x_3845;
}
else
{
lean_object* x_3846; lean_object* x_3847; lean_object* x_3848; lean_object* x_3849; lean_object* x_3850; lean_object* x_3851; lean_object* x_3852; lean_object* x_3853; lean_object* x_3854; lean_object* x_3855; lean_object* x_3856; lean_object* x_3857; lean_object* x_3858; lean_object* x_3859; lean_object* x_3860; lean_object* x_3861; lean_object* x_3862; lean_object* x_3863; lean_object* x_3864; lean_object* x_3874; lean_object* x_3875; 
x_3846 = lean_ctor_get(x_3838, 1);
lean_inc(x_3846);
if (lean_is_exclusive(x_3838)) {
 lean_ctor_release(x_3838, 0);
 lean_ctor_release(x_3838, 1);
 x_3847 = x_3838;
} else {
 lean_dec_ref(x_3838);
 x_3847 = lean_box(0);
}
x_3848 = lean_ctor_get(x_3839, 0);
lean_inc(x_3848);
if (lean_is_exclusive(x_3839)) {
 lean_ctor_release(x_3839, 0);
 x_3849 = x_3839;
} else {
 lean_dec_ref(x_3839);
 x_3849 = lean_box(0);
}
if (lean_is_scalar(x_3849)) {
 x_3850 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3850 = x_3849;
}
lean_ctor_set(x_3850, 0, x_3561);
if (lean_is_scalar(x_3559)) {
 x_3851 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3851 = x_3559;
}
lean_ctor_set(x_3851, 0, x_3562);
if (lean_is_scalar(x_3547)) {
 x_3852 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3852 = x_3547;
}
lean_ctor_set(x_3852, 0, x_3550);
x_3853 = lean_box(0);
x_3854 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3854, 0, x_3848);
x_3855 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3855, 0, x_1);
x_3856 = lean_box(0);
if (lean_is_scalar(x_3567)) {
 x_3857 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3857 = x_3567;
 lean_ctor_set_tag(x_3857, 1);
}
lean_ctor_set(x_3857, 0, x_3855);
lean_ctor_set(x_3857, 1, x_3856);
if (lean_is_scalar(x_3563)) {
 x_3858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3858 = x_3563;
 lean_ctor_set_tag(x_3858, 1);
}
lean_ctor_set(x_3858, 0, x_3854);
lean_ctor_set(x_3858, 1, x_3857);
if (lean_is_scalar(x_3551)) {
 x_3859 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3859 = x_3551;
 lean_ctor_set_tag(x_3859, 1);
}
lean_ctor_set(x_3859, 0, x_3853);
lean_ctor_set(x_3859, 1, x_3858);
x_3860 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3860, 0, x_3852);
lean_ctor_set(x_3860, 1, x_3859);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_3860);
lean_ctor_set(x_17, 0, x_3851);
x_3861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3861, 0, x_3850);
lean_ctor_set(x_3861, 1, x_17);
x_3862 = lean_array_mk(x_3861);
x_3874 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3875 = l_Lean_Meta_mkAppOptM(x_3874, x_3862, x_3, x_4, x_5, x_6, x_3846);
if (lean_obj_tag(x_3875) == 0)
{
lean_object* x_3876; lean_object* x_3877; lean_object* x_3878; 
x_3876 = lean_ctor_get(x_3875, 0);
lean_inc(x_3876);
x_3877 = lean_ctor_get(x_3875, 1);
lean_inc(x_3877);
lean_dec(x_3875);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3878 = l_Lean_Meta_expandCoe(x_3876, x_3, x_4, x_5, x_6, x_3877);
if (lean_obj_tag(x_3878) == 0)
{
lean_object* x_3879; lean_object* x_3880; lean_object* x_3881; lean_object* x_3882; lean_object* x_3883; 
lean_dec(x_3847);
lean_dec(x_3565);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_3879 = lean_ctor_get(x_3878, 0);
lean_inc(x_3879);
x_3880 = lean_ctor_get(x_3878, 1);
lean_inc(x_3880);
if (lean_is_exclusive(x_3878)) {
 lean_ctor_release(x_3878, 0);
 lean_ctor_release(x_3878, 1);
 x_3881 = x_3878;
} else {
 lean_dec_ref(x_3878);
 x_3881 = lean_box(0);
}
x_3882 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3882, 0, x_3879);
if (lean_is_scalar(x_3881)) {
 x_3883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3883 = x_3881;
}
lean_ctor_set(x_3883, 0, x_3882);
lean_ctor_set(x_3883, 1, x_3880);
return x_3883;
}
else
{
lean_object* x_3884; lean_object* x_3885; 
x_3884 = lean_ctor_get(x_3878, 0);
lean_inc(x_3884);
x_3885 = lean_ctor_get(x_3878, 1);
lean_inc(x_3885);
lean_dec(x_3878);
x_3863 = x_3884;
x_3864 = x_3885;
goto block_3873;
}
}
else
{
lean_object* x_3886; lean_object* x_3887; 
x_3886 = lean_ctor_get(x_3875, 0);
lean_inc(x_3886);
x_3887 = lean_ctor_get(x_3875, 1);
lean_inc(x_3887);
lean_dec(x_3875);
x_3863 = x_3886;
x_3864 = x_3887;
goto block_3873;
}
block_3873:
{
uint8_t x_3865; 
x_3865 = l_Lean_Exception_isInterrupt(x_3863);
if (x_3865 == 0)
{
uint8_t x_3866; 
x_3866 = l_Lean_Exception_isRuntime(x_3863);
if (x_3866 == 0)
{
lean_object* x_3867; lean_object* x_3868; lean_object* x_3869; lean_object* x_3870; 
lean_dec(x_3863);
lean_dec(x_3847);
x_3867 = l_Lean_Meta_SavedState_restore(x_3565, x_3, x_4, x_5, x_6, x_3864);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_3565);
x_3868 = lean_ctor_get(x_3867, 1);
lean_inc(x_3868);
if (lean_is_exclusive(x_3867)) {
 lean_ctor_release(x_3867, 0);
 lean_ctor_release(x_3867, 1);
 x_3869 = x_3867;
} else {
 lean_dec_ref(x_3867);
 x_3869 = lean_box(0);
}
if (lean_is_scalar(x_3869)) {
 x_3870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3870 = x_3869;
}
lean_ctor_set(x_3870, 0, x_3853);
lean_ctor_set(x_3870, 1, x_3868);
return x_3870;
}
else
{
lean_object* x_3871; 
lean_dec(x_3565);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_3847)) {
 x_3871 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3871 = x_3847;
 lean_ctor_set_tag(x_3871, 1);
}
lean_ctor_set(x_3871, 0, x_3863);
lean_ctor_set(x_3871, 1, x_3864);
return x_3871;
}
}
else
{
lean_object* x_3872; 
lean_dec(x_3565);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_3847)) {
 x_3872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3872 = x_3847;
 lean_ctor_set_tag(x_3872, 1);
}
lean_ctor_set(x_3872, 0, x_3863);
lean_ctor_set(x_3872, 1, x_3864);
return x_3872;
}
}
}
}
else
{
lean_object* x_3888; lean_object* x_3889; lean_object* x_3890; lean_object* x_3891; 
lean_dec(x_3567);
lean_dec(x_3565);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3547);
lean_free_object(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3888 = lean_ctor_get(x_3838, 0);
lean_inc(x_3888);
x_3889 = lean_ctor_get(x_3838, 1);
lean_inc(x_3889);
if (lean_is_exclusive(x_3838)) {
 lean_ctor_release(x_3838, 0);
 lean_ctor_release(x_3838, 1);
 x_3890 = x_3838;
} else {
 lean_dec_ref(x_3838);
 x_3890 = lean_box(0);
}
if (lean_is_scalar(x_3890)) {
 x_3891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3891 = x_3890;
}
lean_ctor_set(x_3891, 0, x_3888);
lean_ctor_set(x_3891, 1, x_3889);
return x_3891;
}
}
}
else
{
lean_object* x_3892; lean_object* x_3893; lean_object* x_3894; lean_object* x_3895; 
lean_dec(x_3567);
lean_dec(x_3565);
lean_dec(x_3563);
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3559);
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3547);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3892 = lean_ctor_get(x_3568, 0);
lean_inc(x_3892);
x_3893 = lean_ctor_get(x_3568, 1);
lean_inc(x_3893);
if (lean_is_exclusive(x_3568)) {
 lean_ctor_release(x_3568, 0);
 lean_ctor_release(x_3568, 1);
 x_3894 = x_3568;
} else {
 lean_dec_ref(x_3568);
 x_3894 = lean_box(0);
}
if (lean_is_scalar(x_3894)) {
 x_3895 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3895 = x_3894;
}
lean_ctor_set(x_3895, 0, x_3892);
lean_ctor_set(x_3895, 1, x_3893);
return x_3895;
}
}
}
else
{
lean_object* x_3896; lean_object* x_3897; lean_object* x_3898; lean_object* x_3899; 
lean_dec(x_3551);
lean_dec(x_3550);
lean_dec(x_3549);
lean_dec(x_3547);
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3896 = lean_ctor_get(x_3552, 0);
lean_inc(x_3896);
x_3897 = lean_ctor_get(x_3552, 1);
lean_inc(x_3897);
if (lean_is_exclusive(x_3552)) {
 lean_ctor_release(x_3552, 0);
 lean_ctor_release(x_3552, 1);
 x_3898 = x_3552;
} else {
 lean_dec_ref(x_3552);
 x_3898 = lean_box(0);
}
if (lean_is_scalar(x_3898)) {
 x_3899 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3899 = x_3898;
}
lean_ctor_set(x_3899, 0, x_3896);
lean_ctor_set(x_3899, 1, x_3897);
return x_3899;
}
}
}
else
{
lean_object* x_3900; lean_object* x_3901; lean_object* x_3902; lean_object* x_3903; 
lean_dec(x_3538);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3900 = lean_ctor_get(x_3540, 0);
lean_inc(x_3900);
x_3901 = lean_ctor_get(x_3540, 1);
lean_inc(x_3901);
if (lean_is_exclusive(x_3540)) {
 lean_ctor_release(x_3540, 0);
 lean_ctor_release(x_3540, 1);
 x_3902 = x_3540;
} else {
 lean_dec_ref(x_3540);
 x_3902 = lean_box(0);
}
if (lean_is_scalar(x_3902)) {
 x_3903 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3903 = x_3902;
}
lean_ctor_set(x_3903, 0, x_3900);
lean_ctor_set(x_3903, 1, x_3901);
return x_3903;
}
}
}
else
{
uint8_t x_3904; 
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3904 = !lean_is_exclusive(x_21);
if (x_3904 == 0)
{
return x_21;
}
else
{
lean_object* x_3905; lean_object* x_3906; lean_object* x_3907; 
x_3905 = lean_ctor_get(x_21, 0);
x_3906 = lean_ctor_get(x_21, 1);
lean_inc(x_3906);
lean_inc(x_3905);
lean_dec(x_21);
x_3907 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3907, 0, x_3905);
lean_ctor_set(x_3907, 1, x_3906);
return x_3907;
}
}
}
else
{
lean_object* x_3908; lean_object* x_3909; lean_object* x_3910; 
x_3908 = lean_ctor_get(x_17, 0);
x_3909 = lean_ctor_get(x_17, 1);
lean_inc(x_3909);
lean_inc(x_3908);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_3910 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_3909);
if (lean_obj_tag(x_3910) == 0)
{
lean_object* x_3911; lean_object* x_3912; lean_object* x_3913; lean_object* x_3914; lean_object* x_3915; lean_object* x_3916; lean_object* x_3917; 
x_3911 = lean_ctor_get(x_3910, 0);
lean_inc(x_3911);
x_3912 = lean_ctor_get(x_3910, 1);
lean_inc(x_3912);
lean_dec(x_3910);
x_3913 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_3911, x_3, x_4, x_5, x_6, x_3912);
x_3914 = lean_ctor_get(x_3913, 0);
lean_inc(x_3914);
x_3915 = lean_ctor_get(x_3913, 1);
lean_inc(x_3915);
if (lean_is_exclusive(x_3913)) {
 lean_ctor_release(x_3913, 0);
 lean_ctor_release(x_3913, 1);
 x_3916 = x_3913;
} else {
 lean_dec_ref(x_3913);
 x_3916 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3908);
x_3917 = l_Lean_Meta_isTypeApp_x3f(x_3908, x_3, x_4, x_5, x_6, x_3915);
if (lean_obj_tag(x_3917) == 0)
{
lean_object* x_3918; 
x_3918 = lean_ctor_get(x_3917, 0);
lean_inc(x_3918);
if (lean_obj_tag(x_3918) == 0)
{
lean_object* x_3919; lean_object* x_3920; lean_object* x_3921; lean_object* x_3922; 
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3919 = lean_ctor_get(x_3917, 1);
lean_inc(x_3919);
if (lean_is_exclusive(x_3917)) {
 lean_ctor_release(x_3917, 0);
 lean_ctor_release(x_3917, 1);
 x_3920 = x_3917;
} else {
 lean_dec_ref(x_3917);
 x_3920 = lean_box(0);
}
x_3921 = lean_box(0);
if (lean_is_scalar(x_3920)) {
 x_3922 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3922 = x_3920;
}
lean_ctor_set(x_3922, 0, x_3921);
lean_ctor_set(x_3922, 1, x_3919);
return x_3922;
}
else
{
lean_object* x_3923; lean_object* x_3924; lean_object* x_3925; lean_object* x_3926; lean_object* x_3927; lean_object* x_3928; lean_object* x_3929; 
x_3923 = lean_ctor_get(x_3918, 0);
lean_inc(x_3923);
if (lean_is_exclusive(x_3918)) {
 lean_ctor_release(x_3918, 0);
 x_3924 = x_3918;
} else {
 lean_dec_ref(x_3918);
 x_3924 = lean_box(0);
}
x_3925 = lean_ctor_get(x_3917, 1);
lean_inc(x_3925);
lean_dec(x_3917);
x_3926 = lean_ctor_get(x_3923, 0);
lean_inc(x_3926);
x_3927 = lean_ctor_get(x_3923, 1);
lean_inc(x_3927);
if (lean_is_exclusive(x_3923)) {
 lean_ctor_release(x_3923, 0);
 lean_ctor_release(x_3923, 1);
 x_3928 = x_3923;
} else {
 lean_dec_ref(x_3923);
 x_3928 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3914);
x_3929 = l_Lean_Meta_isTypeApp_x3f(x_3914, x_3, x_4, x_5, x_6, x_3925);
if (lean_obj_tag(x_3929) == 0)
{
lean_object* x_3930; 
x_3930 = lean_ctor_get(x_3929, 0);
lean_inc(x_3930);
if (lean_obj_tag(x_3930) == 0)
{
lean_object* x_3931; lean_object* x_3932; lean_object* x_3933; lean_object* x_3934; 
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3924);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3931 = lean_ctor_get(x_3929, 1);
lean_inc(x_3931);
if (lean_is_exclusive(x_3929)) {
 lean_ctor_release(x_3929, 0);
 lean_ctor_release(x_3929, 1);
 x_3932 = x_3929;
} else {
 lean_dec_ref(x_3929);
 x_3932 = lean_box(0);
}
x_3933 = lean_box(0);
if (lean_is_scalar(x_3932)) {
 x_3934 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3934 = x_3932;
}
lean_ctor_set(x_3934, 0, x_3933);
lean_ctor_set(x_3934, 1, x_3931);
return x_3934;
}
else
{
lean_object* x_3935; lean_object* x_3936; lean_object* x_3937; lean_object* x_3938; lean_object* x_3939; lean_object* x_3940; lean_object* x_3941; lean_object* x_3942; lean_object* x_3943; lean_object* x_3944; lean_object* x_3945; 
x_3935 = lean_ctor_get(x_3930, 0);
lean_inc(x_3935);
if (lean_is_exclusive(x_3930)) {
 lean_ctor_release(x_3930, 0);
 x_3936 = x_3930;
} else {
 lean_dec_ref(x_3930);
 x_3936 = lean_box(0);
}
x_3937 = lean_ctor_get(x_3929, 1);
lean_inc(x_3937);
lean_dec(x_3929);
x_3938 = lean_ctor_get(x_3935, 0);
lean_inc(x_3938);
x_3939 = lean_ctor_get(x_3935, 1);
lean_inc(x_3939);
if (lean_is_exclusive(x_3935)) {
 lean_ctor_release(x_3935, 0);
 lean_ctor_release(x_3935, 1);
 x_3940 = x_3935;
} else {
 lean_dec_ref(x_3935);
 x_3940 = lean_box(0);
}
x_3941 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_3937);
x_3942 = lean_ctor_get(x_3941, 0);
lean_inc(x_3942);
x_3943 = lean_ctor_get(x_3941, 1);
lean_inc(x_3943);
if (lean_is_exclusive(x_3941)) {
 lean_ctor_release(x_3941, 0);
 lean_ctor_release(x_3941, 1);
 x_3944 = x_3941;
} else {
 lean_dec_ref(x_3941);
 x_3944 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3926);
lean_inc(x_3938);
x_3945 = l_Lean_Meta_isExprDefEq(x_3938, x_3926, x_3, x_4, x_5, x_6, x_3943);
if (lean_obj_tag(x_3945) == 0)
{
lean_object* x_3946; uint8_t x_3947; 
x_3946 = lean_ctor_get(x_3945, 0);
lean_inc(x_3946);
x_3947 = lean_unbox(x_3946);
lean_dec(x_3946);
if (x_3947 == 0)
{
lean_object* x_3948; lean_object* x_3949; lean_object* x_3950; lean_object* x_3951; uint8_t x_3952; 
lean_dec(x_3942);
lean_dec(x_3924);
x_3948 = lean_ctor_get(x_3945, 1);
lean_inc(x_3948);
if (lean_is_exclusive(x_3945)) {
 lean_ctor_release(x_3945, 0);
 lean_ctor_release(x_3945, 1);
 x_3949 = x_3945;
} else {
 lean_dec_ref(x_3945);
 x_3949 = lean_box(0);
}
x_3950 = lean_ctor_get(x_5, 2);
lean_inc(x_3950);
x_3951 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_3952 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_3950, x_3951);
lean_dec(x_3950);
if (x_3952 == 0)
{
lean_object* x_3953; lean_object* x_3954; 
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3953 = lean_box(0);
if (lean_is_scalar(x_3949)) {
 x_3954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3954 = x_3949;
}
lean_ctor_set(x_3954, 0, x_3953);
lean_ctor_set(x_3954, 1, x_3948);
return x_3954;
}
else
{
lean_object* x_3955; 
lean_dec(x_3949);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3938);
x_3955 = lean_infer_type(x_3938, x_3, x_4, x_5, x_6, x_3948);
if (lean_obj_tag(x_3955) == 0)
{
lean_object* x_3956; lean_object* x_3957; lean_object* x_3958; 
x_3956 = lean_ctor_get(x_3955, 0);
lean_inc(x_3956);
x_3957 = lean_ctor_get(x_3955, 1);
lean_inc(x_3957);
lean_dec(x_3955);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3958 = lean_whnf(x_3956, x_3, x_4, x_5, x_6, x_3957);
if (lean_obj_tag(x_3958) == 0)
{
lean_object* x_3959; 
x_3959 = lean_ctor_get(x_3958, 0);
lean_inc(x_3959);
if (lean_obj_tag(x_3959) == 7)
{
lean_object* x_3960; 
x_3960 = lean_ctor_get(x_3959, 1);
lean_inc(x_3960);
if (lean_obj_tag(x_3960) == 3)
{
lean_object* x_3961; 
x_3961 = lean_ctor_get(x_3959, 2);
lean_inc(x_3961);
lean_dec(x_3959);
if (lean_obj_tag(x_3961) == 3)
{
lean_object* x_3962; lean_object* x_3963; lean_object* x_3964; lean_object* x_3965; 
x_3962 = lean_ctor_get(x_3958, 1);
lean_inc(x_3962);
lean_dec(x_3958);
x_3963 = lean_ctor_get(x_3960, 0);
lean_inc(x_3963);
lean_dec(x_3960);
x_3964 = lean_ctor_get(x_3961, 0);
lean_inc(x_3964);
lean_dec(x_3961);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3926);
x_3965 = lean_infer_type(x_3926, x_3, x_4, x_5, x_6, x_3962);
if (lean_obj_tag(x_3965) == 0)
{
lean_object* x_3966; lean_object* x_3967; lean_object* x_3968; 
x_3966 = lean_ctor_get(x_3965, 0);
lean_inc(x_3966);
x_3967 = lean_ctor_get(x_3965, 1);
lean_inc(x_3967);
lean_dec(x_3965);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_3968 = lean_whnf(x_3966, x_3, x_4, x_5, x_6, x_3967);
if (lean_obj_tag(x_3968) == 0)
{
lean_object* x_3969; 
x_3969 = lean_ctor_get(x_3968, 0);
lean_inc(x_3969);
if (lean_obj_tag(x_3969) == 7)
{
lean_object* x_3970; 
x_3970 = lean_ctor_get(x_3969, 1);
lean_inc(x_3970);
if (lean_obj_tag(x_3970) == 3)
{
lean_object* x_3971; 
x_3971 = lean_ctor_get(x_3969, 2);
lean_inc(x_3971);
lean_dec(x_3969);
if (lean_obj_tag(x_3971) == 3)
{
lean_object* x_3972; lean_object* x_3973; lean_object* x_3974; lean_object* x_3975; 
x_3972 = lean_ctor_get(x_3968, 1);
lean_inc(x_3972);
lean_dec(x_3968);
x_3973 = lean_ctor_get(x_3970, 0);
lean_inc(x_3973);
lean_dec(x_3970);
x_3974 = lean_ctor_get(x_3971, 0);
lean_inc(x_3974);
lean_dec(x_3971);
x_3975 = l_Lean_Meta_decLevel(x_3963, x_3, x_4, x_5, x_6, x_3972);
if (lean_obj_tag(x_3975) == 0)
{
lean_object* x_3976; lean_object* x_3977; lean_object* x_3978; lean_object* x_3979; 
x_3976 = lean_ctor_get(x_3975, 0);
lean_inc(x_3976);
x_3977 = lean_ctor_get(x_3975, 1);
lean_inc(x_3977);
if (lean_is_exclusive(x_3975)) {
 lean_ctor_release(x_3975, 0);
 lean_ctor_release(x_3975, 1);
 x_3978 = x_3975;
} else {
 lean_dec_ref(x_3975);
 x_3978 = lean_box(0);
}
x_3979 = l_Lean_Meta_decLevel(x_3973, x_3, x_4, x_5, x_6, x_3977);
if (lean_obj_tag(x_3979) == 0)
{
lean_object* x_3980; lean_object* x_3981; lean_object* x_3982; uint8_t x_3983; lean_object* x_3984; 
x_3980 = lean_ctor_get(x_3979, 0);
lean_inc(x_3980);
x_3981 = lean_ctor_get(x_3979, 1);
lean_inc(x_3981);
if (lean_is_exclusive(x_3979)) {
 lean_ctor_release(x_3979, 0);
 lean_ctor_release(x_3979, 1);
 x_3982 = x_3979;
} else {
 lean_dec_ref(x_3979);
 x_3982 = lean_box(0);
}
x_3983 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3976);
x_3984 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_3976, x_3980, x_3983, x_3, x_4, x_5, x_6, x_3981);
if (lean_obj_tag(x_3984) == 0)
{
lean_object* x_3985; uint8_t x_3986; 
x_3985 = lean_ctor_get(x_3984, 0);
lean_inc(x_3985);
x_3986 = lean_unbox(x_3985);
lean_dec(x_3985);
if (x_3986 == 0)
{
lean_object* x_3987; lean_object* x_3988; lean_object* x_3989; lean_object* x_3990; 
lean_dec(x_3982);
lean_dec(x_3978);
lean_dec(x_3976);
lean_dec(x_3974);
lean_dec(x_3964);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_3987 = lean_ctor_get(x_3984, 1);
lean_inc(x_3987);
if (lean_is_exclusive(x_3984)) {
 lean_ctor_release(x_3984, 0);
 lean_ctor_release(x_3984, 1);
 x_3988 = x_3984;
} else {
 lean_dec_ref(x_3984);
 x_3988 = lean_box(0);
}
x_3989 = lean_box(0);
if (lean_is_scalar(x_3988)) {
 x_3990 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3990 = x_3988;
}
lean_ctor_set(x_3990, 0, x_3989);
lean_ctor_set(x_3990, 1, x_3987);
return x_3990;
}
else
{
lean_object* x_3991; lean_object* x_3992; 
x_3991 = lean_ctor_get(x_3984, 1);
lean_inc(x_3991);
lean_dec(x_3984);
x_3992 = l_Lean_Meta_decLevel(x_3964, x_3, x_4, x_5, x_6, x_3991);
if (lean_obj_tag(x_3992) == 0)
{
lean_object* x_3993; lean_object* x_3994; lean_object* x_3995; lean_object* x_3996; 
x_3993 = lean_ctor_get(x_3992, 0);
lean_inc(x_3993);
x_3994 = lean_ctor_get(x_3992, 1);
lean_inc(x_3994);
if (lean_is_exclusive(x_3992)) {
 lean_ctor_release(x_3992, 0);
 lean_ctor_release(x_3992, 1);
 x_3995 = x_3992;
} else {
 lean_dec_ref(x_3992);
 x_3995 = lean_box(0);
}
x_3996 = l_Lean_Meta_decLevel(x_3974, x_3, x_4, x_5, x_6, x_3994);
if (lean_obj_tag(x_3996) == 0)
{
lean_object* x_3997; lean_object* x_3998; lean_object* x_3999; lean_object* x_4000; lean_object* x_4001; lean_object* x_4002; lean_object* x_4003; lean_object* x_4004; lean_object* x_4005; lean_object* x_4006; lean_object* x_4007; lean_object* x_4008; lean_object* x_4009; lean_object* x_4010; lean_object* x_4011; 
x_3997 = lean_ctor_get(x_3996, 0);
lean_inc(x_3997);
x_3998 = lean_ctor_get(x_3996, 1);
lean_inc(x_3998);
if (lean_is_exclusive(x_3996)) {
 lean_ctor_release(x_3996, 0);
 lean_ctor_release(x_3996, 1);
 x_3999 = x_3996;
} else {
 lean_dec_ref(x_3996);
 x_3999 = lean_box(0);
}
x_4000 = lean_box(0);
if (lean_is_scalar(x_3999)) {
 x_4001 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4001 = x_3999;
 lean_ctor_set_tag(x_4001, 1);
}
lean_ctor_set(x_4001, 0, x_3997);
lean_ctor_set(x_4001, 1, x_4000);
if (lean_is_scalar(x_3995)) {
 x_4002 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4002 = x_3995;
 lean_ctor_set_tag(x_4002, 1);
}
lean_ctor_set(x_4002, 0, x_3993);
lean_ctor_set(x_4002, 1, x_4001);
if (lean_is_scalar(x_3982)) {
 x_4003 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4003 = x_3982;
 lean_ctor_set_tag(x_4003, 1);
}
lean_ctor_set(x_4003, 0, x_3976);
lean_ctor_set(x_4003, 1, x_4002);
x_4004 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_4005 = l_Lean_Expr_const___override(x_4004, x_4003);
lean_inc(x_3926);
if (lean_is_scalar(x_3978)) {
 x_4006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4006 = x_3978;
 lean_ctor_set_tag(x_4006, 1);
}
lean_ctor_set(x_4006, 0, x_3926);
lean_ctor_set(x_4006, 1, x_4000);
lean_inc(x_3938);
if (lean_is_scalar(x_3944)) {
 x_4007 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4007 = x_3944;
 lean_ctor_set_tag(x_4007, 1);
}
lean_ctor_set(x_4007, 0, x_3938);
lean_ctor_set(x_4007, 1, x_4006);
x_4008 = lean_array_mk(x_4007);
x_4009 = l_Lean_mkAppN(x_4005, x_4008);
lean_dec(x_4008);
x_4010 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4011 = l_Lean_Meta_trySynthInstance(x_4009, x_4010, x_3, x_4, x_5, x_6, x_3998);
if (lean_obj_tag(x_4011) == 0)
{
lean_object* x_4012; 
x_4012 = lean_ctor_get(x_4011, 0);
lean_inc(x_4012);
if (lean_obj_tag(x_4012) == 1)
{
lean_object* x_4013; lean_object* x_4014; lean_object* x_4015; 
x_4013 = lean_ctor_get(x_4011, 1);
lean_inc(x_4013);
lean_dec(x_4011);
x_4014 = lean_ctor_get(x_4012, 0);
lean_inc(x_4014);
lean_dec(x_4012);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3939);
x_4015 = l_Lean_Meta_getDecLevel(x_3939, x_3, x_4, x_5, x_6, x_4013);
if (lean_obj_tag(x_4015) == 0)
{
lean_object* x_4016; lean_object* x_4017; lean_object* x_4018; lean_object* x_4019; 
x_4016 = lean_ctor_get(x_4015, 0);
lean_inc(x_4016);
x_4017 = lean_ctor_get(x_4015, 1);
lean_inc(x_4017);
if (lean_is_exclusive(x_4015)) {
 lean_ctor_release(x_4015, 0);
 lean_ctor_release(x_4015, 1);
 x_4018 = x_4015;
} else {
 lean_dec_ref(x_4015);
 x_4018 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4019 = l_Lean_Meta_getDecLevel(x_3914, x_3, x_4, x_5, x_6, x_4017);
if (lean_obj_tag(x_4019) == 0)
{
lean_object* x_4020; lean_object* x_4021; lean_object* x_4022; lean_object* x_4023; 
x_4020 = lean_ctor_get(x_4019, 0);
lean_inc(x_4020);
x_4021 = lean_ctor_get(x_4019, 1);
lean_inc(x_4021);
if (lean_is_exclusive(x_4019)) {
 lean_ctor_release(x_4019, 0);
 lean_ctor_release(x_4019, 1);
 x_4022 = x_4019;
} else {
 lean_dec_ref(x_4019);
 x_4022 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3908);
x_4023 = l_Lean_Meta_getDecLevel(x_3908, x_3, x_4, x_5, x_6, x_4021);
if (lean_obj_tag(x_4023) == 0)
{
lean_object* x_4024; lean_object* x_4025; lean_object* x_4026; lean_object* x_4027; lean_object* x_4028; lean_object* x_4029; lean_object* x_4030; lean_object* x_4031; lean_object* x_4032; lean_object* x_4033; lean_object* x_4034; lean_object* x_4035; lean_object* x_4036; lean_object* x_4037; lean_object* x_4038; lean_object* x_4039; 
x_4024 = lean_ctor_get(x_4023, 0);
lean_inc(x_4024);
x_4025 = lean_ctor_get(x_4023, 1);
lean_inc(x_4025);
if (lean_is_exclusive(x_4023)) {
 lean_ctor_release(x_4023, 0);
 lean_ctor_release(x_4023, 1);
 x_4026 = x_4023;
} else {
 lean_dec_ref(x_4023);
 x_4026 = lean_box(0);
}
if (lean_is_scalar(x_4026)) {
 x_4027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4027 = x_4026;
 lean_ctor_set_tag(x_4027, 1);
}
lean_ctor_set(x_4027, 0, x_4024);
lean_ctor_set(x_4027, 1, x_4000);
if (lean_is_scalar(x_4022)) {
 x_4028 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4028 = x_4022;
 lean_ctor_set_tag(x_4028, 1);
}
lean_ctor_set(x_4028, 0, x_4020);
lean_ctor_set(x_4028, 1, x_4027);
if (lean_is_scalar(x_4018)) {
 x_4029 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4029 = x_4018;
 lean_ctor_set_tag(x_4029, 1);
}
lean_ctor_set(x_4029, 0, x_4016);
lean_ctor_set(x_4029, 1, x_4028);
x_4030 = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
lean_inc(x_4029);
x_4031 = l_Lean_Expr_const___override(x_4030, x_4029);
if (lean_is_scalar(x_3940)) {
 x_4032 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4032 = x_3940;
 lean_ctor_set_tag(x_4032, 1);
}
lean_ctor_set(x_4032, 0, x_1);
lean_ctor_set(x_4032, 1, x_4000);
lean_inc(x_4032);
lean_inc(x_3939);
if (lean_is_scalar(x_3928)) {
 x_4033 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4033 = x_3928;
 lean_ctor_set_tag(x_4033, 1);
}
lean_ctor_set(x_4033, 0, x_3939);
lean_ctor_set(x_4033, 1, x_4032);
lean_inc(x_4014);
if (lean_is_scalar(x_3916)) {
 x_4034 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4034 = x_3916;
 lean_ctor_set_tag(x_4034, 1);
}
lean_ctor_set(x_4034, 0, x_4014);
lean_ctor_set(x_4034, 1, x_4033);
lean_inc(x_3926);
x_4035 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4035, 0, x_3926);
lean_ctor_set(x_4035, 1, x_4034);
lean_inc(x_3938);
x_4036 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4036, 0, x_3938);
lean_ctor_set(x_4036, 1, x_4035);
x_4037 = lean_array_mk(x_4036);
x_4038 = l_Lean_mkAppN(x_4031, x_4037);
lean_dec(x_4037);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4038);
x_4039 = lean_infer_type(x_4038, x_3, x_4, x_5, x_6, x_4025);
if (lean_obj_tag(x_4039) == 0)
{
lean_object* x_4040; lean_object* x_4041; lean_object* x_4042; lean_object* x_4043; 
x_4040 = lean_ctor_get(x_4039, 0);
lean_inc(x_4040);
x_4041 = lean_ctor_get(x_4039, 1);
lean_inc(x_4041);
if (lean_is_exclusive(x_4039)) {
 lean_ctor_release(x_4039, 0);
 lean_ctor_release(x_4039, 1);
 x_4042 = x_4039;
} else {
 lean_dec_ref(x_4039);
 x_4042 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3908);
x_4043 = l_Lean_Meta_isExprDefEq(x_3908, x_4040, x_3, x_4, x_5, x_6, x_4041);
if (lean_obj_tag(x_4043) == 0)
{
lean_object* x_4044; uint8_t x_4045; 
x_4044 = lean_ctor_get(x_4043, 0);
lean_inc(x_4044);
x_4045 = lean_unbox(x_4044);
lean_dec(x_4044);
if (x_4045 == 0)
{
lean_object* x_4046; lean_object* x_4047; 
lean_dec(x_4038);
lean_dec(x_3936);
x_4046 = lean_ctor_get(x_4043, 1);
lean_inc(x_4046);
lean_dec(x_4043);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3926);
x_4047 = l_Lean_Meta_isMonad_x3f(x_3926, x_3, x_4, x_5, x_6, x_4046);
if (lean_obj_tag(x_4047) == 0)
{
lean_object* x_4048; 
x_4048 = lean_ctor_get(x_4047, 0);
lean_inc(x_4048);
if (lean_obj_tag(x_4048) == 0)
{
lean_object* x_4049; lean_object* x_4050; lean_object* x_4051; 
lean_dec(x_4042);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4049 = lean_ctor_get(x_4047, 1);
lean_inc(x_4049);
if (lean_is_exclusive(x_4047)) {
 lean_ctor_release(x_4047, 0);
 lean_ctor_release(x_4047, 1);
 x_4050 = x_4047;
} else {
 lean_dec_ref(x_4047);
 x_4050 = lean_box(0);
}
if (lean_is_scalar(x_4050)) {
 x_4051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4051 = x_4050;
}
lean_ctor_set(x_4051, 0, x_4010);
lean_ctor_set(x_4051, 1, x_4049);
return x_4051;
}
else
{
lean_object* x_4052; lean_object* x_4053; lean_object* x_4054; 
x_4052 = lean_ctor_get(x_4047, 1);
lean_inc(x_4052);
lean_dec(x_4047);
x_4053 = lean_ctor_get(x_4048, 0);
lean_inc(x_4053);
lean_dec(x_4048);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3939);
x_4054 = l_Lean_Meta_getLevel(x_3939, x_3, x_4, x_5, x_6, x_4052);
if (lean_obj_tag(x_4054) == 0)
{
lean_object* x_4055; lean_object* x_4056; lean_object* x_4057; lean_object* x_4058; 
x_4055 = lean_ctor_get(x_4054, 0);
lean_inc(x_4055);
x_4056 = lean_ctor_get(x_4054, 1);
lean_inc(x_4056);
if (lean_is_exclusive(x_4054)) {
 lean_ctor_release(x_4054, 0);
 lean_ctor_release(x_4054, 1);
 x_4057 = x_4054;
} else {
 lean_dec_ref(x_4054);
 x_4057 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_3927);
x_4058 = l_Lean_Meta_getLevel(x_3927, x_3, x_4, x_5, x_6, x_4056);
if (lean_obj_tag(x_4058) == 0)
{
lean_object* x_4059; lean_object* x_4060; lean_object* x_4061; lean_object* x_4062; lean_object* x_4063; lean_object* x_4064; lean_object* x_4065; lean_object* x_4066; lean_object* x_4067; lean_object* x_4068; lean_object* x_4069; lean_object* x_4070; lean_object* x_4071; lean_object* x_4072; uint8_t x_4073; lean_object* x_4074; lean_object* x_4075; 
x_4059 = lean_ctor_get(x_4058, 0);
lean_inc(x_4059);
x_4060 = lean_ctor_get(x_4058, 1);
lean_inc(x_4060);
if (lean_is_exclusive(x_4058)) {
 lean_ctor_release(x_4058, 0);
 lean_ctor_release(x_4058, 1);
 x_4061 = x_4058;
} else {
 lean_dec_ref(x_4058);
 x_4061 = lean_box(0);
}
if (lean_is_scalar(x_4061)) {
 x_4062 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4062 = x_4061;
 lean_ctor_set_tag(x_4062, 1);
}
lean_ctor_set(x_4062, 0, x_4059);
lean_ctor_set(x_4062, 1, x_4000);
if (lean_is_scalar(x_4057)) {
 x_4063 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4063 = x_4057;
 lean_ctor_set_tag(x_4063, 1);
}
lean_ctor_set(x_4063, 0, x_4055);
lean_ctor_set(x_4063, 1, x_4062);
x_4064 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_4065 = l_Lean_Expr_const___override(x_4064, x_4063);
lean_inc(x_3927);
if (lean_is_scalar(x_4042)) {
 x_4066 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4066 = x_4042;
 lean_ctor_set_tag(x_4066, 1);
}
lean_ctor_set(x_4066, 0, x_3927);
lean_ctor_set(x_4066, 1, x_4000);
x_4067 = l_Lean_Meta_coerceMonadLift_x3f___closed__8;
x_4068 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4068, 0, x_4067);
lean_ctor_set(x_4068, 1, x_4066);
lean_inc(x_3939);
x_4069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4069, 0, x_3939);
lean_ctor_set(x_4069, 1, x_4068);
x_4070 = lean_array_mk(x_4069);
x_4071 = l_Lean_mkAppN(x_4065, x_4070);
lean_dec(x_4070);
x_4072 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
x_4073 = 0;
lean_inc(x_3939);
x_4074 = l_Lean_Expr_forallE___override(x_4072, x_3939, x_4071, x_4073);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4075 = l_Lean_Meta_trySynthInstance(x_4074, x_4010, x_3, x_4, x_5, x_6, x_4060);
if (lean_obj_tag(x_4075) == 0)
{
lean_object* x_4076; 
x_4076 = lean_ctor_get(x_4075, 0);
lean_inc(x_4076);
if (lean_obj_tag(x_4076) == 1)
{
lean_object* x_4077; lean_object* x_4078; lean_object* x_4079; lean_object* x_4080; lean_object* x_4081; lean_object* x_4082; lean_object* x_4083; lean_object* x_4084; lean_object* x_4085; lean_object* x_4086; lean_object* x_4087; lean_object* x_4088; lean_object* x_4089; lean_object* x_4090; 
x_4077 = lean_ctor_get(x_4075, 1);
lean_inc(x_4077);
lean_dec(x_4075);
x_4078 = lean_ctor_get(x_4076, 0);
lean_inc(x_4078);
lean_dec(x_4076);
x_4079 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_4080 = l_Lean_Expr_const___override(x_4079, x_4029);
x_4081 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4081, 0, x_4053);
lean_ctor_set(x_4081, 1, x_4032);
x_4082 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4082, 0, x_4078);
lean_ctor_set(x_4082, 1, x_4081);
x_4083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4083, 0, x_4014);
lean_ctor_set(x_4083, 1, x_4082);
x_4084 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4084, 0, x_3927);
lean_ctor_set(x_4084, 1, x_4083);
x_4085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4085, 0, x_3939);
lean_ctor_set(x_4085, 1, x_4084);
x_4086 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4086, 0, x_3926);
lean_ctor_set(x_4086, 1, x_4085);
x_4087 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4087, 0, x_3938);
lean_ctor_set(x_4087, 1, x_4086);
x_4088 = lean_array_mk(x_4087);
x_4089 = l_Lean_mkAppN(x_4080, x_4088);
lean_dec(x_4088);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4090 = l_Lean_Meta_expandCoe(x_4089, x_3, x_4, x_5, x_6, x_4077);
if (lean_obj_tag(x_4090) == 0)
{
lean_object* x_4091; lean_object* x_4092; lean_object* x_4093; 
x_4091 = lean_ctor_get(x_4090, 0);
lean_inc(x_4091);
x_4092 = lean_ctor_get(x_4090, 1);
lean_inc(x_4092);
lean_dec(x_4090);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_4091);
x_4093 = lean_infer_type(x_4091, x_3, x_4, x_5, x_6, x_4092);
if (lean_obj_tag(x_4093) == 0)
{
lean_object* x_4094; lean_object* x_4095; lean_object* x_4096; 
x_4094 = lean_ctor_get(x_4093, 0);
lean_inc(x_4094);
x_4095 = lean_ctor_get(x_4093, 1);
lean_inc(x_4095);
lean_dec(x_4093);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4096 = l_Lean_Meta_isExprDefEq(x_3908, x_4094, x_3, x_4, x_5, x_6, x_4095);
if (lean_obj_tag(x_4096) == 0)
{
lean_object* x_4097; uint8_t x_4098; 
x_4097 = lean_ctor_get(x_4096, 0);
lean_inc(x_4097);
x_4098 = lean_unbox(x_4097);
lean_dec(x_4097);
if (x_4098 == 0)
{
lean_object* x_4099; lean_object* x_4100; lean_object* x_4101; 
lean_dec(x_4091);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4099 = lean_ctor_get(x_4096, 1);
lean_inc(x_4099);
if (lean_is_exclusive(x_4096)) {
 lean_ctor_release(x_4096, 0);
 lean_ctor_release(x_4096, 1);
 x_4100 = x_4096;
} else {
 lean_dec_ref(x_4096);
 x_4100 = lean_box(0);
}
if (lean_is_scalar(x_4100)) {
 x_4101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4101 = x_4100;
}
lean_ctor_set(x_4101, 0, x_4010);
lean_ctor_set(x_4101, 1, x_4099);
return x_4101;
}
else
{
lean_object* x_4102; lean_object* x_4103; lean_object* x_4104; lean_object* x_4105; lean_object* x_4106; lean_object* x_4107; lean_object* x_4108; 
x_4102 = lean_ctor_get(x_4096, 1);
lean_inc(x_4102);
lean_dec(x_4096);
x_4103 = lean_box(0);
x_4104 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_4091, x_4103, x_3, x_4, x_5, x_6, x_4102);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4105 = lean_ctor_get(x_4104, 0);
lean_inc(x_4105);
x_4106 = lean_ctor_get(x_4104, 1);
lean_inc(x_4106);
if (lean_is_exclusive(x_4104)) {
 lean_ctor_release(x_4104, 0);
 lean_ctor_release(x_4104, 1);
 x_4107 = x_4104;
} else {
 lean_dec_ref(x_4104);
 x_4107 = lean_box(0);
}
if (lean_is_scalar(x_4107)) {
 x_4108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4108 = x_4107;
}
lean_ctor_set(x_4108, 0, x_4105);
lean_ctor_set(x_4108, 1, x_4106);
return x_4108;
}
}
else
{
lean_object* x_4109; lean_object* x_4110; 
lean_dec(x_4091);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4109 = lean_ctor_get(x_4096, 0);
lean_inc(x_4109);
x_4110 = lean_ctor_get(x_4096, 1);
lean_inc(x_4110);
lean_dec(x_4096);
x_8 = x_4109;
x_9 = x_4110;
goto block_16;
}
}
else
{
lean_object* x_4111; lean_object* x_4112; 
lean_dec(x_4091);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4111 = lean_ctor_get(x_4093, 0);
lean_inc(x_4111);
x_4112 = lean_ctor_get(x_4093, 1);
lean_inc(x_4112);
lean_dec(x_4093);
x_8 = x_4111;
x_9 = x_4112;
goto block_16;
}
}
else
{
lean_object* x_4113; lean_object* x_4114; 
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4113 = lean_ctor_get(x_4090, 0);
lean_inc(x_4113);
x_4114 = lean_ctor_get(x_4090, 1);
lean_inc(x_4114);
lean_dec(x_4090);
x_8 = x_4113;
x_9 = x_4114;
goto block_16;
}
}
else
{
lean_object* x_4115; lean_object* x_4116; lean_object* x_4117; 
lean_dec(x_4076);
lean_dec(x_4053);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4115 = lean_ctor_get(x_4075, 1);
lean_inc(x_4115);
if (lean_is_exclusive(x_4075)) {
 lean_ctor_release(x_4075, 0);
 lean_ctor_release(x_4075, 1);
 x_4116 = x_4075;
} else {
 lean_dec_ref(x_4075);
 x_4116 = lean_box(0);
}
if (lean_is_scalar(x_4116)) {
 x_4117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4117 = x_4116;
}
lean_ctor_set(x_4117, 0, x_4010);
lean_ctor_set(x_4117, 1, x_4115);
return x_4117;
}
}
else
{
lean_object* x_4118; lean_object* x_4119; 
lean_dec(x_4053);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4118 = lean_ctor_get(x_4075, 0);
lean_inc(x_4118);
x_4119 = lean_ctor_get(x_4075, 1);
lean_inc(x_4119);
lean_dec(x_4075);
x_8 = x_4118;
x_9 = x_4119;
goto block_16;
}
}
else
{
lean_object* x_4120; lean_object* x_4121; 
lean_dec(x_4057);
lean_dec(x_4055);
lean_dec(x_4053);
lean_dec(x_4042);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4120 = lean_ctor_get(x_4058, 0);
lean_inc(x_4120);
x_4121 = lean_ctor_get(x_4058, 1);
lean_inc(x_4121);
lean_dec(x_4058);
x_8 = x_4120;
x_9 = x_4121;
goto block_16;
}
}
else
{
lean_object* x_4122; lean_object* x_4123; 
lean_dec(x_4053);
lean_dec(x_4042);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4122 = lean_ctor_get(x_4054, 0);
lean_inc(x_4122);
x_4123 = lean_ctor_get(x_4054, 1);
lean_inc(x_4123);
lean_dec(x_4054);
x_8 = x_4122;
x_9 = x_4123;
goto block_16;
}
}
}
else
{
lean_object* x_4124; lean_object* x_4125; 
lean_dec(x_4042);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4124 = lean_ctor_get(x_4047, 0);
lean_inc(x_4124);
x_4125 = lean_ctor_get(x_4047, 1);
lean_inc(x_4125);
lean_dec(x_4047);
x_8 = x_4124;
x_9 = x_4125;
goto block_16;
}
}
else
{
lean_object* x_4126; lean_object* x_4127; lean_object* x_4128; lean_object* x_4129; 
lean_dec(x_4042);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4126 = lean_ctor_get(x_4043, 1);
lean_inc(x_4126);
if (lean_is_exclusive(x_4043)) {
 lean_ctor_release(x_4043, 0);
 lean_ctor_release(x_4043, 1);
 x_4127 = x_4043;
} else {
 lean_dec_ref(x_4043);
 x_4127 = lean_box(0);
}
if (lean_is_scalar(x_3936)) {
 x_4128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_4128 = x_3936;
}
lean_ctor_set(x_4128, 0, x_4038);
if (lean_is_scalar(x_4127)) {
 x_4129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4129 = x_4127;
}
lean_ctor_set(x_4129, 0, x_4128);
lean_ctor_set(x_4129, 1, x_4126);
return x_4129;
}
}
else
{
lean_object* x_4130; lean_object* x_4131; 
lean_dec(x_4042);
lean_dec(x_4038);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4130 = lean_ctor_get(x_4043, 0);
lean_inc(x_4130);
x_4131 = lean_ctor_get(x_4043, 1);
lean_inc(x_4131);
lean_dec(x_4043);
x_8 = x_4130;
x_9 = x_4131;
goto block_16;
}
}
else
{
lean_object* x_4132; lean_object* x_4133; 
lean_dec(x_4038);
lean_dec(x_4032);
lean_dec(x_4029);
lean_dec(x_4014);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4132 = lean_ctor_get(x_4039, 0);
lean_inc(x_4132);
x_4133 = lean_ctor_get(x_4039, 1);
lean_inc(x_4133);
lean_dec(x_4039);
x_8 = x_4132;
x_9 = x_4133;
goto block_16;
}
}
else
{
lean_object* x_4134; lean_object* x_4135; 
lean_dec(x_4022);
lean_dec(x_4020);
lean_dec(x_4018);
lean_dec(x_4016);
lean_dec(x_4014);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4134 = lean_ctor_get(x_4023, 0);
lean_inc(x_4134);
x_4135 = lean_ctor_get(x_4023, 1);
lean_inc(x_4135);
lean_dec(x_4023);
x_8 = x_4134;
x_9 = x_4135;
goto block_16;
}
}
else
{
lean_object* x_4136; lean_object* x_4137; 
lean_dec(x_4018);
lean_dec(x_4016);
lean_dec(x_4014);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4136 = lean_ctor_get(x_4019, 0);
lean_inc(x_4136);
x_4137 = lean_ctor_get(x_4019, 1);
lean_inc(x_4137);
lean_dec(x_4019);
x_8 = x_4136;
x_9 = x_4137;
goto block_16;
}
}
else
{
lean_object* x_4138; lean_object* x_4139; 
lean_dec(x_4014);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4138 = lean_ctor_get(x_4015, 0);
lean_inc(x_4138);
x_4139 = lean_ctor_get(x_4015, 1);
lean_inc(x_4139);
lean_dec(x_4015);
x_8 = x_4138;
x_9 = x_4139;
goto block_16;
}
}
else
{
lean_object* x_4140; lean_object* x_4141; lean_object* x_4142; 
lean_dec(x_4012);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4140 = lean_ctor_get(x_4011, 1);
lean_inc(x_4140);
if (lean_is_exclusive(x_4011)) {
 lean_ctor_release(x_4011, 0);
 lean_ctor_release(x_4011, 1);
 x_4141 = x_4011;
} else {
 lean_dec_ref(x_4011);
 x_4141 = lean_box(0);
}
if (lean_is_scalar(x_4141)) {
 x_4142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4142 = x_4141;
}
lean_ctor_set(x_4142, 0, x_4010);
lean_ctor_set(x_4142, 1, x_4140);
return x_4142;
}
}
else
{
lean_object* x_4143; lean_object* x_4144; 
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4143 = lean_ctor_get(x_4011, 0);
lean_inc(x_4143);
x_4144 = lean_ctor_get(x_4011, 1);
lean_inc(x_4144);
lean_dec(x_4011);
x_8 = x_4143;
x_9 = x_4144;
goto block_16;
}
}
else
{
lean_object* x_4145; lean_object* x_4146; 
lean_dec(x_3995);
lean_dec(x_3993);
lean_dec(x_3982);
lean_dec(x_3978);
lean_dec(x_3976);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4145 = lean_ctor_get(x_3996, 0);
lean_inc(x_4145);
x_4146 = lean_ctor_get(x_3996, 1);
lean_inc(x_4146);
lean_dec(x_3996);
x_8 = x_4145;
x_9 = x_4146;
goto block_16;
}
}
else
{
lean_object* x_4147; lean_object* x_4148; 
lean_dec(x_3982);
lean_dec(x_3978);
lean_dec(x_3976);
lean_dec(x_3974);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4147 = lean_ctor_get(x_3992, 0);
lean_inc(x_4147);
x_4148 = lean_ctor_get(x_3992, 1);
lean_inc(x_4148);
lean_dec(x_3992);
x_8 = x_4147;
x_9 = x_4148;
goto block_16;
}
}
}
else
{
lean_object* x_4149; lean_object* x_4150; 
lean_dec(x_3982);
lean_dec(x_3978);
lean_dec(x_3976);
lean_dec(x_3974);
lean_dec(x_3964);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4149 = lean_ctor_get(x_3984, 0);
lean_inc(x_4149);
x_4150 = lean_ctor_get(x_3984, 1);
lean_inc(x_4150);
lean_dec(x_3984);
x_8 = x_4149;
x_9 = x_4150;
goto block_16;
}
}
else
{
lean_object* x_4151; lean_object* x_4152; 
lean_dec(x_3978);
lean_dec(x_3976);
lean_dec(x_3974);
lean_dec(x_3964);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4151 = lean_ctor_get(x_3979, 0);
lean_inc(x_4151);
x_4152 = lean_ctor_get(x_3979, 1);
lean_inc(x_4152);
lean_dec(x_3979);
x_8 = x_4151;
x_9 = x_4152;
goto block_16;
}
}
else
{
lean_object* x_4153; lean_object* x_4154; 
lean_dec(x_3974);
lean_dec(x_3973);
lean_dec(x_3964);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4153 = lean_ctor_get(x_3975, 0);
lean_inc(x_4153);
x_4154 = lean_ctor_get(x_3975, 1);
lean_inc(x_4154);
lean_dec(x_3975);
x_8 = x_4153;
x_9 = x_4154;
goto block_16;
}
}
else
{
lean_object* x_4155; lean_object* x_4156; lean_object* x_4157; lean_object* x_4158; 
lean_dec(x_3971);
lean_dec(x_3970);
lean_dec(x_3964);
lean_dec(x_3963);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4155 = lean_ctor_get(x_3968, 1);
lean_inc(x_4155);
if (lean_is_exclusive(x_3968)) {
 lean_ctor_release(x_3968, 0);
 lean_ctor_release(x_3968, 1);
 x_4156 = x_3968;
} else {
 lean_dec_ref(x_3968);
 x_4156 = lean_box(0);
}
x_4157 = lean_box(0);
if (lean_is_scalar(x_4156)) {
 x_4158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4158 = x_4156;
}
lean_ctor_set(x_4158, 0, x_4157);
lean_ctor_set(x_4158, 1, x_4155);
return x_4158;
}
}
else
{
lean_object* x_4159; lean_object* x_4160; lean_object* x_4161; lean_object* x_4162; 
lean_dec(x_3970);
lean_dec(x_3969);
lean_dec(x_3964);
lean_dec(x_3963);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4159 = lean_ctor_get(x_3968, 1);
lean_inc(x_4159);
if (lean_is_exclusive(x_3968)) {
 lean_ctor_release(x_3968, 0);
 lean_ctor_release(x_3968, 1);
 x_4160 = x_3968;
} else {
 lean_dec_ref(x_3968);
 x_4160 = lean_box(0);
}
x_4161 = lean_box(0);
if (lean_is_scalar(x_4160)) {
 x_4162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4162 = x_4160;
}
lean_ctor_set(x_4162, 0, x_4161);
lean_ctor_set(x_4162, 1, x_4159);
return x_4162;
}
}
else
{
lean_object* x_4163; lean_object* x_4164; lean_object* x_4165; lean_object* x_4166; 
lean_dec(x_3969);
lean_dec(x_3964);
lean_dec(x_3963);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4163 = lean_ctor_get(x_3968, 1);
lean_inc(x_4163);
if (lean_is_exclusive(x_3968)) {
 lean_ctor_release(x_3968, 0);
 lean_ctor_release(x_3968, 1);
 x_4164 = x_3968;
} else {
 lean_dec_ref(x_3968);
 x_4164 = lean_box(0);
}
x_4165 = lean_box(0);
if (lean_is_scalar(x_4164)) {
 x_4166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4166 = x_4164;
}
lean_ctor_set(x_4166, 0, x_4165);
lean_ctor_set(x_4166, 1, x_4163);
return x_4166;
}
}
else
{
lean_object* x_4167; lean_object* x_4168; lean_object* x_4169; uint8_t x_4170; 
lean_dec(x_3964);
lean_dec(x_3963);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4167 = lean_ctor_get(x_3968, 0);
lean_inc(x_4167);
x_4168 = lean_ctor_get(x_3968, 1);
lean_inc(x_4168);
if (lean_is_exclusive(x_3968)) {
 lean_ctor_release(x_3968, 0);
 lean_ctor_release(x_3968, 1);
 x_4169 = x_3968;
} else {
 lean_dec_ref(x_3968);
 x_4169 = lean_box(0);
}
x_4170 = l_Lean_Exception_isInterrupt(x_4167);
if (x_4170 == 0)
{
uint8_t x_4171; 
x_4171 = l_Lean_Exception_isRuntime(x_4167);
if (x_4171 == 0)
{
lean_object* x_4172; lean_object* x_4173; 
lean_dec(x_4167);
x_4172 = lean_box(0);
if (lean_is_scalar(x_4169)) {
 x_4173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4173 = x_4169;
 lean_ctor_set_tag(x_4173, 0);
}
lean_ctor_set(x_4173, 0, x_4172);
lean_ctor_set(x_4173, 1, x_4168);
return x_4173;
}
else
{
lean_object* x_4174; 
if (lean_is_scalar(x_4169)) {
 x_4174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4174 = x_4169;
}
lean_ctor_set(x_4174, 0, x_4167);
lean_ctor_set(x_4174, 1, x_4168);
return x_4174;
}
}
else
{
lean_object* x_4175; 
if (lean_is_scalar(x_4169)) {
 x_4175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4175 = x_4169;
}
lean_ctor_set(x_4175, 0, x_4167);
lean_ctor_set(x_4175, 1, x_4168);
return x_4175;
}
}
}
else
{
lean_object* x_4176; lean_object* x_4177; lean_object* x_4178; uint8_t x_4179; 
lean_dec(x_3964);
lean_dec(x_3963);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4176 = lean_ctor_get(x_3965, 0);
lean_inc(x_4176);
x_4177 = lean_ctor_get(x_3965, 1);
lean_inc(x_4177);
if (lean_is_exclusive(x_3965)) {
 lean_ctor_release(x_3965, 0);
 lean_ctor_release(x_3965, 1);
 x_4178 = x_3965;
} else {
 lean_dec_ref(x_3965);
 x_4178 = lean_box(0);
}
x_4179 = l_Lean_Exception_isInterrupt(x_4176);
if (x_4179 == 0)
{
uint8_t x_4180; 
x_4180 = l_Lean_Exception_isRuntime(x_4176);
if (x_4180 == 0)
{
lean_object* x_4181; lean_object* x_4182; 
lean_dec(x_4176);
x_4181 = lean_box(0);
if (lean_is_scalar(x_4178)) {
 x_4182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4182 = x_4178;
 lean_ctor_set_tag(x_4182, 0);
}
lean_ctor_set(x_4182, 0, x_4181);
lean_ctor_set(x_4182, 1, x_4177);
return x_4182;
}
else
{
lean_object* x_4183; 
if (lean_is_scalar(x_4178)) {
 x_4183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4183 = x_4178;
}
lean_ctor_set(x_4183, 0, x_4176);
lean_ctor_set(x_4183, 1, x_4177);
return x_4183;
}
}
else
{
lean_object* x_4184; 
if (lean_is_scalar(x_4178)) {
 x_4184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4184 = x_4178;
}
lean_ctor_set(x_4184, 0, x_4176);
lean_ctor_set(x_4184, 1, x_4177);
return x_4184;
}
}
}
else
{
lean_object* x_4185; lean_object* x_4186; lean_object* x_4187; lean_object* x_4188; 
lean_dec(x_3961);
lean_dec(x_3960);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4185 = lean_ctor_get(x_3958, 1);
lean_inc(x_4185);
if (lean_is_exclusive(x_3958)) {
 lean_ctor_release(x_3958, 0);
 lean_ctor_release(x_3958, 1);
 x_4186 = x_3958;
} else {
 lean_dec_ref(x_3958);
 x_4186 = lean_box(0);
}
x_4187 = lean_box(0);
if (lean_is_scalar(x_4186)) {
 x_4188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4188 = x_4186;
}
lean_ctor_set(x_4188, 0, x_4187);
lean_ctor_set(x_4188, 1, x_4185);
return x_4188;
}
}
else
{
lean_object* x_4189; lean_object* x_4190; lean_object* x_4191; lean_object* x_4192; 
lean_dec(x_3960);
lean_dec(x_3959);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4189 = lean_ctor_get(x_3958, 1);
lean_inc(x_4189);
if (lean_is_exclusive(x_3958)) {
 lean_ctor_release(x_3958, 0);
 lean_ctor_release(x_3958, 1);
 x_4190 = x_3958;
} else {
 lean_dec_ref(x_3958);
 x_4190 = lean_box(0);
}
x_4191 = lean_box(0);
if (lean_is_scalar(x_4190)) {
 x_4192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4192 = x_4190;
}
lean_ctor_set(x_4192, 0, x_4191);
lean_ctor_set(x_4192, 1, x_4189);
return x_4192;
}
}
else
{
lean_object* x_4193; lean_object* x_4194; lean_object* x_4195; lean_object* x_4196; 
lean_dec(x_3959);
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4193 = lean_ctor_get(x_3958, 1);
lean_inc(x_4193);
if (lean_is_exclusive(x_3958)) {
 lean_ctor_release(x_3958, 0);
 lean_ctor_release(x_3958, 1);
 x_4194 = x_3958;
} else {
 lean_dec_ref(x_3958);
 x_4194 = lean_box(0);
}
x_4195 = lean_box(0);
if (lean_is_scalar(x_4194)) {
 x_4196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4196 = x_4194;
}
lean_ctor_set(x_4196, 0, x_4195);
lean_ctor_set(x_4196, 1, x_4193);
return x_4196;
}
}
else
{
lean_object* x_4197; lean_object* x_4198; lean_object* x_4199; uint8_t x_4200; 
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4197 = lean_ctor_get(x_3958, 0);
lean_inc(x_4197);
x_4198 = lean_ctor_get(x_3958, 1);
lean_inc(x_4198);
if (lean_is_exclusive(x_3958)) {
 lean_ctor_release(x_3958, 0);
 lean_ctor_release(x_3958, 1);
 x_4199 = x_3958;
} else {
 lean_dec_ref(x_3958);
 x_4199 = lean_box(0);
}
x_4200 = l_Lean_Exception_isInterrupt(x_4197);
if (x_4200 == 0)
{
uint8_t x_4201; 
x_4201 = l_Lean_Exception_isRuntime(x_4197);
if (x_4201 == 0)
{
lean_object* x_4202; lean_object* x_4203; 
lean_dec(x_4197);
x_4202 = lean_box(0);
if (lean_is_scalar(x_4199)) {
 x_4203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4203 = x_4199;
 lean_ctor_set_tag(x_4203, 0);
}
lean_ctor_set(x_4203, 0, x_4202);
lean_ctor_set(x_4203, 1, x_4198);
return x_4203;
}
else
{
lean_object* x_4204; 
if (lean_is_scalar(x_4199)) {
 x_4204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4204 = x_4199;
}
lean_ctor_set(x_4204, 0, x_4197);
lean_ctor_set(x_4204, 1, x_4198);
return x_4204;
}
}
else
{
lean_object* x_4205; 
if (lean_is_scalar(x_4199)) {
 x_4205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4205 = x_4199;
}
lean_ctor_set(x_4205, 0, x_4197);
lean_ctor_set(x_4205, 1, x_4198);
return x_4205;
}
}
}
else
{
lean_object* x_4206; lean_object* x_4207; lean_object* x_4208; uint8_t x_4209; 
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4206 = lean_ctor_get(x_3955, 0);
lean_inc(x_4206);
x_4207 = lean_ctor_get(x_3955, 1);
lean_inc(x_4207);
if (lean_is_exclusive(x_3955)) {
 lean_ctor_release(x_3955, 0);
 lean_ctor_release(x_3955, 1);
 x_4208 = x_3955;
} else {
 lean_dec_ref(x_3955);
 x_4208 = lean_box(0);
}
x_4209 = l_Lean_Exception_isInterrupt(x_4206);
if (x_4209 == 0)
{
uint8_t x_4210; 
x_4210 = l_Lean_Exception_isRuntime(x_4206);
if (x_4210 == 0)
{
lean_object* x_4211; lean_object* x_4212; 
lean_dec(x_4206);
x_4211 = lean_box(0);
if (lean_is_scalar(x_4208)) {
 x_4212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4212 = x_4208;
 lean_ctor_set_tag(x_4212, 0);
}
lean_ctor_set(x_4212, 0, x_4211);
lean_ctor_set(x_4212, 1, x_4207);
return x_4212;
}
else
{
lean_object* x_4213; 
if (lean_is_scalar(x_4208)) {
 x_4213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4213 = x_4208;
}
lean_ctor_set(x_4213, 0, x_4206);
lean_ctor_set(x_4213, 1, x_4207);
return x_4213;
}
}
else
{
lean_object* x_4214; 
if (lean_is_scalar(x_4208)) {
 x_4214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4214 = x_4208;
}
lean_ctor_set(x_4214, 0, x_4206);
lean_ctor_set(x_4214, 1, x_4207);
return x_4214;
}
}
}
}
else
{
lean_object* x_4215; lean_object* x_4216; 
lean_dec(x_3914);
lean_dec(x_3908);
x_4215 = lean_ctor_get(x_3945, 1);
lean_inc(x_4215);
lean_dec(x_3945);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4216 = l_Lean_Meta_isMonad_x3f(x_3926, x_3, x_4, x_5, x_6, x_4215);
if (lean_obj_tag(x_4216) == 0)
{
lean_object* x_4217; 
x_4217 = lean_ctor_get(x_4216, 0);
lean_inc(x_4217);
if (lean_obj_tag(x_4217) == 0)
{
lean_object* x_4218; lean_object* x_4219; lean_object* x_4220; lean_object* x_4221; lean_object* x_4222; lean_object* x_4223; 
lean_dec(x_3944);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3924);
lean_dec(x_3916);
lean_dec(x_1);
x_4218 = lean_ctor_get(x_4216, 1);
lean_inc(x_4218);
lean_dec(x_4216);
x_4219 = l_Lean_Meta_SavedState_restore(x_3942, x_3, x_4, x_5, x_6, x_4218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_3942);
x_4220 = lean_ctor_get(x_4219, 1);
lean_inc(x_4220);
if (lean_is_exclusive(x_4219)) {
 lean_ctor_release(x_4219, 0);
 lean_ctor_release(x_4219, 1);
 x_4221 = x_4219;
} else {
 lean_dec_ref(x_4219);
 x_4221 = lean_box(0);
}
x_4222 = lean_box(0);
if (lean_is_scalar(x_4221)) {
 x_4223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4223 = x_4221;
}
lean_ctor_set(x_4223, 0, x_4222);
lean_ctor_set(x_4223, 1, x_4220);
return x_4223;
}
else
{
lean_object* x_4224; lean_object* x_4225; lean_object* x_4226; lean_object* x_4227; lean_object* x_4228; lean_object* x_4229; lean_object* x_4230; lean_object* x_4231; lean_object* x_4232; lean_object* x_4233; lean_object* x_4234; lean_object* x_4235; lean_object* x_4236; lean_object* x_4237; lean_object* x_4238; lean_object* x_4239; lean_object* x_4240; lean_object* x_4241; lean_object* x_4242; lean_object* x_4243; lean_object* x_4253; lean_object* x_4254; 
x_4224 = lean_ctor_get(x_4216, 1);
lean_inc(x_4224);
if (lean_is_exclusive(x_4216)) {
 lean_ctor_release(x_4216, 0);
 lean_ctor_release(x_4216, 1);
 x_4225 = x_4216;
} else {
 lean_dec_ref(x_4216);
 x_4225 = lean_box(0);
}
x_4226 = lean_ctor_get(x_4217, 0);
lean_inc(x_4226);
if (lean_is_exclusive(x_4217)) {
 lean_ctor_release(x_4217, 0);
 x_4227 = x_4217;
} else {
 lean_dec_ref(x_4217);
 x_4227 = lean_box(0);
}
if (lean_is_scalar(x_4227)) {
 x_4228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_4228 = x_4227;
}
lean_ctor_set(x_4228, 0, x_3938);
if (lean_is_scalar(x_3936)) {
 x_4229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_4229 = x_3936;
}
lean_ctor_set(x_4229, 0, x_3939);
if (lean_is_scalar(x_3924)) {
 x_4230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_4230 = x_3924;
}
lean_ctor_set(x_4230, 0, x_3927);
x_4231 = lean_box(0);
x_4232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4232, 0, x_4226);
x_4233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4233, 0, x_1);
x_4234 = lean_box(0);
if (lean_is_scalar(x_3944)) {
 x_4235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4235 = x_3944;
 lean_ctor_set_tag(x_4235, 1);
}
lean_ctor_set(x_4235, 0, x_4233);
lean_ctor_set(x_4235, 1, x_4234);
if (lean_is_scalar(x_3940)) {
 x_4236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4236 = x_3940;
 lean_ctor_set_tag(x_4236, 1);
}
lean_ctor_set(x_4236, 0, x_4232);
lean_ctor_set(x_4236, 1, x_4235);
if (lean_is_scalar(x_3928)) {
 x_4237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4237 = x_3928;
 lean_ctor_set_tag(x_4237, 1);
}
lean_ctor_set(x_4237, 0, x_4231);
lean_ctor_set(x_4237, 1, x_4236);
if (lean_is_scalar(x_3916)) {
 x_4238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4238 = x_3916;
 lean_ctor_set_tag(x_4238, 1);
}
lean_ctor_set(x_4238, 0, x_4230);
lean_ctor_set(x_4238, 1, x_4237);
x_4239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4239, 0, x_4229);
lean_ctor_set(x_4239, 1, x_4238);
x_4240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4240, 0, x_4228);
lean_ctor_set(x_4240, 1, x_4239);
x_4241 = lean_array_mk(x_4240);
x_4253 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4254 = l_Lean_Meta_mkAppOptM(x_4253, x_4241, x_3, x_4, x_5, x_6, x_4224);
if (lean_obj_tag(x_4254) == 0)
{
lean_object* x_4255; lean_object* x_4256; lean_object* x_4257; 
x_4255 = lean_ctor_get(x_4254, 0);
lean_inc(x_4255);
x_4256 = lean_ctor_get(x_4254, 1);
lean_inc(x_4256);
lean_dec(x_4254);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_4257 = l_Lean_Meta_expandCoe(x_4255, x_3, x_4, x_5, x_6, x_4256);
if (lean_obj_tag(x_4257) == 0)
{
lean_object* x_4258; lean_object* x_4259; lean_object* x_4260; lean_object* x_4261; lean_object* x_4262; 
lean_dec(x_4225);
lean_dec(x_3942);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_4258 = lean_ctor_get(x_4257, 0);
lean_inc(x_4258);
x_4259 = lean_ctor_get(x_4257, 1);
lean_inc(x_4259);
if (lean_is_exclusive(x_4257)) {
 lean_ctor_release(x_4257, 0);
 lean_ctor_release(x_4257, 1);
 x_4260 = x_4257;
} else {
 lean_dec_ref(x_4257);
 x_4260 = lean_box(0);
}
x_4261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4261, 0, x_4258);
if (lean_is_scalar(x_4260)) {
 x_4262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4262 = x_4260;
}
lean_ctor_set(x_4262, 0, x_4261);
lean_ctor_set(x_4262, 1, x_4259);
return x_4262;
}
else
{
lean_object* x_4263; lean_object* x_4264; 
x_4263 = lean_ctor_get(x_4257, 0);
lean_inc(x_4263);
x_4264 = lean_ctor_get(x_4257, 1);
lean_inc(x_4264);
lean_dec(x_4257);
x_4242 = x_4263;
x_4243 = x_4264;
goto block_4252;
}
}
else
{
lean_object* x_4265; lean_object* x_4266; 
x_4265 = lean_ctor_get(x_4254, 0);
lean_inc(x_4265);
x_4266 = lean_ctor_get(x_4254, 1);
lean_inc(x_4266);
lean_dec(x_4254);
x_4242 = x_4265;
x_4243 = x_4266;
goto block_4252;
}
block_4252:
{
uint8_t x_4244; 
x_4244 = l_Lean_Exception_isInterrupt(x_4242);
if (x_4244 == 0)
{
uint8_t x_4245; 
x_4245 = l_Lean_Exception_isRuntime(x_4242);
if (x_4245 == 0)
{
lean_object* x_4246; lean_object* x_4247; lean_object* x_4248; lean_object* x_4249; 
lean_dec(x_4242);
lean_dec(x_4225);
x_4246 = l_Lean_Meta_SavedState_restore(x_3942, x_3, x_4, x_5, x_6, x_4243);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_3942);
x_4247 = lean_ctor_get(x_4246, 1);
lean_inc(x_4247);
if (lean_is_exclusive(x_4246)) {
 lean_ctor_release(x_4246, 0);
 lean_ctor_release(x_4246, 1);
 x_4248 = x_4246;
} else {
 lean_dec_ref(x_4246);
 x_4248 = lean_box(0);
}
if (lean_is_scalar(x_4248)) {
 x_4249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4249 = x_4248;
}
lean_ctor_set(x_4249, 0, x_4231);
lean_ctor_set(x_4249, 1, x_4247);
return x_4249;
}
else
{
lean_object* x_4250; 
lean_dec(x_3942);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_4225)) {
 x_4250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4250 = x_4225;
 lean_ctor_set_tag(x_4250, 1);
}
lean_ctor_set(x_4250, 0, x_4242);
lean_ctor_set(x_4250, 1, x_4243);
return x_4250;
}
}
else
{
lean_object* x_4251; 
lean_dec(x_3942);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_4225)) {
 x_4251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4251 = x_4225;
 lean_ctor_set_tag(x_4251, 1);
}
lean_ctor_set(x_4251, 0, x_4242);
lean_ctor_set(x_4251, 1, x_4243);
return x_4251;
}
}
}
}
else
{
lean_object* x_4267; lean_object* x_4268; lean_object* x_4269; lean_object* x_4270; 
lean_dec(x_3944);
lean_dec(x_3942);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3924);
lean_dec(x_3916);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4267 = lean_ctor_get(x_4216, 0);
lean_inc(x_4267);
x_4268 = lean_ctor_get(x_4216, 1);
lean_inc(x_4268);
if (lean_is_exclusive(x_4216)) {
 lean_ctor_release(x_4216, 0);
 lean_ctor_release(x_4216, 1);
 x_4269 = x_4216;
} else {
 lean_dec_ref(x_4216);
 x_4269 = lean_box(0);
}
if (lean_is_scalar(x_4269)) {
 x_4270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4270 = x_4269;
}
lean_ctor_set(x_4270, 0, x_4267);
lean_ctor_set(x_4270, 1, x_4268);
return x_4270;
}
}
}
else
{
lean_object* x_4271; lean_object* x_4272; lean_object* x_4273; lean_object* x_4274; 
lean_dec(x_3944);
lean_dec(x_3942);
lean_dec(x_3940);
lean_dec(x_3939);
lean_dec(x_3938);
lean_dec(x_3936);
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3924);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4271 = lean_ctor_get(x_3945, 0);
lean_inc(x_4271);
x_4272 = lean_ctor_get(x_3945, 1);
lean_inc(x_4272);
if (lean_is_exclusive(x_3945)) {
 lean_ctor_release(x_3945, 0);
 lean_ctor_release(x_3945, 1);
 x_4273 = x_3945;
} else {
 lean_dec_ref(x_3945);
 x_4273 = lean_box(0);
}
if (lean_is_scalar(x_4273)) {
 x_4274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4274 = x_4273;
}
lean_ctor_set(x_4274, 0, x_4271);
lean_ctor_set(x_4274, 1, x_4272);
return x_4274;
}
}
}
else
{
lean_object* x_4275; lean_object* x_4276; lean_object* x_4277; lean_object* x_4278; 
lean_dec(x_3928);
lean_dec(x_3927);
lean_dec(x_3926);
lean_dec(x_3924);
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4275 = lean_ctor_get(x_3929, 0);
lean_inc(x_4275);
x_4276 = lean_ctor_get(x_3929, 1);
lean_inc(x_4276);
if (lean_is_exclusive(x_3929)) {
 lean_ctor_release(x_3929, 0);
 lean_ctor_release(x_3929, 1);
 x_4277 = x_3929;
} else {
 lean_dec_ref(x_3929);
 x_4277 = lean_box(0);
}
if (lean_is_scalar(x_4277)) {
 x_4278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4278 = x_4277;
}
lean_ctor_set(x_4278, 0, x_4275);
lean_ctor_set(x_4278, 1, x_4276);
return x_4278;
}
}
}
else
{
lean_object* x_4279; lean_object* x_4280; lean_object* x_4281; lean_object* x_4282; 
lean_dec(x_3916);
lean_dec(x_3914);
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4279 = lean_ctor_get(x_3917, 0);
lean_inc(x_4279);
x_4280 = lean_ctor_get(x_3917, 1);
lean_inc(x_4280);
if (lean_is_exclusive(x_3917)) {
 lean_ctor_release(x_3917, 0);
 lean_ctor_release(x_3917, 1);
 x_4281 = x_3917;
} else {
 lean_dec_ref(x_3917);
 x_4281 = lean_box(0);
}
if (lean_is_scalar(x_4281)) {
 x_4282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4282 = x_4281;
}
lean_ctor_set(x_4282, 0, x_4279);
lean_ctor_set(x_4282, 1, x_4280);
return x_4282;
}
}
else
{
lean_object* x_4283; lean_object* x_4284; lean_object* x_4285; lean_object* x_4286; 
lean_dec(x_3908);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_4283 = lean_ctor_get(x_3910, 0);
lean_inc(x_4283);
x_4284 = lean_ctor_get(x_3910, 1);
lean_inc(x_4284);
if (lean_is_exclusive(x_3910)) {
 lean_ctor_release(x_3910, 0);
 lean_ctor_release(x_3910, 1);
 x_4285 = x_3910;
} else {
 lean_dec_ref(x_3910);
 x_4285 = lean_box(0);
}
if (lean_is_scalar(x_4285)) {
 x_4286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4286 = x_4285;
}
lean_ctor_set(x_4286, 0, x_4283);
lean_ctor_set(x_4286, 1, x_4284);
return x_4286;
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
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3____closed__8);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_3_(lean_io_mk_world());
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
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_217_(lean_io_mk_world());
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
