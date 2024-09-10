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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__7;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__1;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__6;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__4;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__9;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__11;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220_(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__8;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__3;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__1;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__6;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__17;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__6;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__10;
uint8_t l_Lean_Expr_isSort(lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__3;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__6;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__8;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__2;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__1;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__15;
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
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__2;
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
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__5;
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
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__18;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("autoLift", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("insert monadic lifts (i.e., `liftM` and coercions) when needed", 62, 62);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__6;
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
x_1 = lean_mk_string_unchecked("coe", 3, 3);
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
x_1 = lean_mk_string_unchecked("could not coerce", 16, 16);
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
x_1 = lean_mk_string_unchecked("\nto", 3, 3);
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
x_1 = lean_mk_string_unchecked("\ncoerced expression has wrong type:", 35, 35);
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__3;
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
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__4;
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
x_61 = l_Lean_Meta_coerceSimple_x3f___closed__13;
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
x_125 = l_Lean_Meta_coerceSimple_x3f___closed__13;
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
x_196 = l_Lean_Meta_coerceSimple_x3f___closed__13;
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
x_273 = l_Lean_Meta_coerceSimple_x3f___closed__13;
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
x_2 = l_Lean_Meta_coerceSimple_x3f___closed__4;
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
x_123 = l_Lean_Meta_coerceSimple_x3f___closed__13;
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
x_196 = l_Lean_Meta_coerceSimple_x3f___closed__13;
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
x_1 = lean_mk_string_unchecked("liftM", 5, 5);
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
x_1 = lean_mk_string_unchecked("a", 1, 1);
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
x_1 = lean_mk_string_unchecked("Internal", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("liftCoeM", 8, 8);
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
x_1 = lean_mk_string_unchecked("coeM", 4, 4);
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
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__18() {
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
lean_object* x_8; lean_object* x_9; lean_object* x_17; lean_object* x_18; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_34 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_35, x_3, x_4, x_5, x_6, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_40 = l_Lean_Meta_isTypeApp_x3f(x_32, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_38);
x_53 = l_Lean_Meta_isTypeApp_x3f(x_38, x_3, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
lean_dec(x_52);
lean_dec(x_51);
lean_free_object(x_41);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_53, 0, x_57);
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_dec(x_53);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
lean_inc(x_65);
x_67 = l_Lean_Meta_isExprDefEq(x_65, x_51, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
lean_free_object(x_62);
lean_free_object(x_41);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_67, 1);
x_72 = lean_ctor_get(x_67, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_5, 2);
lean_inc(x_73);
x_74 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_75 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = lean_box(0);
lean_ctor_set(x_67, 0, x_76);
return x_67;
}
else
{
lean_object* x_77; 
lean_free_object(x_67);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_65);
x_77 = lean_infer_type(x_65, x_3, x_4, x_5, x_6, x_71);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_80 = lean_whnf(x_78, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 7)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 3)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 2);
lean_inc(x_83);
lean_dec(x_81);
if (lean_obj_tag(x_83) == 3)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_87 = lean_infer_type(x_51, x_3, x_4, x_5, x_6, x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_90 = lean_whnf(x_88, x_3, x_4, x_5, x_6, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 7)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 3)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 2);
lean_inc(x_93);
lean_dec(x_91);
if (lean_obj_tag(x_93) == 3)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = l_Lean_Meta_decLevel(x_85, x_3, x_4, x_5, x_6, x_94);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Meta_decLevel(x_95, x_3, x_4, x_5, x_6, x_99);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
x_104 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_98);
x_105 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_98, x_102, x_104, x_3, x_4, x_5, x_6, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_free_object(x_100);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_86);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = lean_box(0);
lean_ctor_set(x_105, 0, x_110);
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
lean_dec(x_105);
x_115 = l_Lean_Meta_decLevel(x_86, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = l_Lean_Meta_decLevel(x_96, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_121 = lean_ctor_get(x_119, 1);
x_122 = lean_box(0);
lean_ctor_set_tag(x_119, 1);
lean_ctor_set(x_119, 1, x_122);
lean_ctor_set_tag(x_115, 1);
lean_ctor_set(x_115, 1, x_119);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_115);
lean_ctor_set(x_100, 0, x_98);
x_123 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_124 = l_Lean_Expr_const___override(x_123, x_100);
x_125 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_65);
x_126 = lean_array_push(x_125, x_65);
lean_inc(x_51);
x_127 = lean_array_push(x_126, x_51);
x_128 = l_Lean_mkAppN(x_124, x_127);
lean_dec(x_127);
x_129 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_130 = l_Lean_Meta_trySynthInstance(x_128, x_129, x_3, x_4, x_5, x_6, x_121);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 1)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_134 = l_Lean_Meta_getDecLevel(x_66, x_3, x_4, x_5, x_6, x_132);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_138 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_142 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_141);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_142, 1);
lean_ctor_set_tag(x_142, 1);
lean_ctor_set(x_142, 1, x_122);
lean_ctor_set_tag(x_138, 1);
lean_ctor_set(x_138, 1, x_142);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_138);
x_145 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_134);
x_146 = l_Lean_Expr_const___override(x_145, x_134);
x_147 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_65);
x_148 = lean_array_push(x_147, x_65);
lean_inc(x_51);
x_149 = lean_array_push(x_148, x_51);
lean_inc(x_133);
x_150 = lean_array_push(x_149, x_133);
lean_inc(x_66);
x_151 = lean_array_push(x_150, x_66);
lean_inc(x_1);
x_152 = lean_array_push(x_151, x_1);
x_153 = l_Lean_mkAppN(x_146, x_152);
lean_dec(x_152);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_153);
x_154 = lean_infer_type(x_153, x_3, x_4, x_5, x_6, x_144);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_157 = l_Lean_Meta_isExprDefEq(x_32, x_155, x_3, x_4, x_5, x_6, x_156);
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
lean_dec(x_153);
lean_free_object(x_54);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_161 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_161);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_161, 0);
lean_dec(x_164);
lean_ctor_set(x_161, 0, x_129);
return x_161;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
lean_dec(x_161);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_129);
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
lean_inc(x_66);
x_169 = l_Lean_Meta_getLevel(x_66, x_3, x_4, x_5, x_6, x_167);
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
lean_inc(x_52);
x_173 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_172);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; 
x_175 = lean_ctor_get(x_173, 1);
lean_ctor_set_tag(x_173, 1);
lean_ctor_set(x_173, 1, x_122);
lean_ctor_set_tag(x_169, 1);
lean_ctor_set(x_169, 1, x_173);
x_176 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_177 = l_Lean_Expr_const___override(x_176, x_169);
x_178 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_179 = lean_array_push(x_178, x_66);
x_180 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_181 = lean_array_push(x_179, x_180);
lean_inc(x_52);
x_182 = lean_array_push(x_181, x_52);
x_183 = l_Lean_mkAppN(x_177, x_182);
lean_dec(x_182);
x_184 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_185 = 0;
lean_inc(x_66);
x_186 = l_Lean_Expr_forallE___override(x_184, x_66, x_183, x_185);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_187 = l_Lean_Meta_trySynthInstance(x_186, x_129, x_3, x_4, x_5, x_6, x_175);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 1)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_192 = l_Lean_Expr_const___override(x_191, x_134);
x_193 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_194 = lean_array_push(x_193, x_65);
x_195 = lean_array_push(x_194, x_51);
x_196 = lean_array_push(x_195, x_66);
x_197 = lean_array_push(x_196, x_52);
x_198 = lean_array_push(x_197, x_133);
x_199 = lean_array_push(x_198, x_190);
x_200 = lean_array_push(x_199, x_168);
x_201 = lean_array_push(x_200, x_1);
x_202 = l_Lean_mkAppN(x_192, x_201);
lean_dec(x_201);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_203 = l_Lean_Meta_expandCoe(x_202, x_3, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_204);
x_206 = lean_infer_type(x_204, x_3, x_4, x_5, x_6, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_209 = l_Lean_Meta_isExprDefEq(x_32, x_207, x_3, x_4, x_5, x_6, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_unbox(x_210);
lean_dec(x_210);
if (x_211 == 0)
{
uint8_t x_212; 
lean_dec(x_204);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_212 = !lean_is_exclusive(x_209);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_209, 0);
lean_dec(x_213);
lean_ctor_set(x_209, 0, x_129);
return x_209;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
lean_dec(x_209);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_129);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_216 = lean_ctor_get(x_209, 1);
lean_inc(x_216);
lean_dec(x_209);
x_217 = lean_box(0);
x_218 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_204, x_217, x_3, x_4, x_5, x_6, x_216);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
return x_218;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_218, 0);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_218);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_204);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_223 = lean_ctor_get(x_209, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_209, 1);
lean_inc(x_224);
lean_dec(x_209);
x_8 = x_223;
x_9 = x_224;
goto block_16;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_204);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_225 = lean_ctor_get(x_206, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_206, 1);
lean_inc(x_226);
lean_dec(x_206);
x_8 = x_225;
x_9 = x_226;
goto block_16;
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_227 = lean_ctor_get(x_203, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_203, 1);
lean_inc(x_228);
lean_dec(x_203);
x_8 = x_227;
x_9 = x_228;
goto block_16;
}
}
else
{
uint8_t x_229; 
lean_dec(x_188);
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_187);
if (x_229 == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_187, 0);
lean_dec(x_230);
lean_ctor_set(x_187, 0, x_129);
return x_187;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_187, 1);
lean_inc(x_231);
lean_dec(x_187);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_129);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_233 = lean_ctor_get(x_187, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_187, 1);
lean_inc(x_234);
lean_dec(x_187);
x_8 = x_233;
x_9 = x_234;
goto block_16;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_235 = lean_ctor_get(x_173, 0);
x_236 = lean_ctor_get(x_173, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_173);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_122);
lean_ctor_set_tag(x_169, 1);
lean_ctor_set(x_169, 1, x_237);
x_238 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_239 = l_Lean_Expr_const___override(x_238, x_169);
x_240 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_241 = lean_array_push(x_240, x_66);
x_242 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_243 = lean_array_push(x_241, x_242);
lean_inc(x_52);
x_244 = lean_array_push(x_243, x_52);
x_245 = l_Lean_mkAppN(x_239, x_244);
lean_dec(x_244);
x_246 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_247 = 0;
lean_inc(x_66);
x_248 = l_Lean_Expr_forallE___override(x_246, x_66, x_245, x_247);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_249 = l_Lean_Meta_trySynthInstance(x_248, x_129, x_3, x_4, x_5, x_6, x_236);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 1)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
lean_dec(x_250);
x_253 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_254 = l_Lean_Expr_const___override(x_253, x_134);
x_255 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_256 = lean_array_push(x_255, x_65);
x_257 = lean_array_push(x_256, x_51);
x_258 = lean_array_push(x_257, x_66);
x_259 = lean_array_push(x_258, x_52);
x_260 = lean_array_push(x_259, x_133);
x_261 = lean_array_push(x_260, x_252);
x_262 = lean_array_push(x_261, x_168);
x_263 = lean_array_push(x_262, x_1);
x_264 = l_Lean_mkAppN(x_254, x_263);
lean_dec(x_263);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_265 = l_Lean_Meta_expandCoe(x_264, x_3, x_4, x_5, x_6, x_251);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_266);
x_268 = lean_infer_type(x_266, x_3, x_4, x_5, x_6, x_267);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_271 = l_Lean_Meta_isExprDefEq(x_32, x_269, x_3, x_4, x_5, x_6, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_unbox(x_272);
lean_dec(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_275 = x_271;
} else {
 lean_dec_ref(x_271);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_129);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_277 = lean_ctor_get(x_271, 1);
lean_inc(x_277);
lean_dec(x_271);
x_278 = lean_box(0);
x_279 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_266, x_278, x_3, x_4, x_5, x_6, x_277);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_282 = x_279;
} else {
 lean_dec_ref(x_279);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_266);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_284 = lean_ctor_get(x_271, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_271, 1);
lean_inc(x_285);
lean_dec(x_271);
x_8 = x_284;
x_9 = x_285;
goto block_16;
}
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_266);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_286 = lean_ctor_get(x_268, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_268, 1);
lean_inc(x_287);
lean_dec(x_268);
x_8 = x_286;
x_9 = x_287;
goto block_16;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_288 = lean_ctor_get(x_265, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_265, 1);
lean_inc(x_289);
lean_dec(x_265);
x_8 = x_288;
x_9 = x_289;
goto block_16;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_250);
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_290 = lean_ctor_get(x_249, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_291 = x_249;
} else {
 lean_dec_ref(x_249);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_129);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_293 = lean_ctor_get(x_249, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_249, 1);
lean_inc(x_294);
lean_dec(x_249);
x_8 = x_293;
x_9 = x_294;
goto block_16;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_free_object(x_169);
lean_dec(x_171);
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_295 = lean_ctor_get(x_173, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_173, 1);
lean_inc(x_296);
lean_dec(x_173);
x_8 = x_295;
x_9 = x_296;
goto block_16;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_169, 0);
x_298 = lean_ctor_get(x_169, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_169);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_299 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_298);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
 lean_ctor_set_tag(x_303, 1);
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_122);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_297);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_306 = l_Lean_Expr_const___override(x_305, x_304);
x_307 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_308 = lean_array_push(x_307, x_66);
x_309 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_310 = lean_array_push(x_308, x_309);
lean_inc(x_52);
x_311 = lean_array_push(x_310, x_52);
x_312 = l_Lean_mkAppN(x_306, x_311);
lean_dec(x_311);
x_313 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_314 = 0;
lean_inc(x_66);
x_315 = l_Lean_Expr_forallE___override(x_313, x_66, x_312, x_314);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_316 = l_Lean_Meta_trySynthInstance(x_315, x_129, x_3, x_4, x_5, x_6, x_301);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_obj_tag(x_317) == 1)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
lean_dec(x_317);
x_320 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_321 = l_Lean_Expr_const___override(x_320, x_134);
x_322 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_323 = lean_array_push(x_322, x_65);
x_324 = lean_array_push(x_323, x_51);
x_325 = lean_array_push(x_324, x_66);
x_326 = lean_array_push(x_325, x_52);
x_327 = lean_array_push(x_326, x_133);
x_328 = lean_array_push(x_327, x_319);
x_329 = lean_array_push(x_328, x_168);
x_330 = lean_array_push(x_329, x_1);
x_331 = l_Lean_mkAppN(x_321, x_330);
lean_dec(x_330);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_332 = l_Lean_Meta_expandCoe(x_331, x_3, x_4, x_5, x_6, x_318);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_333);
x_335 = lean_infer_type(x_333, x_3, x_4, x_5, x_6, x_334);
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
x_338 = l_Lean_Meta_isExprDefEq(x_32, x_336, x_3, x_4, x_5, x_6, x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_unbox(x_339);
lean_dec(x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_333);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_342 = x_338;
} else {
 lean_dec_ref(x_338);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_129);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_344 = lean_ctor_get(x_338, 1);
lean_inc(x_344);
lean_dec(x_338);
x_345 = lean_box(0);
x_346 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_333, x_345, x_3, x_4, x_5, x_6, x_344);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_349 = x_346;
} else {
 lean_dec_ref(x_346);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_333);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_351 = lean_ctor_get(x_338, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_338, 1);
lean_inc(x_352);
lean_dec(x_338);
x_8 = x_351;
x_9 = x_352;
goto block_16;
}
}
else
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_333);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_353 = lean_ctor_get(x_335, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_335, 1);
lean_inc(x_354);
lean_dec(x_335);
x_8 = x_353;
x_9 = x_354;
goto block_16;
}
}
else
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_355 = lean_ctor_get(x_332, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_332, 1);
lean_inc(x_356);
lean_dec(x_332);
x_8 = x_355;
x_9 = x_356;
goto block_16;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_317);
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_357 = lean_ctor_get(x_316, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_358 = x_316;
} else {
 lean_dec_ref(x_316);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_129);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_360 = lean_ctor_get(x_316, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_316, 1);
lean_inc(x_361);
lean_dec(x_316);
x_8 = x_360;
x_9 = x_361;
goto block_16;
}
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_297);
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_362 = lean_ctor_get(x_299, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_299, 1);
lean_inc(x_363);
lean_dec(x_299);
x_8 = x_362;
x_9 = x_363;
goto block_16;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_168);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_364 = lean_ctor_get(x_169, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_169, 1);
lean_inc(x_365);
lean_dec(x_169);
x_8 = x_364;
x_9 = x_365;
goto block_16;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_366 = lean_ctor_get(x_161, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_161, 1);
lean_inc(x_367);
lean_dec(x_161);
x_8 = x_366;
x_9 = x_367;
goto block_16;
}
}
else
{
uint8_t x_368; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_368 = !lean_is_exclusive(x_157);
if (x_368 == 0)
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_157, 0);
lean_dec(x_369);
lean_ctor_set(x_54, 0, x_153);
lean_ctor_set(x_157, 0, x_54);
return x_157;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_157, 1);
lean_inc(x_370);
lean_dec(x_157);
lean_ctor_set(x_54, 0, x_153);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_54);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
else
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_153);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_372 = lean_ctor_get(x_157, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_157, 1);
lean_inc(x_373);
lean_dec(x_157);
x_8 = x_372;
x_9 = x_373;
goto block_16;
}
}
else
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_153);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_374 = lean_ctor_get(x_154, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_154, 1);
lean_inc(x_375);
lean_dec(x_154);
x_8 = x_374;
x_9 = x_375;
goto block_16;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_376 = lean_ctor_get(x_142, 0);
x_377 = lean_ctor_get(x_142, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_142);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_122);
lean_ctor_set_tag(x_138, 1);
lean_ctor_set(x_138, 1, x_378);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_138);
x_379 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_134);
x_380 = l_Lean_Expr_const___override(x_379, x_134);
x_381 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_65);
x_382 = lean_array_push(x_381, x_65);
lean_inc(x_51);
x_383 = lean_array_push(x_382, x_51);
lean_inc(x_133);
x_384 = lean_array_push(x_383, x_133);
lean_inc(x_66);
x_385 = lean_array_push(x_384, x_66);
lean_inc(x_1);
x_386 = lean_array_push(x_385, x_1);
x_387 = l_Lean_mkAppN(x_380, x_386);
lean_dec(x_386);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_387);
x_388 = lean_infer_type(x_387, x_3, x_4, x_5, x_6, x_377);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_391 = l_Lean_Meta_isExprDefEq(x_32, x_389, x_3, x_4, x_5, x_6, x_390);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; uint8_t x_393; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_unbox(x_392);
lean_dec(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_387);
lean_free_object(x_54);
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
lean_dec(x_391);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_395 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_394);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_398 = x_395;
} else {
 lean_dec_ref(x_395);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_129);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_395, 1);
lean_inc(x_400);
lean_dec(x_395);
x_401 = lean_ctor_get(x_396, 0);
lean_inc(x_401);
lean_dec(x_396);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_402 = l_Lean_Meta_getLevel(x_66, x_3, x_4, x_5, x_6, x_400);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_405 = x_402;
} else {
 lean_dec_ref(x_402);
 x_405 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_406 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_404);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_409 = x_406;
} else {
 lean_dec_ref(x_406);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
 lean_ctor_set_tag(x_410, 1);
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_122);
if (lean_is_scalar(x_405)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_405;
 lean_ctor_set_tag(x_411, 1);
}
lean_ctor_set(x_411, 0, x_403);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_413 = l_Lean_Expr_const___override(x_412, x_411);
x_414 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_415 = lean_array_push(x_414, x_66);
x_416 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_417 = lean_array_push(x_415, x_416);
lean_inc(x_52);
x_418 = lean_array_push(x_417, x_52);
x_419 = l_Lean_mkAppN(x_413, x_418);
lean_dec(x_418);
x_420 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_421 = 0;
lean_inc(x_66);
x_422 = l_Lean_Expr_forallE___override(x_420, x_66, x_419, x_421);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_423 = l_Lean_Meta_trySynthInstance(x_422, x_129, x_3, x_4, x_5, x_6, x_408);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
if (lean_obj_tag(x_424) == 1)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
lean_dec(x_424);
x_427 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_428 = l_Lean_Expr_const___override(x_427, x_134);
x_429 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_430 = lean_array_push(x_429, x_65);
x_431 = lean_array_push(x_430, x_51);
x_432 = lean_array_push(x_431, x_66);
x_433 = lean_array_push(x_432, x_52);
x_434 = lean_array_push(x_433, x_133);
x_435 = lean_array_push(x_434, x_426);
x_436 = lean_array_push(x_435, x_401);
x_437 = lean_array_push(x_436, x_1);
x_438 = l_Lean_mkAppN(x_428, x_437);
lean_dec(x_437);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_439 = l_Lean_Meta_expandCoe(x_438, x_3, x_4, x_5, x_6, x_425);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_440);
x_442 = lean_infer_type(x_440, x_3, x_4, x_5, x_6, x_441);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_445 = l_Lean_Meta_isExprDefEq(x_32, x_443, x_3, x_4, x_5, x_6, x_444);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; uint8_t x_447; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_unbox(x_446);
lean_dec(x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_440);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_449 = x_445;
} else {
 lean_dec_ref(x_445);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_129);
lean_ctor_set(x_450, 1, x_448);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_451 = lean_ctor_get(x_445, 1);
lean_inc(x_451);
lean_dec(x_445);
x_452 = lean_box(0);
x_453 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_440, x_452, x_3, x_4, x_5, x_6, x_451);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_456 = x_453;
} else {
 lean_dec_ref(x_453);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_440);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_458 = lean_ctor_get(x_445, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_445, 1);
lean_inc(x_459);
lean_dec(x_445);
x_8 = x_458;
x_9 = x_459;
goto block_16;
}
}
else
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_440);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_460 = lean_ctor_get(x_442, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_442, 1);
lean_inc(x_461);
lean_dec(x_442);
x_8 = x_460;
x_9 = x_461;
goto block_16;
}
}
else
{
lean_object* x_462; lean_object* x_463; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_462 = lean_ctor_get(x_439, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_439, 1);
lean_inc(x_463);
lean_dec(x_439);
x_8 = x_462;
x_9 = x_463;
goto block_16;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_424);
lean_dec(x_401);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_464 = lean_ctor_get(x_423, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_465 = x_423;
} else {
 lean_dec_ref(x_423);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_129);
lean_ctor_set(x_466, 1, x_464);
return x_466;
}
}
else
{
lean_object* x_467; lean_object* x_468; 
lean_dec(x_401);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_467 = lean_ctor_get(x_423, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_423, 1);
lean_inc(x_468);
lean_dec(x_423);
x_8 = x_467;
x_9 = x_468;
goto block_16;
}
}
else
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_405);
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_469 = lean_ctor_get(x_406, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_406, 1);
lean_inc(x_470);
lean_dec(x_406);
x_8 = x_469;
x_9 = x_470;
goto block_16;
}
}
else
{
lean_object* x_471; lean_object* x_472; 
lean_dec(x_401);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_471 = lean_ctor_get(x_402, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_402, 1);
lean_inc(x_472);
lean_dec(x_402);
x_8 = x_471;
x_9 = x_472;
goto block_16;
}
}
}
else
{
lean_object* x_473; lean_object* x_474; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_473 = lean_ctor_get(x_395, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_395, 1);
lean_inc(x_474);
lean_dec(x_395);
x_8 = x_473;
x_9 = x_474;
goto block_16;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_475 = lean_ctor_get(x_391, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_476 = x_391;
} else {
 lean_dec_ref(x_391);
 x_476 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_387);
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_54);
lean_ctor_set(x_477, 1, x_475);
return x_477;
}
}
else
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_387);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_478 = lean_ctor_get(x_391, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_391, 1);
lean_inc(x_479);
lean_dec(x_391);
x_8 = x_478;
x_9 = x_479;
goto block_16;
}
}
else
{
lean_object* x_480; lean_object* x_481; 
lean_dec(x_387);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_480 = lean_ctor_get(x_388, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_388, 1);
lean_inc(x_481);
lean_dec(x_388);
x_8 = x_480;
x_9 = x_481;
goto block_16;
}
}
}
else
{
lean_object* x_482; lean_object* x_483; 
lean_free_object(x_138);
lean_dec(x_140);
lean_free_object(x_134);
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_482 = lean_ctor_get(x_142, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_142, 1);
lean_inc(x_483);
lean_dec(x_142);
x_8 = x_482;
x_9 = x_483;
goto block_16;
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_138, 0);
x_485 = lean_ctor_get(x_138, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_138);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_486 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_489 = x_486;
} else {
 lean_dec_ref(x_486);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
 lean_ctor_set_tag(x_490, 1);
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_122);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_484);
lean_ctor_set(x_491, 1, x_490);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_491);
x_492 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_134);
x_493 = l_Lean_Expr_const___override(x_492, x_134);
x_494 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_65);
x_495 = lean_array_push(x_494, x_65);
lean_inc(x_51);
x_496 = lean_array_push(x_495, x_51);
lean_inc(x_133);
x_497 = lean_array_push(x_496, x_133);
lean_inc(x_66);
x_498 = lean_array_push(x_497, x_66);
lean_inc(x_1);
x_499 = lean_array_push(x_498, x_1);
x_500 = l_Lean_mkAppN(x_493, x_499);
lean_dec(x_499);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_500);
x_501 = lean_infer_type(x_500, x_3, x_4, x_5, x_6, x_488);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_504 = l_Lean_Meta_isExprDefEq(x_32, x_502, x_3, x_4, x_5, x_6, x_503);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; uint8_t x_506; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_unbox(x_505);
lean_dec(x_505);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; 
lean_dec(x_500);
lean_free_object(x_54);
x_507 = lean_ctor_get(x_504, 1);
lean_inc(x_507);
lean_dec(x_504);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_508 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_511 = x_508;
} else {
 lean_dec_ref(x_508);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_129);
lean_ctor_set(x_512, 1, x_510);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_508, 1);
lean_inc(x_513);
lean_dec(x_508);
x_514 = lean_ctor_get(x_509, 0);
lean_inc(x_514);
lean_dec(x_509);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_515 = l_Lean_Meta_getLevel(x_66, x_3, x_4, x_5, x_6, x_513);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 x_518 = x_515;
} else {
 lean_dec_ref(x_515);
 x_518 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_519 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_517);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; lean_object* x_535; lean_object* x_536; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_522 = x_519;
} else {
 lean_dec_ref(x_519);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
 lean_ctor_set_tag(x_523, 1);
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_122);
if (lean_is_scalar(x_518)) {
 x_524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_524 = x_518;
 lean_ctor_set_tag(x_524, 1);
}
lean_ctor_set(x_524, 0, x_516);
lean_ctor_set(x_524, 1, x_523);
x_525 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_526 = l_Lean_Expr_const___override(x_525, x_524);
x_527 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_528 = lean_array_push(x_527, x_66);
x_529 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_530 = lean_array_push(x_528, x_529);
lean_inc(x_52);
x_531 = lean_array_push(x_530, x_52);
x_532 = l_Lean_mkAppN(x_526, x_531);
lean_dec(x_531);
x_533 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_534 = 0;
lean_inc(x_66);
x_535 = l_Lean_Expr_forallE___override(x_533, x_66, x_532, x_534);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_536 = l_Lean_Meta_trySynthInstance(x_535, x_129, x_3, x_4, x_5, x_6, x_521);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
if (lean_obj_tag(x_537) == 1)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_ctor_get(x_537, 0);
lean_inc(x_539);
lean_dec(x_537);
x_540 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_541 = l_Lean_Expr_const___override(x_540, x_134);
x_542 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_543 = lean_array_push(x_542, x_65);
x_544 = lean_array_push(x_543, x_51);
x_545 = lean_array_push(x_544, x_66);
x_546 = lean_array_push(x_545, x_52);
x_547 = lean_array_push(x_546, x_133);
x_548 = lean_array_push(x_547, x_539);
x_549 = lean_array_push(x_548, x_514);
x_550 = lean_array_push(x_549, x_1);
x_551 = l_Lean_mkAppN(x_541, x_550);
lean_dec(x_550);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_552 = l_Lean_Meta_expandCoe(x_551, x_3, x_4, x_5, x_6, x_538);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_553);
x_555 = lean_infer_type(x_553, x_3, x_4, x_5, x_6, x_554);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_558 = l_Lean_Meta_isExprDefEq(x_32, x_556, x_3, x_4, x_5, x_6, x_557);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; uint8_t x_560; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_unbox(x_559);
lean_dec(x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_553);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_562 = x_558;
} else {
 lean_dec_ref(x_558);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_129);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_564 = lean_ctor_get(x_558, 1);
lean_inc(x_564);
lean_dec(x_558);
x_565 = lean_box(0);
x_566 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_553, x_565, x_3, x_4, x_5, x_6, x_564);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_567);
lean_ctor_set(x_570, 1, x_568);
return x_570;
}
}
else
{
lean_object* x_571; lean_object* x_572; 
lean_dec(x_553);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_571 = lean_ctor_get(x_558, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_558, 1);
lean_inc(x_572);
lean_dec(x_558);
x_8 = x_571;
x_9 = x_572;
goto block_16;
}
}
else
{
lean_object* x_573; lean_object* x_574; 
lean_dec(x_553);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_573 = lean_ctor_get(x_555, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_555, 1);
lean_inc(x_574);
lean_dec(x_555);
x_8 = x_573;
x_9 = x_574;
goto block_16;
}
}
else
{
lean_object* x_575; lean_object* x_576; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_575 = lean_ctor_get(x_552, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_552, 1);
lean_inc(x_576);
lean_dec(x_552);
x_8 = x_575;
x_9 = x_576;
goto block_16;
}
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_537);
lean_dec(x_514);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_577 = lean_ctor_get(x_536, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 lean_ctor_release(x_536, 1);
 x_578 = x_536;
} else {
 lean_dec_ref(x_536);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_129);
lean_ctor_set(x_579, 1, x_577);
return x_579;
}
}
else
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_514);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_580 = lean_ctor_get(x_536, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_536, 1);
lean_inc(x_581);
lean_dec(x_536);
x_8 = x_580;
x_9 = x_581;
goto block_16;
}
}
else
{
lean_object* x_582; lean_object* x_583; 
lean_dec(x_518);
lean_dec(x_516);
lean_dec(x_514);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_582 = lean_ctor_get(x_519, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_519, 1);
lean_inc(x_583);
lean_dec(x_519);
x_8 = x_582;
x_9 = x_583;
goto block_16;
}
}
else
{
lean_object* x_584; lean_object* x_585; 
lean_dec(x_514);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_584 = lean_ctor_get(x_515, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_515, 1);
lean_inc(x_585);
lean_dec(x_515);
x_8 = x_584;
x_9 = x_585;
goto block_16;
}
}
}
else
{
lean_object* x_586; lean_object* x_587; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_586 = lean_ctor_get(x_508, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_508, 1);
lean_inc(x_587);
lean_dec(x_508);
x_8 = x_586;
x_9 = x_587;
goto block_16;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_588 = lean_ctor_get(x_504, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_589 = x_504;
} else {
 lean_dec_ref(x_504);
 x_589 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_500);
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_54);
lean_ctor_set(x_590, 1, x_588);
return x_590;
}
}
else
{
lean_object* x_591; lean_object* x_592; 
lean_dec(x_500);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_591 = lean_ctor_get(x_504, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_504, 1);
lean_inc(x_592);
lean_dec(x_504);
x_8 = x_591;
x_9 = x_592;
goto block_16;
}
}
else
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_500);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_593 = lean_ctor_get(x_501, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_501, 1);
lean_inc(x_594);
lean_dec(x_501);
x_8 = x_593;
x_9 = x_594;
goto block_16;
}
}
else
{
lean_object* x_595; lean_object* x_596; 
lean_dec(x_484);
lean_free_object(x_134);
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_595 = lean_ctor_get(x_486, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_486, 1);
lean_inc(x_596);
lean_dec(x_486);
x_8 = x_595;
x_9 = x_596;
goto block_16;
}
}
}
else
{
lean_object* x_597; lean_object* x_598; 
lean_free_object(x_134);
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_597 = lean_ctor_get(x_138, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_138, 1);
lean_inc(x_598);
lean_dec(x_138);
x_8 = x_597;
x_9 = x_598;
goto block_16;
}
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_134, 0);
x_600 = lean_ctor_get(x_134, 1);
lean_inc(x_600);
lean_inc(x_599);
lean_dec(x_134);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_601 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_600);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_604 = x_601;
} else {
 lean_dec_ref(x_601);
 x_604 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_605 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_603);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_608 = x_605;
} else {
 lean_dec_ref(x_605);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_608;
 lean_ctor_set_tag(x_609, 1);
}
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_122);
if (lean_is_scalar(x_604)) {
 x_610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_610 = x_604;
 lean_ctor_set_tag(x_610, 1);
}
lean_ctor_set(x_610, 0, x_602);
lean_ctor_set(x_610, 1, x_609);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_599);
lean_ctor_set(x_611, 1, x_610);
x_612 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_611);
x_613 = l_Lean_Expr_const___override(x_612, x_611);
x_614 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_65);
x_615 = lean_array_push(x_614, x_65);
lean_inc(x_51);
x_616 = lean_array_push(x_615, x_51);
lean_inc(x_133);
x_617 = lean_array_push(x_616, x_133);
lean_inc(x_66);
x_618 = lean_array_push(x_617, x_66);
lean_inc(x_1);
x_619 = lean_array_push(x_618, x_1);
x_620 = l_Lean_mkAppN(x_613, x_619);
lean_dec(x_619);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_620);
x_621 = lean_infer_type(x_620, x_3, x_4, x_5, x_6, x_607);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_624 = l_Lean_Meta_isExprDefEq(x_32, x_622, x_3, x_4, x_5, x_6, x_623);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; uint8_t x_626; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_unbox(x_625);
lean_dec(x_625);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; 
lean_dec(x_620);
lean_free_object(x_54);
x_627 = lean_ctor_get(x_624, 1);
lean_inc(x_627);
lean_dec(x_624);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_628 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_627);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 lean_ctor_release(x_628, 1);
 x_631 = x_628;
} else {
 lean_dec_ref(x_628);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_129);
lean_ctor_set(x_632, 1, x_630);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_628, 1);
lean_inc(x_633);
lean_dec(x_628);
x_634 = lean_ctor_get(x_629, 0);
lean_inc(x_634);
lean_dec(x_629);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_635 = l_Lean_Meta_getLevel(x_66, x_3, x_4, x_5, x_6, x_633);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_638 = x_635;
} else {
 lean_dec_ref(x_635);
 x_638 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_639 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_637);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; lean_object* x_655; lean_object* x_656; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_642 = x_639;
} else {
 lean_dec_ref(x_639);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_642;
 lean_ctor_set_tag(x_643, 1);
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_122);
if (lean_is_scalar(x_638)) {
 x_644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_644 = x_638;
 lean_ctor_set_tag(x_644, 1);
}
lean_ctor_set(x_644, 0, x_636);
lean_ctor_set(x_644, 1, x_643);
x_645 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_646 = l_Lean_Expr_const___override(x_645, x_644);
x_647 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_648 = lean_array_push(x_647, x_66);
x_649 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_650 = lean_array_push(x_648, x_649);
lean_inc(x_52);
x_651 = lean_array_push(x_650, x_52);
x_652 = l_Lean_mkAppN(x_646, x_651);
lean_dec(x_651);
x_653 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_654 = 0;
lean_inc(x_66);
x_655 = l_Lean_Expr_forallE___override(x_653, x_66, x_652, x_654);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_656 = l_Lean_Meta_trySynthInstance(x_655, x_129, x_3, x_4, x_5, x_6, x_641);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
if (lean_obj_tag(x_657) == 1)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_659 = lean_ctor_get(x_657, 0);
lean_inc(x_659);
lean_dec(x_657);
x_660 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_661 = l_Lean_Expr_const___override(x_660, x_611);
x_662 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_663 = lean_array_push(x_662, x_65);
x_664 = lean_array_push(x_663, x_51);
x_665 = lean_array_push(x_664, x_66);
x_666 = lean_array_push(x_665, x_52);
x_667 = lean_array_push(x_666, x_133);
x_668 = lean_array_push(x_667, x_659);
x_669 = lean_array_push(x_668, x_634);
x_670 = lean_array_push(x_669, x_1);
x_671 = l_Lean_mkAppN(x_661, x_670);
lean_dec(x_670);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_672 = l_Lean_Meta_expandCoe(x_671, x_3, x_4, x_5, x_6, x_658);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_673);
x_675 = lean_infer_type(x_673, x_3, x_4, x_5, x_6, x_674);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_678 = l_Lean_Meta_isExprDefEq(x_32, x_676, x_3, x_4, x_5, x_6, x_677);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; uint8_t x_680; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_unbox(x_679);
lean_dec(x_679);
if (x_680 == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_673);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_681 = lean_ctor_get(x_678, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_682 = x_678;
} else {
 lean_dec_ref(x_678);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_682)) {
 x_683 = lean_alloc_ctor(0, 2, 0);
} else {
 x_683 = x_682;
}
lean_ctor_set(x_683, 0, x_129);
lean_ctor_set(x_683, 1, x_681);
return x_683;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_684 = lean_ctor_get(x_678, 1);
lean_inc(x_684);
lean_dec(x_678);
x_685 = lean_box(0);
x_686 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_673, x_685, x_3, x_4, x_5, x_6, x_684);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_689 = x_686;
} else {
 lean_dec_ref(x_686);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
}
else
{
lean_object* x_691; lean_object* x_692; 
lean_dec(x_673);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_691 = lean_ctor_get(x_678, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_678, 1);
lean_inc(x_692);
lean_dec(x_678);
x_8 = x_691;
x_9 = x_692;
goto block_16;
}
}
else
{
lean_object* x_693; lean_object* x_694; 
lean_dec(x_673);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_693 = lean_ctor_get(x_675, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_675, 1);
lean_inc(x_694);
lean_dec(x_675);
x_8 = x_693;
x_9 = x_694;
goto block_16;
}
}
else
{
lean_object* x_695; lean_object* x_696; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_695 = lean_ctor_get(x_672, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_672, 1);
lean_inc(x_696);
lean_dec(x_672);
x_8 = x_695;
x_9 = x_696;
goto block_16;
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_657);
lean_dec(x_634);
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_697 = lean_ctor_get(x_656, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 lean_ctor_release(x_656, 1);
 x_698 = x_656;
} else {
 lean_dec_ref(x_656);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_129);
lean_ctor_set(x_699, 1, x_697);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; 
lean_dec(x_634);
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_700 = lean_ctor_get(x_656, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_656, 1);
lean_inc(x_701);
lean_dec(x_656);
x_8 = x_700;
x_9 = x_701;
goto block_16;
}
}
else
{
lean_object* x_702; lean_object* x_703; 
lean_dec(x_638);
lean_dec(x_636);
lean_dec(x_634);
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_702 = lean_ctor_get(x_639, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_639, 1);
lean_inc(x_703);
lean_dec(x_639);
x_8 = x_702;
x_9 = x_703;
goto block_16;
}
}
else
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_634);
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_704 = lean_ctor_get(x_635, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_635, 1);
lean_inc(x_705);
lean_dec(x_635);
x_8 = x_704;
x_9 = x_705;
goto block_16;
}
}
}
else
{
lean_object* x_706; lean_object* x_707; 
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_706 = lean_ctor_get(x_628, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_628, 1);
lean_inc(x_707);
lean_dec(x_628);
x_8 = x_706;
x_9 = x_707;
goto block_16;
}
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; 
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_708 = lean_ctor_get(x_624, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_709 = x_624;
} else {
 lean_dec_ref(x_624);
 x_709 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_620);
if (lean_is_scalar(x_709)) {
 x_710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_710 = x_709;
}
lean_ctor_set(x_710, 0, x_54);
lean_ctor_set(x_710, 1, x_708);
return x_710;
}
}
else
{
lean_object* x_711; lean_object* x_712; 
lean_dec(x_620);
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_711 = lean_ctor_get(x_624, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_624, 1);
lean_inc(x_712);
lean_dec(x_624);
x_8 = x_711;
x_9 = x_712;
goto block_16;
}
}
else
{
lean_object* x_713; lean_object* x_714; 
lean_dec(x_620);
lean_dec(x_611);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_713 = lean_ctor_get(x_621, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_621, 1);
lean_inc(x_714);
lean_dec(x_621);
x_8 = x_713;
x_9 = x_714;
goto block_16;
}
}
else
{
lean_object* x_715; lean_object* x_716; 
lean_dec(x_604);
lean_dec(x_602);
lean_dec(x_599);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_715 = lean_ctor_get(x_605, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_605, 1);
lean_inc(x_716);
lean_dec(x_605);
x_8 = x_715;
x_9 = x_716;
goto block_16;
}
}
else
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_599);
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_717 = lean_ctor_get(x_601, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_601, 1);
lean_inc(x_718);
lean_dec(x_601);
x_8 = x_717;
x_9 = x_718;
goto block_16;
}
}
}
else
{
lean_object* x_719; lean_object* x_720; 
lean_dec(x_133);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_719 = lean_ctor_get(x_134, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_134, 1);
lean_inc(x_720);
lean_dec(x_134);
x_8 = x_719;
x_9 = x_720;
goto block_16;
}
}
else
{
uint8_t x_721; 
lean_dec(x_131);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_721 = !lean_is_exclusive(x_130);
if (x_721 == 0)
{
lean_object* x_722; 
x_722 = lean_ctor_get(x_130, 0);
lean_dec(x_722);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
else
{
lean_object* x_723; lean_object* x_724; 
x_723 = lean_ctor_get(x_130, 1);
lean_inc(x_723);
lean_dec(x_130);
x_724 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_724, 0, x_129);
lean_ctor_set(x_724, 1, x_723);
return x_724;
}
}
}
else
{
lean_object* x_725; lean_object* x_726; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_725 = lean_ctor_get(x_130, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_130, 1);
lean_inc(x_726);
lean_dec(x_130);
x_8 = x_725;
x_9 = x_726;
goto block_16;
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_727 = lean_ctor_get(x_119, 0);
x_728 = lean_ctor_get(x_119, 1);
lean_inc(x_728);
lean_inc(x_727);
lean_dec(x_119);
x_729 = lean_box(0);
x_730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_730, 0, x_727);
lean_ctor_set(x_730, 1, x_729);
lean_ctor_set_tag(x_115, 1);
lean_ctor_set(x_115, 1, x_730);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_115);
lean_ctor_set(x_100, 0, x_98);
x_731 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_732 = l_Lean_Expr_const___override(x_731, x_100);
x_733 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_65);
x_734 = lean_array_push(x_733, x_65);
lean_inc(x_51);
x_735 = lean_array_push(x_734, x_51);
x_736 = l_Lean_mkAppN(x_732, x_735);
lean_dec(x_735);
x_737 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_738 = l_Lean_Meta_trySynthInstance(x_736, x_737, x_3, x_4, x_5, x_6, x_728);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
if (lean_obj_tag(x_739) == 1)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
lean_dec(x_738);
x_741 = lean_ctor_get(x_739, 0);
lean_inc(x_741);
lean_dec(x_739);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_742 = l_Lean_Meta_getDecLevel(x_66, x_3, x_4, x_5, x_6, x_740);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_745 = x_742;
} else {
 lean_dec_ref(x_742);
 x_745 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_746 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_744);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_746)) {
 lean_ctor_release(x_746, 0);
 lean_ctor_release(x_746, 1);
 x_749 = x_746;
} else {
 lean_dec_ref(x_746);
 x_749 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_750 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_748);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
if (lean_is_exclusive(x_750)) {
 lean_ctor_release(x_750, 0);
 lean_ctor_release(x_750, 1);
 x_753 = x_750;
} else {
 lean_dec_ref(x_750);
 x_753 = lean_box(0);
}
if (lean_is_scalar(x_753)) {
 x_754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_754 = x_753;
 lean_ctor_set_tag(x_754, 1);
}
lean_ctor_set(x_754, 0, x_751);
lean_ctor_set(x_754, 1, x_729);
if (lean_is_scalar(x_749)) {
 x_755 = lean_alloc_ctor(1, 2, 0);
} else {
 x_755 = x_749;
 lean_ctor_set_tag(x_755, 1);
}
lean_ctor_set(x_755, 0, x_747);
lean_ctor_set(x_755, 1, x_754);
if (lean_is_scalar(x_745)) {
 x_756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_756 = x_745;
 lean_ctor_set_tag(x_756, 1);
}
lean_ctor_set(x_756, 0, x_743);
lean_ctor_set(x_756, 1, x_755);
x_757 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_756);
x_758 = l_Lean_Expr_const___override(x_757, x_756);
x_759 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_65);
x_760 = lean_array_push(x_759, x_65);
lean_inc(x_51);
x_761 = lean_array_push(x_760, x_51);
lean_inc(x_741);
x_762 = lean_array_push(x_761, x_741);
lean_inc(x_66);
x_763 = lean_array_push(x_762, x_66);
lean_inc(x_1);
x_764 = lean_array_push(x_763, x_1);
x_765 = l_Lean_mkAppN(x_758, x_764);
lean_dec(x_764);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_765);
x_766 = lean_infer_type(x_765, x_3, x_4, x_5, x_6, x_752);
if (lean_obj_tag(x_766) == 0)
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
lean_dec(x_766);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_769 = l_Lean_Meta_isExprDefEq(x_32, x_767, x_3, x_4, x_5, x_6, x_768);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; uint8_t x_771; 
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
x_771 = lean_unbox(x_770);
lean_dec(x_770);
if (x_771 == 0)
{
lean_object* x_772; lean_object* x_773; 
lean_dec(x_765);
lean_free_object(x_54);
x_772 = lean_ctor_get(x_769, 1);
lean_inc(x_772);
lean_dec(x_769);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_773 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_772);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; 
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_776 = x_773;
} else {
 lean_dec_ref(x_773);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(0, 2, 0);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_737);
lean_ctor_set(x_777, 1, x_775);
return x_777;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_773, 1);
lean_inc(x_778);
lean_dec(x_773);
x_779 = lean_ctor_get(x_774, 0);
lean_inc(x_779);
lean_dec(x_774);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_780 = l_Lean_Meta_getLevel(x_66, x_3, x_4, x_5, x_6, x_778);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_784 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_782);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; uint8_t x_799; lean_object* x_800; lean_object* x_801; 
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_784)) {
 lean_ctor_release(x_784, 0);
 lean_ctor_release(x_784, 1);
 x_787 = x_784;
} else {
 lean_dec_ref(x_784);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_787)) {
 x_788 = lean_alloc_ctor(1, 2, 0);
} else {
 x_788 = x_787;
 lean_ctor_set_tag(x_788, 1);
}
lean_ctor_set(x_788, 0, x_785);
lean_ctor_set(x_788, 1, x_729);
if (lean_is_scalar(x_783)) {
 x_789 = lean_alloc_ctor(1, 2, 0);
} else {
 x_789 = x_783;
 lean_ctor_set_tag(x_789, 1);
}
lean_ctor_set(x_789, 0, x_781);
lean_ctor_set(x_789, 1, x_788);
x_790 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_791 = l_Lean_Expr_const___override(x_790, x_789);
x_792 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_793 = lean_array_push(x_792, x_66);
x_794 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_795 = lean_array_push(x_793, x_794);
lean_inc(x_52);
x_796 = lean_array_push(x_795, x_52);
x_797 = l_Lean_mkAppN(x_791, x_796);
lean_dec(x_796);
x_798 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_799 = 0;
lean_inc(x_66);
x_800 = l_Lean_Expr_forallE___override(x_798, x_66, x_797, x_799);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_801 = l_Lean_Meta_trySynthInstance(x_800, x_737, x_3, x_4, x_5, x_6, x_786);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
if (lean_obj_tag(x_802) == 1)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
lean_dec(x_801);
x_804 = lean_ctor_get(x_802, 0);
lean_inc(x_804);
lean_dec(x_802);
x_805 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_806 = l_Lean_Expr_const___override(x_805, x_756);
x_807 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_808 = lean_array_push(x_807, x_65);
x_809 = lean_array_push(x_808, x_51);
x_810 = lean_array_push(x_809, x_66);
x_811 = lean_array_push(x_810, x_52);
x_812 = lean_array_push(x_811, x_741);
x_813 = lean_array_push(x_812, x_804);
x_814 = lean_array_push(x_813, x_779);
x_815 = lean_array_push(x_814, x_1);
x_816 = l_Lean_mkAppN(x_806, x_815);
lean_dec(x_815);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_817 = l_Lean_Meta_expandCoe(x_816, x_3, x_4, x_5, x_6, x_803);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
lean_dec(x_817);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_818);
x_820 = lean_infer_type(x_818, x_3, x_4, x_5, x_6, x_819);
if (lean_obj_tag(x_820) == 0)
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_820, 1);
lean_inc(x_822);
lean_dec(x_820);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_823 = l_Lean_Meta_isExprDefEq(x_32, x_821, x_3, x_4, x_5, x_6, x_822);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; uint8_t x_825; 
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
x_825 = lean_unbox(x_824);
lean_dec(x_824);
if (x_825 == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec(x_818);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_826 = lean_ctor_get(x_823, 1);
lean_inc(x_826);
if (lean_is_exclusive(x_823)) {
 lean_ctor_release(x_823, 0);
 lean_ctor_release(x_823, 1);
 x_827 = x_823;
} else {
 lean_dec_ref(x_823);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_737);
lean_ctor_set(x_828, 1, x_826);
return x_828;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_829 = lean_ctor_get(x_823, 1);
lean_inc(x_829);
lean_dec(x_823);
x_830 = lean_box(0);
x_831 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_818, x_830, x_3, x_4, x_5, x_6, x_829);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_831, 1);
lean_inc(x_833);
if (lean_is_exclusive(x_831)) {
 lean_ctor_release(x_831, 0);
 lean_ctor_release(x_831, 1);
 x_834 = x_831;
} else {
 lean_dec_ref(x_831);
 x_834 = lean_box(0);
}
if (lean_is_scalar(x_834)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_834;
}
lean_ctor_set(x_835, 0, x_832);
lean_ctor_set(x_835, 1, x_833);
return x_835;
}
}
else
{
lean_object* x_836; lean_object* x_837; 
lean_dec(x_818);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_836 = lean_ctor_get(x_823, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_823, 1);
lean_inc(x_837);
lean_dec(x_823);
x_8 = x_836;
x_9 = x_837;
goto block_16;
}
}
else
{
lean_object* x_838; lean_object* x_839; 
lean_dec(x_818);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_838 = lean_ctor_get(x_820, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_820, 1);
lean_inc(x_839);
lean_dec(x_820);
x_8 = x_838;
x_9 = x_839;
goto block_16;
}
}
else
{
lean_object* x_840; lean_object* x_841; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_840 = lean_ctor_get(x_817, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_817, 1);
lean_inc(x_841);
lean_dec(x_817);
x_8 = x_840;
x_9 = x_841;
goto block_16;
}
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_802);
lean_dec(x_779);
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_842 = lean_ctor_get(x_801, 1);
lean_inc(x_842);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_843 = x_801;
} else {
 lean_dec_ref(x_801);
 x_843 = lean_box(0);
}
if (lean_is_scalar(x_843)) {
 x_844 = lean_alloc_ctor(0, 2, 0);
} else {
 x_844 = x_843;
}
lean_ctor_set(x_844, 0, x_737);
lean_ctor_set(x_844, 1, x_842);
return x_844;
}
}
else
{
lean_object* x_845; lean_object* x_846; 
lean_dec(x_779);
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_845 = lean_ctor_get(x_801, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_801, 1);
lean_inc(x_846);
lean_dec(x_801);
x_8 = x_845;
x_9 = x_846;
goto block_16;
}
}
else
{
lean_object* x_847; lean_object* x_848; 
lean_dec(x_783);
lean_dec(x_781);
lean_dec(x_779);
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_847 = lean_ctor_get(x_784, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_784, 1);
lean_inc(x_848);
lean_dec(x_784);
x_8 = x_847;
x_9 = x_848;
goto block_16;
}
}
else
{
lean_object* x_849; lean_object* x_850; 
lean_dec(x_779);
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_849 = lean_ctor_get(x_780, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_780, 1);
lean_inc(x_850);
lean_dec(x_780);
x_8 = x_849;
x_9 = x_850;
goto block_16;
}
}
}
else
{
lean_object* x_851; lean_object* x_852; 
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_851 = lean_ctor_get(x_773, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_773, 1);
lean_inc(x_852);
lean_dec(x_773);
x_8 = x_851;
x_9 = x_852;
goto block_16;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_853 = lean_ctor_get(x_769, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_854 = x_769;
} else {
 lean_dec_ref(x_769);
 x_854 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_765);
if (lean_is_scalar(x_854)) {
 x_855 = lean_alloc_ctor(0, 2, 0);
} else {
 x_855 = x_854;
}
lean_ctor_set(x_855, 0, x_54);
lean_ctor_set(x_855, 1, x_853);
return x_855;
}
}
else
{
lean_object* x_856; lean_object* x_857; 
lean_dec(x_765);
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_856 = lean_ctor_get(x_769, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_769, 1);
lean_inc(x_857);
lean_dec(x_769);
x_8 = x_856;
x_9 = x_857;
goto block_16;
}
}
else
{
lean_object* x_858; lean_object* x_859; 
lean_dec(x_765);
lean_dec(x_756);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_858 = lean_ctor_get(x_766, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_766, 1);
lean_inc(x_859);
lean_dec(x_766);
x_8 = x_858;
x_9 = x_859;
goto block_16;
}
}
else
{
lean_object* x_860; lean_object* x_861; 
lean_dec(x_749);
lean_dec(x_747);
lean_dec(x_745);
lean_dec(x_743);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_860 = lean_ctor_get(x_750, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_750, 1);
lean_inc(x_861);
lean_dec(x_750);
x_8 = x_860;
x_9 = x_861;
goto block_16;
}
}
else
{
lean_object* x_862; lean_object* x_863; 
lean_dec(x_745);
lean_dec(x_743);
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_862 = lean_ctor_get(x_746, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_746, 1);
lean_inc(x_863);
lean_dec(x_746);
x_8 = x_862;
x_9 = x_863;
goto block_16;
}
}
else
{
lean_object* x_864; lean_object* x_865; 
lean_dec(x_741);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_864 = lean_ctor_get(x_742, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_742, 1);
lean_inc(x_865);
lean_dec(x_742);
x_8 = x_864;
x_9 = x_865;
goto block_16;
}
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_739);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_866 = lean_ctor_get(x_738, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 x_867 = x_738;
} else {
 lean_dec_ref(x_738);
 x_867 = lean_box(0);
}
if (lean_is_scalar(x_867)) {
 x_868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_868 = x_867;
}
lean_ctor_set(x_868, 0, x_737);
lean_ctor_set(x_868, 1, x_866);
return x_868;
}
}
else
{
lean_object* x_869; lean_object* x_870; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_869 = lean_ctor_get(x_738, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_738, 1);
lean_inc(x_870);
lean_dec(x_738);
x_8 = x_869;
x_9 = x_870;
goto block_16;
}
}
}
else
{
lean_object* x_871; lean_object* x_872; 
lean_free_object(x_115);
lean_dec(x_117);
lean_free_object(x_100);
lean_dec(x_98);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_871 = lean_ctor_get(x_119, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_119, 1);
lean_inc(x_872);
lean_dec(x_119);
x_8 = x_871;
x_9 = x_872;
goto block_16;
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_115, 0);
x_874 = lean_ctor_get(x_115, 1);
lean_inc(x_874);
lean_inc(x_873);
lean_dec(x_115);
x_875 = l_Lean_Meta_decLevel(x_96, x_3, x_4, x_5, x_6, x_874);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_878 = x_875;
} else {
 lean_dec_ref(x_875);
 x_878 = lean_box(0);
}
x_879 = lean_box(0);
if (lean_is_scalar(x_878)) {
 x_880 = lean_alloc_ctor(1, 2, 0);
} else {
 x_880 = x_878;
 lean_ctor_set_tag(x_880, 1);
}
lean_ctor_set(x_880, 0, x_876);
lean_ctor_set(x_880, 1, x_879);
x_881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_881, 0, x_873);
lean_ctor_set(x_881, 1, x_880);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_881);
lean_ctor_set(x_100, 0, x_98);
x_882 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_883 = l_Lean_Expr_const___override(x_882, x_100);
x_884 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_65);
x_885 = lean_array_push(x_884, x_65);
lean_inc(x_51);
x_886 = lean_array_push(x_885, x_51);
x_887 = l_Lean_mkAppN(x_883, x_886);
lean_dec(x_886);
x_888 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_889 = l_Lean_Meta_trySynthInstance(x_887, x_888, x_3, x_4, x_5, x_6, x_877);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
if (lean_obj_tag(x_890) == 1)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
lean_dec(x_889);
x_892 = lean_ctor_get(x_890, 0);
lean_inc(x_892);
lean_dec(x_890);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_893 = l_Lean_Meta_getDecLevel(x_66, x_3, x_4, x_5, x_6, x_891);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_896 = x_893;
} else {
 lean_dec_ref(x_893);
 x_896 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_897 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_895);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_900 = x_897;
} else {
 lean_dec_ref(x_897);
 x_900 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_901 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_899);
if (lean_obj_tag(x_901) == 0)
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
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
 x_905 = lean_alloc_ctor(1, 2, 0);
} else {
 x_905 = x_904;
 lean_ctor_set_tag(x_905, 1);
}
lean_ctor_set(x_905, 0, x_902);
lean_ctor_set(x_905, 1, x_879);
if (lean_is_scalar(x_900)) {
 x_906 = lean_alloc_ctor(1, 2, 0);
} else {
 x_906 = x_900;
 lean_ctor_set_tag(x_906, 1);
}
lean_ctor_set(x_906, 0, x_898);
lean_ctor_set(x_906, 1, x_905);
if (lean_is_scalar(x_896)) {
 x_907 = lean_alloc_ctor(1, 2, 0);
} else {
 x_907 = x_896;
 lean_ctor_set_tag(x_907, 1);
}
lean_ctor_set(x_907, 0, x_894);
lean_ctor_set(x_907, 1, x_906);
x_908 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_907);
x_909 = l_Lean_Expr_const___override(x_908, x_907);
x_910 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_65);
x_911 = lean_array_push(x_910, x_65);
lean_inc(x_51);
x_912 = lean_array_push(x_911, x_51);
lean_inc(x_892);
x_913 = lean_array_push(x_912, x_892);
lean_inc(x_66);
x_914 = lean_array_push(x_913, x_66);
lean_inc(x_1);
x_915 = lean_array_push(x_914, x_1);
x_916 = l_Lean_mkAppN(x_909, x_915);
lean_dec(x_915);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_916);
x_917 = lean_infer_type(x_916, x_3, x_4, x_5, x_6, x_903);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
lean_dec(x_917);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_920 = l_Lean_Meta_isExprDefEq(x_32, x_918, x_3, x_4, x_5, x_6, x_919);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; uint8_t x_922; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_unbox(x_921);
lean_dec(x_921);
if (x_922 == 0)
{
lean_object* x_923; lean_object* x_924; 
lean_dec(x_916);
lean_free_object(x_54);
x_923 = lean_ctor_get(x_920, 1);
lean_inc(x_923);
lean_dec(x_920);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_924 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_923);
if (lean_obj_tag(x_924) == 0)
{
lean_object* x_925; 
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
if (lean_obj_tag(x_925) == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_926 = lean_ctor_get(x_924, 1);
lean_inc(x_926);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 lean_ctor_release(x_924, 1);
 x_927 = x_924;
} else {
 lean_dec_ref(x_924);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(0, 2, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_888);
lean_ctor_set(x_928, 1, x_926);
return x_928;
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_929 = lean_ctor_get(x_924, 1);
lean_inc(x_929);
lean_dec(x_924);
x_930 = lean_ctor_get(x_925, 0);
lean_inc(x_930);
lean_dec(x_925);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_931 = l_Lean_Meta_getLevel(x_66, x_3, x_4, x_5, x_6, x_929);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_931, 1);
lean_inc(x_933);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_934 = x_931;
} else {
 lean_dec_ref(x_931);
 x_934 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_935 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_933);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; uint8_t x_950; lean_object* x_951; lean_object* x_952; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_938 = x_935;
} else {
 lean_dec_ref(x_935);
 x_938 = lean_box(0);
}
if (lean_is_scalar(x_938)) {
 x_939 = lean_alloc_ctor(1, 2, 0);
} else {
 x_939 = x_938;
 lean_ctor_set_tag(x_939, 1);
}
lean_ctor_set(x_939, 0, x_936);
lean_ctor_set(x_939, 1, x_879);
if (lean_is_scalar(x_934)) {
 x_940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_940 = x_934;
 lean_ctor_set_tag(x_940, 1);
}
lean_ctor_set(x_940, 0, x_932);
lean_ctor_set(x_940, 1, x_939);
x_941 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_942 = l_Lean_Expr_const___override(x_941, x_940);
x_943 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_944 = lean_array_push(x_943, x_66);
x_945 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_946 = lean_array_push(x_944, x_945);
lean_inc(x_52);
x_947 = lean_array_push(x_946, x_52);
x_948 = l_Lean_mkAppN(x_942, x_947);
lean_dec(x_947);
x_949 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_950 = 0;
lean_inc(x_66);
x_951 = l_Lean_Expr_forallE___override(x_949, x_66, x_948, x_950);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_952 = l_Lean_Meta_trySynthInstance(x_951, x_888, x_3, x_4, x_5, x_6, x_937);
if (lean_obj_tag(x_952) == 0)
{
lean_object* x_953; 
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
if (lean_obj_tag(x_953) == 1)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_954 = lean_ctor_get(x_952, 1);
lean_inc(x_954);
lean_dec(x_952);
x_955 = lean_ctor_get(x_953, 0);
lean_inc(x_955);
lean_dec(x_953);
x_956 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_957 = l_Lean_Expr_const___override(x_956, x_907);
x_958 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_959 = lean_array_push(x_958, x_65);
x_960 = lean_array_push(x_959, x_51);
x_961 = lean_array_push(x_960, x_66);
x_962 = lean_array_push(x_961, x_52);
x_963 = lean_array_push(x_962, x_892);
x_964 = lean_array_push(x_963, x_955);
x_965 = lean_array_push(x_964, x_930);
x_966 = lean_array_push(x_965, x_1);
x_967 = l_Lean_mkAppN(x_957, x_966);
lean_dec(x_966);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_968 = l_Lean_Meta_expandCoe(x_967, x_3, x_4, x_5, x_6, x_954);
if (lean_obj_tag(x_968) == 0)
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; 
x_969 = lean_ctor_get(x_968, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_968, 1);
lean_inc(x_970);
lean_dec(x_968);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_969);
x_971 = lean_infer_type(x_969, x_3, x_4, x_5, x_6, x_970);
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_972 = lean_ctor_get(x_971, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_971, 1);
lean_inc(x_973);
lean_dec(x_971);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_974 = l_Lean_Meta_isExprDefEq(x_32, x_972, x_3, x_4, x_5, x_6, x_973);
if (lean_obj_tag(x_974) == 0)
{
lean_object* x_975; uint8_t x_976; 
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_unbox(x_975);
lean_dec(x_975);
if (x_976 == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; 
lean_dec(x_969);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_977 = lean_ctor_get(x_974, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_978 = x_974;
} else {
 lean_dec_ref(x_974);
 x_978 = lean_box(0);
}
if (lean_is_scalar(x_978)) {
 x_979 = lean_alloc_ctor(0, 2, 0);
} else {
 x_979 = x_978;
}
lean_ctor_set(x_979, 0, x_888);
lean_ctor_set(x_979, 1, x_977);
return x_979;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_980 = lean_ctor_get(x_974, 1);
lean_inc(x_980);
lean_dec(x_974);
x_981 = lean_box(0);
x_982 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_969, x_981, x_3, x_4, x_5, x_6, x_980);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_985)) {
 x_986 = lean_alloc_ctor(0, 2, 0);
} else {
 x_986 = x_985;
}
lean_ctor_set(x_986, 0, x_983);
lean_ctor_set(x_986, 1, x_984);
return x_986;
}
}
else
{
lean_object* x_987; lean_object* x_988; 
lean_dec(x_969);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_987 = lean_ctor_get(x_974, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_974, 1);
lean_inc(x_988);
lean_dec(x_974);
x_8 = x_987;
x_9 = x_988;
goto block_16;
}
}
else
{
lean_object* x_989; lean_object* x_990; 
lean_dec(x_969);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_989 = lean_ctor_get(x_971, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_971, 1);
lean_inc(x_990);
lean_dec(x_971);
x_8 = x_989;
x_9 = x_990;
goto block_16;
}
}
else
{
lean_object* x_991; lean_object* x_992; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_991 = lean_ctor_get(x_968, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_968, 1);
lean_inc(x_992);
lean_dec(x_968);
x_8 = x_991;
x_9 = x_992;
goto block_16;
}
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
lean_dec(x_953);
lean_dec(x_930);
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_993 = lean_ctor_get(x_952, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_994 = x_952;
} else {
 lean_dec_ref(x_952);
 x_994 = lean_box(0);
}
if (lean_is_scalar(x_994)) {
 x_995 = lean_alloc_ctor(0, 2, 0);
} else {
 x_995 = x_994;
}
lean_ctor_set(x_995, 0, x_888);
lean_ctor_set(x_995, 1, x_993);
return x_995;
}
}
else
{
lean_object* x_996; lean_object* x_997; 
lean_dec(x_930);
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_996 = lean_ctor_get(x_952, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_952, 1);
lean_inc(x_997);
lean_dec(x_952);
x_8 = x_996;
x_9 = x_997;
goto block_16;
}
}
else
{
lean_object* x_998; lean_object* x_999; 
lean_dec(x_934);
lean_dec(x_932);
lean_dec(x_930);
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_998 = lean_ctor_get(x_935, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_935, 1);
lean_inc(x_999);
lean_dec(x_935);
x_8 = x_998;
x_9 = x_999;
goto block_16;
}
}
else
{
lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_930);
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1000 = lean_ctor_get(x_931, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_931, 1);
lean_inc(x_1001);
lean_dec(x_931);
x_8 = x_1000;
x_9 = x_1001;
goto block_16;
}
}
}
else
{
lean_object* x_1002; lean_object* x_1003; 
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1002 = lean_ctor_get(x_924, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_924, 1);
lean_inc(x_1003);
lean_dec(x_924);
x_8 = x_1002;
x_9 = x_1003;
goto block_16;
}
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1004 = lean_ctor_get(x_920, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_1005 = x_920;
} else {
 lean_dec_ref(x_920);
 x_1005 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_916);
if (lean_is_scalar(x_1005)) {
 x_1006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1006 = x_1005;
}
lean_ctor_set(x_1006, 0, x_54);
lean_ctor_set(x_1006, 1, x_1004);
return x_1006;
}
}
else
{
lean_object* x_1007; lean_object* x_1008; 
lean_dec(x_916);
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1007 = lean_ctor_get(x_920, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_920, 1);
lean_inc(x_1008);
lean_dec(x_920);
x_8 = x_1007;
x_9 = x_1008;
goto block_16;
}
}
else
{
lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_916);
lean_dec(x_907);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1009 = lean_ctor_get(x_917, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_917, 1);
lean_inc(x_1010);
lean_dec(x_917);
x_8 = x_1009;
x_9 = x_1010;
goto block_16;
}
}
else
{
lean_object* x_1011; lean_object* x_1012; 
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_896);
lean_dec(x_894);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1011 = lean_ctor_get(x_901, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_901, 1);
lean_inc(x_1012);
lean_dec(x_901);
x_8 = x_1011;
x_9 = x_1012;
goto block_16;
}
}
else
{
lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_896);
lean_dec(x_894);
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1013 = lean_ctor_get(x_897, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_897, 1);
lean_inc(x_1014);
lean_dec(x_897);
x_8 = x_1013;
x_9 = x_1014;
goto block_16;
}
}
else
{
lean_object* x_1015; lean_object* x_1016; 
lean_dec(x_892);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1015 = lean_ctor_get(x_893, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_893, 1);
lean_inc(x_1016);
lean_dec(x_893);
x_8 = x_1015;
x_9 = x_1016;
goto block_16;
}
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
lean_dec(x_890);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1017 = lean_ctor_get(x_889, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_1018 = x_889;
} else {
 lean_dec_ref(x_889);
 x_1018 = lean_box(0);
}
if (lean_is_scalar(x_1018)) {
 x_1019 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1019 = x_1018;
}
lean_ctor_set(x_1019, 0, x_888);
lean_ctor_set(x_1019, 1, x_1017);
return x_1019;
}
}
else
{
lean_object* x_1020; lean_object* x_1021; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1020 = lean_ctor_get(x_889, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_889, 1);
lean_inc(x_1021);
lean_dec(x_889);
x_8 = x_1020;
x_9 = x_1021;
goto block_16;
}
}
else
{
lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_873);
lean_free_object(x_100);
lean_dec(x_98);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1022 = lean_ctor_get(x_875, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_875, 1);
lean_inc(x_1023);
lean_dec(x_875);
x_8 = x_1022;
x_9 = x_1023;
goto block_16;
}
}
}
else
{
lean_object* x_1024; lean_object* x_1025; 
lean_free_object(x_100);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1024 = lean_ctor_get(x_115, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_115, 1);
lean_inc(x_1025);
lean_dec(x_115);
x_8 = x_1024;
x_9 = x_1025;
goto block_16;
}
}
}
else
{
lean_object* x_1026; lean_object* x_1027; 
lean_free_object(x_100);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_86);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1026 = lean_ctor_get(x_105, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_105, 1);
lean_inc(x_1027);
lean_dec(x_105);
x_8 = x_1026;
x_9 = x_1027;
goto block_16;
}
}
else
{
lean_object* x_1028; lean_object* x_1029; uint8_t x_1030; lean_object* x_1031; 
x_1028 = lean_ctor_get(x_100, 0);
x_1029 = lean_ctor_get(x_100, 1);
lean_inc(x_1029);
lean_inc(x_1028);
lean_dec(x_100);
x_1030 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_98);
x_1031 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_98, x_1028, x_1030, x_3, x_4, x_5, x_6, x_1029);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; uint8_t x_1033; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_unbox(x_1032);
lean_dec(x_1032);
if (x_1033 == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_86);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1034 = lean_ctor_get(x_1031, 1);
lean_inc(x_1034);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1035 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1035 = lean_box(0);
}
x_1036 = lean_box(0);
if (lean_is_scalar(x_1035)) {
 x_1037 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1037 = x_1035;
}
lean_ctor_set(x_1037, 0, x_1036);
lean_ctor_set(x_1037, 1, x_1034);
return x_1037;
}
else
{
lean_object* x_1038; lean_object* x_1039; 
x_1038 = lean_ctor_get(x_1031, 1);
lean_inc(x_1038);
lean_dec(x_1031);
x_1039 = l_Lean_Meta_decLevel(x_86, x_3, x_4, x_5, x_6, x_1038);
if (lean_obj_tag(x_1039) == 0)
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1039, 1);
lean_inc(x_1041);
if (lean_is_exclusive(x_1039)) {
 lean_ctor_release(x_1039, 0);
 lean_ctor_release(x_1039, 1);
 x_1042 = x_1039;
} else {
 lean_dec_ref(x_1039);
 x_1042 = lean_box(0);
}
x_1043 = l_Lean_Meta_decLevel(x_96, x_3, x_4, x_5, x_6, x_1041);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1044 = lean_ctor_get(x_1043, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1043, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1046 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1046 = lean_box(0);
}
x_1047 = lean_box(0);
if (lean_is_scalar(x_1046)) {
 x_1048 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1048 = x_1046;
 lean_ctor_set_tag(x_1048, 1);
}
lean_ctor_set(x_1048, 0, x_1044);
lean_ctor_set(x_1048, 1, x_1047);
if (lean_is_scalar(x_1042)) {
 x_1049 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1049 = x_1042;
 lean_ctor_set_tag(x_1049, 1);
}
lean_ctor_set(x_1049, 0, x_1040);
lean_ctor_set(x_1049, 1, x_1048);
x_1050 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1050, 0, x_98);
lean_ctor_set(x_1050, 1, x_1049);
x_1051 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1052 = l_Lean_Expr_const___override(x_1051, x_1050);
x_1053 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_65);
x_1054 = lean_array_push(x_1053, x_65);
lean_inc(x_51);
x_1055 = lean_array_push(x_1054, x_51);
x_1056 = l_Lean_mkAppN(x_1052, x_1055);
lean_dec(x_1055);
x_1057 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1058 = l_Lean_Meta_trySynthInstance(x_1056, x_1057, x_3, x_4, x_5, x_6, x_1045);
if (lean_obj_tag(x_1058) == 0)
{
lean_object* x_1059; 
x_1059 = lean_ctor_get(x_1058, 0);
lean_inc(x_1059);
if (lean_obj_tag(x_1059) == 1)
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
x_1060 = lean_ctor_get(x_1058, 1);
lean_inc(x_1060);
lean_dec(x_1058);
x_1061 = lean_ctor_get(x_1059, 0);
lean_inc(x_1061);
lean_dec(x_1059);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_1062 = l_Lean_Meta_getDecLevel(x_66, x_3, x_4, x_5, x_6, x_1060);
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 lean_ctor_release(x_1062, 1);
 x_1065 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1065 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1066 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_1064);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1067 = lean_ctor_get(x_1066, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1066, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1069 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1069 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_1070 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_1068);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 lean_ctor_release(x_1070, 1);
 x_1073 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1073 = lean_box(0);
}
if (lean_is_scalar(x_1073)) {
 x_1074 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1074 = x_1073;
 lean_ctor_set_tag(x_1074, 1);
}
lean_ctor_set(x_1074, 0, x_1071);
lean_ctor_set(x_1074, 1, x_1047);
if (lean_is_scalar(x_1069)) {
 x_1075 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1075 = x_1069;
 lean_ctor_set_tag(x_1075, 1);
}
lean_ctor_set(x_1075, 0, x_1067);
lean_ctor_set(x_1075, 1, x_1074);
if (lean_is_scalar(x_1065)) {
 x_1076 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1076 = x_1065;
 lean_ctor_set_tag(x_1076, 1);
}
lean_ctor_set(x_1076, 0, x_1063);
lean_ctor_set(x_1076, 1, x_1075);
x_1077 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_1076);
x_1078 = l_Lean_Expr_const___override(x_1077, x_1076);
x_1079 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_65);
x_1080 = lean_array_push(x_1079, x_65);
lean_inc(x_51);
x_1081 = lean_array_push(x_1080, x_51);
lean_inc(x_1061);
x_1082 = lean_array_push(x_1081, x_1061);
lean_inc(x_66);
x_1083 = lean_array_push(x_1082, x_66);
lean_inc(x_1);
x_1084 = lean_array_push(x_1083, x_1);
x_1085 = l_Lean_mkAppN(x_1078, x_1084);
lean_dec(x_1084);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1085);
x_1086 = lean_infer_type(x_1085, x_3, x_4, x_5, x_6, x_1072);
if (lean_obj_tag(x_1086) == 0)
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1087 = lean_ctor_get(x_1086, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1086, 1);
lean_inc(x_1088);
lean_dec(x_1086);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_1089 = l_Lean_Meta_isExprDefEq(x_32, x_1087, x_3, x_4, x_5, x_6, x_1088);
if (lean_obj_tag(x_1089) == 0)
{
lean_object* x_1090; uint8_t x_1091; 
x_1090 = lean_ctor_get(x_1089, 0);
lean_inc(x_1090);
x_1091 = lean_unbox(x_1090);
lean_dec(x_1090);
if (x_1091 == 0)
{
lean_object* x_1092; lean_object* x_1093; 
lean_dec(x_1085);
lean_free_object(x_54);
x_1092 = lean_ctor_get(x_1089, 1);
lean_inc(x_1092);
lean_dec(x_1089);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_1093 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_1092);
if (lean_obj_tag(x_1093) == 0)
{
lean_object* x_1094; 
x_1094 = lean_ctor_get(x_1093, 0);
lean_inc(x_1094);
if (lean_obj_tag(x_1094) == 0)
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1095 = lean_ctor_get(x_1093, 1);
lean_inc(x_1095);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 x_1096 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1096 = lean_box(0);
}
if (lean_is_scalar(x_1096)) {
 x_1097 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1097 = x_1096;
}
lean_ctor_set(x_1097, 0, x_1057);
lean_ctor_set(x_1097, 1, x_1095);
return x_1097;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1098 = lean_ctor_get(x_1093, 1);
lean_inc(x_1098);
lean_dec(x_1093);
x_1099 = lean_ctor_get(x_1094, 0);
lean_inc(x_1099);
lean_dec(x_1094);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_1100 = l_Lean_Meta_getLevel(x_66, x_3, x_4, x_5, x_6, x_1098);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
if (lean_is_exclusive(x_1100)) {
 lean_ctor_release(x_1100, 0);
 lean_ctor_release(x_1100, 1);
 x_1103 = x_1100;
} else {
 lean_dec_ref(x_1100);
 x_1103 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_1104 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_1102);
if (lean_obj_tag(x_1104) == 0)
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; uint8_t x_1119; lean_object* x_1120; lean_object* x_1121; 
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
if (lean_is_scalar(x_1107)) {
 x_1108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1108 = x_1107;
 lean_ctor_set_tag(x_1108, 1);
}
lean_ctor_set(x_1108, 0, x_1105);
lean_ctor_set(x_1108, 1, x_1047);
if (lean_is_scalar(x_1103)) {
 x_1109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1109 = x_1103;
 lean_ctor_set_tag(x_1109, 1);
}
lean_ctor_set(x_1109, 0, x_1101);
lean_ctor_set(x_1109, 1, x_1108);
x_1110 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1111 = l_Lean_Expr_const___override(x_1110, x_1109);
x_1112 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_1113 = lean_array_push(x_1112, x_66);
x_1114 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_1115 = lean_array_push(x_1113, x_1114);
lean_inc(x_52);
x_1116 = lean_array_push(x_1115, x_52);
x_1117 = l_Lean_mkAppN(x_1111, x_1116);
lean_dec(x_1116);
x_1118 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_1119 = 0;
lean_inc(x_66);
x_1120 = l_Lean_Expr_forallE___override(x_1118, x_66, x_1117, x_1119);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1121 = l_Lean_Meta_trySynthInstance(x_1120, x_1057, x_3, x_4, x_5, x_6, x_1106);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
if (lean_obj_tag(x_1122) == 1)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1123 = lean_ctor_get(x_1121, 1);
lean_inc(x_1123);
lean_dec(x_1121);
x_1124 = lean_ctor_get(x_1122, 0);
lean_inc(x_1124);
lean_dec(x_1122);
x_1125 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_1126 = l_Lean_Expr_const___override(x_1125, x_1076);
x_1127 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_1128 = lean_array_push(x_1127, x_65);
x_1129 = lean_array_push(x_1128, x_51);
x_1130 = lean_array_push(x_1129, x_66);
x_1131 = lean_array_push(x_1130, x_52);
x_1132 = lean_array_push(x_1131, x_1061);
x_1133 = lean_array_push(x_1132, x_1124);
x_1134 = lean_array_push(x_1133, x_1099);
x_1135 = lean_array_push(x_1134, x_1);
x_1136 = l_Lean_mkAppN(x_1126, x_1135);
lean_dec(x_1135);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1137 = l_Lean_Meta_expandCoe(x_1136, x_3, x_4, x_5, x_6, x_1123);
if (lean_obj_tag(x_1137) == 0)
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
lean_dec(x_1137);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1138);
x_1140 = lean_infer_type(x_1138, x_3, x_4, x_5, x_6, x_1139);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
lean_dec(x_1140);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1143 = l_Lean_Meta_isExprDefEq(x_32, x_1141, x_3, x_4, x_5, x_6, x_1142);
if (lean_obj_tag(x_1143) == 0)
{
lean_object* x_1144; uint8_t x_1145; 
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
x_1145 = lean_unbox(x_1144);
lean_dec(x_1144);
if (x_1145 == 0)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
lean_dec(x_1138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1146 = lean_ctor_get(x_1143, 1);
lean_inc(x_1146);
if (lean_is_exclusive(x_1143)) {
 lean_ctor_release(x_1143, 0);
 lean_ctor_release(x_1143, 1);
 x_1147 = x_1143;
} else {
 lean_dec_ref(x_1143);
 x_1147 = lean_box(0);
}
if (lean_is_scalar(x_1147)) {
 x_1148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1148 = x_1147;
}
lean_ctor_set(x_1148, 0, x_1057);
lean_ctor_set(x_1148, 1, x_1146);
return x_1148;
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1149 = lean_ctor_get(x_1143, 1);
lean_inc(x_1149);
lean_dec(x_1143);
x_1150 = lean_box(0);
x_1151 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1138, x_1150, x_3, x_4, x_5, x_6, x_1149);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1152 = lean_ctor_get(x_1151, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1151, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_1151)) {
 lean_ctor_release(x_1151, 0);
 lean_ctor_release(x_1151, 1);
 x_1154 = x_1151;
} else {
 lean_dec_ref(x_1151);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_1152);
lean_ctor_set(x_1155, 1, x_1153);
return x_1155;
}
}
else
{
lean_object* x_1156; lean_object* x_1157; 
lean_dec(x_1138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1156 = lean_ctor_get(x_1143, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1143, 1);
lean_inc(x_1157);
lean_dec(x_1143);
x_8 = x_1156;
x_9 = x_1157;
goto block_16;
}
}
else
{
lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_1138);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1158 = lean_ctor_get(x_1140, 0);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1140, 1);
lean_inc(x_1159);
lean_dec(x_1140);
x_8 = x_1158;
x_9 = x_1159;
goto block_16;
}
}
else
{
lean_object* x_1160; lean_object* x_1161; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1160 = lean_ctor_get(x_1137, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1137, 1);
lean_inc(x_1161);
lean_dec(x_1137);
x_8 = x_1160;
x_9 = x_1161;
goto block_16;
}
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
lean_dec(x_1122);
lean_dec(x_1099);
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1162 = lean_ctor_get(x_1121, 1);
lean_inc(x_1162);
if (lean_is_exclusive(x_1121)) {
 lean_ctor_release(x_1121, 0);
 lean_ctor_release(x_1121, 1);
 x_1163 = x_1121;
} else {
 lean_dec_ref(x_1121);
 x_1163 = lean_box(0);
}
if (lean_is_scalar(x_1163)) {
 x_1164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1164 = x_1163;
}
lean_ctor_set(x_1164, 0, x_1057);
lean_ctor_set(x_1164, 1, x_1162);
return x_1164;
}
}
else
{
lean_object* x_1165; lean_object* x_1166; 
lean_dec(x_1099);
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1165 = lean_ctor_get(x_1121, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1121, 1);
lean_inc(x_1166);
lean_dec(x_1121);
x_8 = x_1165;
x_9 = x_1166;
goto block_16;
}
}
else
{
lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1103);
lean_dec(x_1101);
lean_dec(x_1099);
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1167 = lean_ctor_get(x_1104, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1104, 1);
lean_inc(x_1168);
lean_dec(x_1104);
x_8 = x_1167;
x_9 = x_1168;
goto block_16;
}
}
else
{
lean_object* x_1169; lean_object* x_1170; 
lean_dec(x_1099);
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1169 = lean_ctor_get(x_1100, 0);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1100, 1);
lean_inc(x_1170);
lean_dec(x_1100);
x_8 = x_1169;
x_9 = x_1170;
goto block_16;
}
}
}
else
{
lean_object* x_1171; lean_object* x_1172; 
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1171 = lean_ctor_get(x_1093, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1093, 1);
lean_inc(x_1172);
lean_dec(x_1093);
x_8 = x_1171;
x_9 = x_1172;
goto block_16;
}
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1173 = lean_ctor_get(x_1089, 1);
lean_inc(x_1173);
if (lean_is_exclusive(x_1089)) {
 lean_ctor_release(x_1089, 0);
 lean_ctor_release(x_1089, 1);
 x_1174 = x_1089;
} else {
 lean_dec_ref(x_1089);
 x_1174 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_1085);
if (lean_is_scalar(x_1174)) {
 x_1175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1175 = x_1174;
}
lean_ctor_set(x_1175, 0, x_54);
lean_ctor_set(x_1175, 1, x_1173);
return x_1175;
}
}
else
{
lean_object* x_1176; lean_object* x_1177; 
lean_dec(x_1085);
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1176 = lean_ctor_get(x_1089, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1089, 1);
lean_inc(x_1177);
lean_dec(x_1089);
x_8 = x_1176;
x_9 = x_1177;
goto block_16;
}
}
else
{
lean_object* x_1178; lean_object* x_1179; 
lean_dec(x_1085);
lean_dec(x_1076);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1178 = lean_ctor_get(x_1086, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1086, 1);
lean_inc(x_1179);
lean_dec(x_1086);
x_8 = x_1178;
x_9 = x_1179;
goto block_16;
}
}
else
{
lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_1069);
lean_dec(x_1067);
lean_dec(x_1065);
lean_dec(x_1063);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1180 = lean_ctor_get(x_1070, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1070, 1);
lean_inc(x_1181);
lean_dec(x_1070);
x_8 = x_1180;
x_9 = x_1181;
goto block_16;
}
}
else
{
lean_object* x_1182; lean_object* x_1183; 
lean_dec(x_1065);
lean_dec(x_1063);
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1182 = lean_ctor_get(x_1066, 0);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_1066, 1);
lean_inc(x_1183);
lean_dec(x_1066);
x_8 = x_1182;
x_9 = x_1183;
goto block_16;
}
}
else
{
lean_object* x_1184; lean_object* x_1185; 
lean_dec(x_1061);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1184 = lean_ctor_get(x_1062, 0);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_1062, 1);
lean_inc(x_1185);
lean_dec(x_1062);
x_8 = x_1184;
x_9 = x_1185;
goto block_16;
}
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
lean_dec(x_1059);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1186 = lean_ctor_get(x_1058, 1);
lean_inc(x_1186);
if (lean_is_exclusive(x_1058)) {
 lean_ctor_release(x_1058, 0);
 lean_ctor_release(x_1058, 1);
 x_1187 = x_1058;
} else {
 lean_dec_ref(x_1058);
 x_1187 = lean_box(0);
}
if (lean_is_scalar(x_1187)) {
 x_1188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1188 = x_1187;
}
lean_ctor_set(x_1188, 0, x_1057);
lean_ctor_set(x_1188, 1, x_1186);
return x_1188;
}
}
else
{
lean_object* x_1189; lean_object* x_1190; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1189 = lean_ctor_get(x_1058, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1058, 1);
lean_inc(x_1190);
lean_dec(x_1058);
x_8 = x_1189;
x_9 = x_1190;
goto block_16;
}
}
else
{
lean_object* x_1191; lean_object* x_1192; 
lean_dec(x_1042);
lean_dec(x_1040);
lean_dec(x_98);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1191 = lean_ctor_get(x_1043, 0);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1043, 1);
lean_inc(x_1192);
lean_dec(x_1043);
x_8 = x_1191;
x_9 = x_1192;
goto block_16;
}
}
else
{
lean_object* x_1193; lean_object* x_1194; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1193 = lean_ctor_get(x_1039, 0);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_1039, 1);
lean_inc(x_1194);
lean_dec(x_1039);
x_8 = x_1193;
x_9 = x_1194;
goto block_16;
}
}
}
else
{
lean_object* x_1195; lean_object* x_1196; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_86);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1195 = lean_ctor_get(x_1031, 0);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1031, 1);
lean_inc(x_1196);
lean_dec(x_1031);
x_8 = x_1195;
x_9 = x_1196;
goto block_16;
}
}
}
else
{
lean_object* x_1197; lean_object* x_1198; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_86);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1197 = lean_ctor_get(x_100, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_100, 1);
lean_inc(x_1198);
lean_dec(x_100);
x_8 = x_1197;
x_9 = x_1198;
goto block_16;
}
}
else
{
lean_object* x_1199; lean_object* x_1200; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_86);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1199 = lean_ctor_get(x_97, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_97, 1);
lean_inc(x_1200);
lean_dec(x_97);
x_8 = x_1199;
x_9 = x_1200;
goto block_16;
}
}
else
{
uint8_t x_1201; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1201 = !lean_is_exclusive(x_90);
if (x_1201 == 0)
{
lean_object* x_1202; lean_object* x_1203; 
x_1202 = lean_ctor_get(x_90, 0);
lean_dec(x_1202);
x_1203 = lean_box(0);
lean_ctor_set(x_90, 0, x_1203);
return x_90;
}
else
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1204 = lean_ctor_get(x_90, 1);
lean_inc(x_1204);
lean_dec(x_90);
x_1205 = lean_box(0);
x_1206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1206, 0, x_1205);
lean_ctor_set(x_1206, 1, x_1204);
return x_1206;
}
}
}
else
{
uint8_t x_1207; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1207 = !lean_is_exclusive(x_90);
if (x_1207 == 0)
{
lean_object* x_1208; lean_object* x_1209; 
x_1208 = lean_ctor_get(x_90, 0);
lean_dec(x_1208);
x_1209 = lean_box(0);
lean_ctor_set(x_90, 0, x_1209);
return x_90;
}
else
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1210 = lean_ctor_get(x_90, 1);
lean_inc(x_1210);
lean_dec(x_90);
x_1211 = lean_box(0);
x_1212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1212, 0, x_1211);
lean_ctor_set(x_1212, 1, x_1210);
return x_1212;
}
}
}
else
{
uint8_t x_1213; 
lean_dec(x_91);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1213 = !lean_is_exclusive(x_90);
if (x_1213 == 0)
{
lean_object* x_1214; lean_object* x_1215; 
x_1214 = lean_ctor_get(x_90, 0);
lean_dec(x_1214);
x_1215 = lean_box(0);
lean_ctor_set(x_90, 0, x_1215);
return x_90;
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
x_1216 = lean_ctor_get(x_90, 1);
lean_inc(x_1216);
lean_dec(x_90);
x_1217 = lean_box(0);
x_1218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1218, 0, x_1217);
lean_ctor_set(x_1218, 1, x_1216);
return x_1218;
}
}
}
else
{
uint8_t x_1219; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1219 = !lean_is_exclusive(x_90);
if (x_1219 == 0)
{
lean_object* x_1220; uint8_t x_1221; 
x_1220 = lean_ctor_get(x_90, 0);
x_1221 = l_Lean_Exception_isInterrupt(x_1220);
if (x_1221 == 0)
{
uint8_t x_1222; 
x_1222 = l_Lean_Exception_isRuntime(x_1220);
if (x_1222 == 0)
{
lean_object* x_1223; 
lean_dec(x_1220);
x_1223 = lean_box(0);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 0, x_1223);
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
lean_object* x_1224; lean_object* x_1225; uint8_t x_1226; 
x_1224 = lean_ctor_get(x_90, 0);
x_1225 = lean_ctor_get(x_90, 1);
lean_inc(x_1225);
lean_inc(x_1224);
lean_dec(x_90);
x_1226 = l_Lean_Exception_isInterrupt(x_1224);
if (x_1226 == 0)
{
uint8_t x_1227; 
x_1227 = l_Lean_Exception_isRuntime(x_1224);
if (x_1227 == 0)
{
lean_object* x_1228; lean_object* x_1229; 
lean_dec(x_1224);
x_1228 = lean_box(0);
x_1229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1229, 0, x_1228);
lean_ctor_set(x_1229, 1, x_1225);
return x_1229;
}
else
{
lean_object* x_1230; 
x_1230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1230, 0, x_1224);
lean_ctor_set(x_1230, 1, x_1225);
return x_1230;
}
}
else
{
lean_object* x_1231; 
x_1231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1231, 0, x_1224);
lean_ctor_set(x_1231, 1, x_1225);
return x_1231;
}
}
}
}
else
{
uint8_t x_1232; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1232 = !lean_is_exclusive(x_87);
if (x_1232 == 0)
{
lean_object* x_1233; uint8_t x_1234; 
x_1233 = lean_ctor_get(x_87, 0);
x_1234 = l_Lean_Exception_isInterrupt(x_1233);
if (x_1234 == 0)
{
uint8_t x_1235; 
x_1235 = l_Lean_Exception_isRuntime(x_1233);
if (x_1235 == 0)
{
lean_object* x_1236; 
lean_dec(x_1233);
x_1236 = lean_box(0);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_1236);
return x_87;
}
else
{
return x_87;
}
}
else
{
return x_87;
}
}
else
{
lean_object* x_1237; lean_object* x_1238; uint8_t x_1239; 
x_1237 = lean_ctor_get(x_87, 0);
x_1238 = lean_ctor_get(x_87, 1);
lean_inc(x_1238);
lean_inc(x_1237);
lean_dec(x_87);
x_1239 = l_Lean_Exception_isInterrupt(x_1237);
if (x_1239 == 0)
{
uint8_t x_1240; 
x_1240 = l_Lean_Exception_isRuntime(x_1237);
if (x_1240 == 0)
{
lean_object* x_1241; lean_object* x_1242; 
lean_dec(x_1237);
x_1241 = lean_box(0);
x_1242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1242, 0, x_1241);
lean_ctor_set(x_1242, 1, x_1238);
return x_1242;
}
else
{
lean_object* x_1243; 
x_1243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1243, 0, x_1237);
lean_ctor_set(x_1243, 1, x_1238);
return x_1243;
}
}
else
{
lean_object* x_1244; 
x_1244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1244, 0, x_1237);
lean_ctor_set(x_1244, 1, x_1238);
return x_1244;
}
}
}
}
else
{
uint8_t x_1245; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1245 = !lean_is_exclusive(x_80);
if (x_1245 == 0)
{
lean_object* x_1246; lean_object* x_1247; 
x_1246 = lean_ctor_get(x_80, 0);
lean_dec(x_1246);
x_1247 = lean_box(0);
lean_ctor_set(x_80, 0, x_1247);
return x_80;
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
x_1248 = lean_ctor_get(x_80, 1);
lean_inc(x_1248);
lean_dec(x_80);
x_1249 = lean_box(0);
x_1250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1250, 0, x_1249);
lean_ctor_set(x_1250, 1, x_1248);
return x_1250;
}
}
}
else
{
uint8_t x_1251; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1251 = !lean_is_exclusive(x_80);
if (x_1251 == 0)
{
lean_object* x_1252; lean_object* x_1253; 
x_1252 = lean_ctor_get(x_80, 0);
lean_dec(x_1252);
x_1253 = lean_box(0);
lean_ctor_set(x_80, 0, x_1253);
return x_80;
}
else
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1254 = lean_ctor_get(x_80, 1);
lean_inc(x_1254);
lean_dec(x_80);
x_1255 = lean_box(0);
x_1256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1256, 0, x_1255);
lean_ctor_set(x_1256, 1, x_1254);
return x_1256;
}
}
}
else
{
uint8_t x_1257; 
lean_dec(x_81);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1257 = !lean_is_exclusive(x_80);
if (x_1257 == 0)
{
lean_object* x_1258; lean_object* x_1259; 
x_1258 = lean_ctor_get(x_80, 0);
lean_dec(x_1258);
x_1259 = lean_box(0);
lean_ctor_set(x_80, 0, x_1259);
return x_80;
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1260 = lean_ctor_get(x_80, 1);
lean_inc(x_1260);
lean_dec(x_80);
x_1261 = lean_box(0);
x_1262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1262, 0, x_1261);
lean_ctor_set(x_1262, 1, x_1260);
return x_1262;
}
}
}
else
{
uint8_t x_1263; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1263 = !lean_is_exclusive(x_80);
if (x_1263 == 0)
{
lean_object* x_1264; uint8_t x_1265; 
x_1264 = lean_ctor_get(x_80, 0);
x_1265 = l_Lean_Exception_isInterrupt(x_1264);
if (x_1265 == 0)
{
uint8_t x_1266; 
x_1266 = l_Lean_Exception_isRuntime(x_1264);
if (x_1266 == 0)
{
lean_object* x_1267; 
lean_dec(x_1264);
x_1267 = lean_box(0);
lean_ctor_set_tag(x_80, 0);
lean_ctor_set(x_80, 0, x_1267);
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
lean_object* x_1268; lean_object* x_1269; uint8_t x_1270; 
x_1268 = lean_ctor_get(x_80, 0);
x_1269 = lean_ctor_get(x_80, 1);
lean_inc(x_1269);
lean_inc(x_1268);
lean_dec(x_80);
x_1270 = l_Lean_Exception_isInterrupt(x_1268);
if (x_1270 == 0)
{
uint8_t x_1271; 
x_1271 = l_Lean_Exception_isRuntime(x_1268);
if (x_1271 == 0)
{
lean_object* x_1272; lean_object* x_1273; 
lean_dec(x_1268);
x_1272 = lean_box(0);
x_1273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1273, 0, x_1272);
lean_ctor_set(x_1273, 1, x_1269);
return x_1273;
}
else
{
lean_object* x_1274; 
x_1274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1274, 0, x_1268);
lean_ctor_set(x_1274, 1, x_1269);
return x_1274;
}
}
else
{
lean_object* x_1275; 
x_1275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1275, 0, x_1268);
lean_ctor_set(x_1275, 1, x_1269);
return x_1275;
}
}
}
}
else
{
uint8_t x_1276; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1276 = !lean_is_exclusive(x_77);
if (x_1276 == 0)
{
lean_object* x_1277; uint8_t x_1278; 
x_1277 = lean_ctor_get(x_77, 0);
x_1278 = l_Lean_Exception_isInterrupt(x_1277);
if (x_1278 == 0)
{
uint8_t x_1279; 
x_1279 = l_Lean_Exception_isRuntime(x_1277);
if (x_1279 == 0)
{
lean_object* x_1280; 
lean_dec(x_1277);
x_1280 = lean_box(0);
lean_ctor_set_tag(x_77, 0);
lean_ctor_set(x_77, 0, x_1280);
return x_77;
}
else
{
return x_77;
}
}
else
{
return x_77;
}
}
else
{
lean_object* x_1281; lean_object* x_1282; uint8_t x_1283; 
x_1281 = lean_ctor_get(x_77, 0);
x_1282 = lean_ctor_get(x_77, 1);
lean_inc(x_1282);
lean_inc(x_1281);
lean_dec(x_77);
x_1283 = l_Lean_Exception_isInterrupt(x_1281);
if (x_1283 == 0)
{
uint8_t x_1284; 
x_1284 = l_Lean_Exception_isRuntime(x_1281);
if (x_1284 == 0)
{
lean_object* x_1285; lean_object* x_1286; 
lean_dec(x_1281);
x_1285 = lean_box(0);
x_1286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1286, 0, x_1285);
lean_ctor_set(x_1286, 1, x_1282);
return x_1286;
}
else
{
lean_object* x_1287; 
x_1287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1287, 0, x_1281);
lean_ctor_set(x_1287, 1, x_1282);
return x_1287;
}
}
else
{
lean_object* x_1288; 
x_1288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1288, 0, x_1281);
lean_ctor_set(x_1288, 1, x_1282);
return x_1288;
}
}
}
}
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; uint8_t x_1292; 
x_1289 = lean_ctor_get(x_67, 1);
lean_inc(x_1289);
lean_dec(x_67);
x_1290 = lean_ctor_get(x_5, 2);
lean_inc(x_1290);
x_1291 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1292 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1290, x_1291);
lean_dec(x_1290);
if (x_1292 == 0)
{
lean_object* x_1293; lean_object* x_1294; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1293 = lean_box(0);
x_1294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1294, 0, x_1293);
lean_ctor_set(x_1294, 1, x_1289);
return x_1294;
}
else
{
lean_object* x_1295; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_65);
x_1295 = lean_infer_type(x_65, x_3, x_4, x_5, x_6, x_1289);
if (lean_obj_tag(x_1295) == 0)
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1295, 1);
lean_inc(x_1297);
lean_dec(x_1295);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1298 = lean_whnf(x_1296, x_3, x_4, x_5, x_6, x_1297);
if (lean_obj_tag(x_1298) == 0)
{
lean_object* x_1299; 
x_1299 = lean_ctor_get(x_1298, 0);
lean_inc(x_1299);
if (lean_obj_tag(x_1299) == 7)
{
lean_object* x_1300; 
x_1300 = lean_ctor_get(x_1299, 1);
lean_inc(x_1300);
if (lean_obj_tag(x_1300) == 3)
{
lean_object* x_1301; 
x_1301 = lean_ctor_get(x_1299, 2);
lean_inc(x_1301);
lean_dec(x_1299);
if (lean_obj_tag(x_1301) == 3)
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
x_1302 = lean_ctor_get(x_1298, 1);
lean_inc(x_1302);
lean_dec(x_1298);
x_1303 = lean_ctor_get(x_1300, 0);
lean_inc(x_1303);
lean_dec(x_1300);
x_1304 = lean_ctor_get(x_1301, 0);
lean_inc(x_1304);
lean_dec(x_1301);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_1305 = lean_infer_type(x_51, x_3, x_4, x_5, x_6, x_1302);
if (lean_obj_tag(x_1305) == 0)
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; 
x_1306 = lean_ctor_get(x_1305, 0);
lean_inc(x_1306);
x_1307 = lean_ctor_get(x_1305, 1);
lean_inc(x_1307);
lean_dec(x_1305);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1308 = lean_whnf(x_1306, x_3, x_4, x_5, x_6, x_1307);
if (lean_obj_tag(x_1308) == 0)
{
lean_object* x_1309; 
x_1309 = lean_ctor_get(x_1308, 0);
lean_inc(x_1309);
if (lean_obj_tag(x_1309) == 7)
{
lean_object* x_1310; 
x_1310 = lean_ctor_get(x_1309, 1);
lean_inc(x_1310);
if (lean_obj_tag(x_1310) == 3)
{
lean_object* x_1311; 
x_1311 = lean_ctor_get(x_1309, 2);
lean_inc(x_1311);
lean_dec(x_1309);
if (lean_obj_tag(x_1311) == 3)
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1312 = lean_ctor_get(x_1308, 1);
lean_inc(x_1312);
lean_dec(x_1308);
x_1313 = lean_ctor_get(x_1310, 0);
lean_inc(x_1313);
lean_dec(x_1310);
x_1314 = lean_ctor_get(x_1311, 0);
lean_inc(x_1314);
lean_dec(x_1311);
x_1315 = l_Lean_Meta_decLevel(x_1303, x_3, x_4, x_5, x_6, x_1312);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1315, 1);
lean_inc(x_1317);
lean_dec(x_1315);
x_1318 = l_Lean_Meta_decLevel(x_1313, x_3, x_4, x_5, x_6, x_1317);
if (lean_obj_tag(x_1318) == 0)
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; uint8_t x_1322; lean_object* x_1323; 
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
x_1322 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1316);
x_1323 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1316, x_1319, x_1322, x_3, x_4, x_5, x_6, x_1320);
if (lean_obj_tag(x_1323) == 0)
{
lean_object* x_1324; uint8_t x_1325; 
x_1324 = lean_ctor_get(x_1323, 0);
lean_inc(x_1324);
x_1325 = lean_unbox(x_1324);
lean_dec(x_1324);
if (x_1325 == 0)
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
lean_dec(x_1321);
lean_dec(x_1316);
lean_dec(x_1314);
lean_dec(x_1304);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1326 = lean_ctor_get(x_1323, 1);
lean_inc(x_1326);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 lean_ctor_release(x_1323, 1);
 x_1327 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1327 = lean_box(0);
}
x_1328 = lean_box(0);
if (lean_is_scalar(x_1327)) {
 x_1329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1329 = x_1327;
}
lean_ctor_set(x_1329, 0, x_1328);
lean_ctor_set(x_1329, 1, x_1326);
return x_1329;
}
else
{
lean_object* x_1330; lean_object* x_1331; 
x_1330 = lean_ctor_get(x_1323, 1);
lean_inc(x_1330);
lean_dec(x_1323);
x_1331 = l_Lean_Meta_decLevel(x_1304, x_3, x_4, x_5, x_6, x_1330);
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
if (lean_is_exclusive(x_1331)) {
 lean_ctor_release(x_1331, 0);
 lean_ctor_release(x_1331, 1);
 x_1334 = x_1331;
} else {
 lean_dec_ref(x_1331);
 x_1334 = lean_box(0);
}
x_1335 = l_Lean_Meta_decLevel(x_1314, x_3, x_4, x_5, x_6, x_1333);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1336 = lean_ctor_get(x_1335, 0);
lean_inc(x_1336);
x_1337 = lean_ctor_get(x_1335, 1);
lean_inc(x_1337);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 x_1338 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1338 = lean_box(0);
}
x_1339 = lean_box(0);
if (lean_is_scalar(x_1338)) {
 x_1340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1340 = x_1338;
 lean_ctor_set_tag(x_1340, 1);
}
lean_ctor_set(x_1340, 0, x_1336);
lean_ctor_set(x_1340, 1, x_1339);
if (lean_is_scalar(x_1334)) {
 x_1341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1341 = x_1334;
 lean_ctor_set_tag(x_1341, 1);
}
lean_ctor_set(x_1341, 0, x_1332);
lean_ctor_set(x_1341, 1, x_1340);
if (lean_is_scalar(x_1321)) {
 x_1342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1342 = x_1321;
 lean_ctor_set_tag(x_1342, 1);
}
lean_ctor_set(x_1342, 0, x_1316);
lean_ctor_set(x_1342, 1, x_1341);
x_1343 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1344 = l_Lean_Expr_const___override(x_1343, x_1342);
x_1345 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_65);
x_1346 = lean_array_push(x_1345, x_65);
lean_inc(x_51);
x_1347 = lean_array_push(x_1346, x_51);
x_1348 = l_Lean_mkAppN(x_1344, x_1347);
lean_dec(x_1347);
x_1349 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1350 = l_Lean_Meta_trySynthInstance(x_1348, x_1349, x_3, x_4, x_5, x_6, x_1337);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; 
x_1351 = lean_ctor_get(x_1350, 0);
lean_inc(x_1351);
if (lean_obj_tag(x_1351) == 1)
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
x_1352 = lean_ctor_get(x_1350, 1);
lean_inc(x_1352);
lean_dec(x_1350);
x_1353 = lean_ctor_get(x_1351, 0);
lean_inc(x_1353);
lean_dec(x_1351);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_1354 = l_Lean_Meta_getDecLevel(x_66, x_3, x_4, x_5, x_6, x_1352);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1354, 1);
lean_inc(x_1356);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 lean_ctor_release(x_1354, 1);
 x_1357 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1357 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1358 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_1356);
if (lean_obj_tag(x_1358) == 0)
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
x_1359 = lean_ctor_get(x_1358, 0);
lean_inc(x_1359);
x_1360 = lean_ctor_get(x_1358, 1);
lean_inc(x_1360);
if (lean_is_exclusive(x_1358)) {
 lean_ctor_release(x_1358, 0);
 lean_ctor_release(x_1358, 1);
 x_1361 = x_1358;
} else {
 lean_dec_ref(x_1358);
 x_1361 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_1362 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_1360);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1363 = lean_ctor_get(x_1362, 0);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1362, 1);
lean_inc(x_1364);
if (lean_is_exclusive(x_1362)) {
 lean_ctor_release(x_1362, 0);
 lean_ctor_release(x_1362, 1);
 x_1365 = x_1362;
} else {
 lean_dec_ref(x_1362);
 x_1365 = lean_box(0);
}
if (lean_is_scalar(x_1365)) {
 x_1366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1366 = x_1365;
 lean_ctor_set_tag(x_1366, 1);
}
lean_ctor_set(x_1366, 0, x_1363);
lean_ctor_set(x_1366, 1, x_1339);
if (lean_is_scalar(x_1361)) {
 x_1367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1367 = x_1361;
 lean_ctor_set_tag(x_1367, 1);
}
lean_ctor_set(x_1367, 0, x_1359);
lean_ctor_set(x_1367, 1, x_1366);
if (lean_is_scalar(x_1357)) {
 x_1368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1368 = x_1357;
 lean_ctor_set_tag(x_1368, 1);
}
lean_ctor_set(x_1368, 0, x_1355);
lean_ctor_set(x_1368, 1, x_1367);
x_1369 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_1368);
x_1370 = l_Lean_Expr_const___override(x_1369, x_1368);
x_1371 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_65);
x_1372 = lean_array_push(x_1371, x_65);
lean_inc(x_51);
x_1373 = lean_array_push(x_1372, x_51);
lean_inc(x_1353);
x_1374 = lean_array_push(x_1373, x_1353);
lean_inc(x_66);
x_1375 = lean_array_push(x_1374, x_66);
lean_inc(x_1);
x_1376 = lean_array_push(x_1375, x_1);
x_1377 = l_Lean_mkAppN(x_1370, x_1376);
lean_dec(x_1376);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1377);
x_1378 = lean_infer_type(x_1377, x_3, x_4, x_5, x_6, x_1364);
if (lean_obj_tag(x_1378) == 0)
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1379 = lean_ctor_get(x_1378, 0);
lean_inc(x_1379);
x_1380 = lean_ctor_get(x_1378, 1);
lean_inc(x_1380);
lean_dec(x_1378);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_1381 = l_Lean_Meta_isExprDefEq(x_32, x_1379, x_3, x_4, x_5, x_6, x_1380);
if (lean_obj_tag(x_1381) == 0)
{
lean_object* x_1382; uint8_t x_1383; 
x_1382 = lean_ctor_get(x_1381, 0);
lean_inc(x_1382);
x_1383 = lean_unbox(x_1382);
lean_dec(x_1382);
if (x_1383 == 0)
{
lean_object* x_1384; lean_object* x_1385; 
lean_dec(x_1377);
lean_free_object(x_54);
x_1384 = lean_ctor_get(x_1381, 1);
lean_inc(x_1384);
lean_dec(x_1381);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_1385 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_1384);
if (lean_obj_tag(x_1385) == 0)
{
lean_object* x_1386; 
x_1386 = lean_ctor_get(x_1385, 0);
lean_inc(x_1386);
if (lean_obj_tag(x_1386) == 0)
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1387 = lean_ctor_get(x_1385, 1);
lean_inc(x_1387);
if (lean_is_exclusive(x_1385)) {
 lean_ctor_release(x_1385, 0);
 lean_ctor_release(x_1385, 1);
 x_1388 = x_1385;
} else {
 lean_dec_ref(x_1385);
 x_1388 = lean_box(0);
}
if (lean_is_scalar(x_1388)) {
 x_1389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1389 = x_1388;
}
lean_ctor_set(x_1389, 0, x_1349);
lean_ctor_set(x_1389, 1, x_1387);
return x_1389;
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
x_1390 = lean_ctor_get(x_1385, 1);
lean_inc(x_1390);
lean_dec(x_1385);
x_1391 = lean_ctor_get(x_1386, 0);
lean_inc(x_1391);
lean_dec(x_1386);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_66);
x_1392 = l_Lean_Meta_getLevel(x_66, x_3, x_4, x_5, x_6, x_1390);
if (lean_obj_tag(x_1392) == 0)
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
x_1393 = lean_ctor_get(x_1392, 0);
lean_inc(x_1393);
x_1394 = lean_ctor_get(x_1392, 1);
lean_inc(x_1394);
if (lean_is_exclusive(x_1392)) {
 lean_ctor_release(x_1392, 0);
 lean_ctor_release(x_1392, 1);
 x_1395 = x_1392;
} else {
 lean_dec_ref(x_1392);
 x_1395 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_1396 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_1394);
if (lean_obj_tag(x_1396) == 0)
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; uint8_t x_1411; lean_object* x_1412; lean_object* x_1413; 
x_1397 = lean_ctor_get(x_1396, 0);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1396, 1);
lean_inc(x_1398);
if (lean_is_exclusive(x_1396)) {
 lean_ctor_release(x_1396, 0);
 lean_ctor_release(x_1396, 1);
 x_1399 = x_1396;
} else {
 lean_dec_ref(x_1396);
 x_1399 = lean_box(0);
}
if (lean_is_scalar(x_1399)) {
 x_1400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1400 = x_1399;
 lean_ctor_set_tag(x_1400, 1);
}
lean_ctor_set(x_1400, 0, x_1397);
lean_ctor_set(x_1400, 1, x_1339);
if (lean_is_scalar(x_1395)) {
 x_1401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1401 = x_1395;
 lean_ctor_set_tag(x_1401, 1);
}
lean_ctor_set(x_1401, 0, x_1393);
lean_ctor_set(x_1401, 1, x_1400);
x_1402 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1403 = l_Lean_Expr_const___override(x_1402, x_1401);
x_1404 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_66);
x_1405 = lean_array_push(x_1404, x_66);
x_1406 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_1407 = lean_array_push(x_1405, x_1406);
lean_inc(x_52);
x_1408 = lean_array_push(x_1407, x_52);
x_1409 = l_Lean_mkAppN(x_1403, x_1408);
lean_dec(x_1408);
x_1410 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_1411 = 0;
lean_inc(x_66);
x_1412 = l_Lean_Expr_forallE___override(x_1410, x_66, x_1409, x_1411);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1413 = l_Lean_Meta_trySynthInstance(x_1412, x_1349, x_3, x_4, x_5, x_6, x_1398);
if (lean_obj_tag(x_1413) == 0)
{
lean_object* x_1414; 
x_1414 = lean_ctor_get(x_1413, 0);
lean_inc(x_1414);
if (lean_obj_tag(x_1414) == 1)
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; 
x_1415 = lean_ctor_get(x_1413, 1);
lean_inc(x_1415);
lean_dec(x_1413);
x_1416 = lean_ctor_get(x_1414, 0);
lean_inc(x_1416);
lean_dec(x_1414);
x_1417 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_1418 = l_Lean_Expr_const___override(x_1417, x_1368);
x_1419 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_1420 = lean_array_push(x_1419, x_65);
x_1421 = lean_array_push(x_1420, x_51);
x_1422 = lean_array_push(x_1421, x_66);
x_1423 = lean_array_push(x_1422, x_52);
x_1424 = lean_array_push(x_1423, x_1353);
x_1425 = lean_array_push(x_1424, x_1416);
x_1426 = lean_array_push(x_1425, x_1391);
x_1427 = lean_array_push(x_1426, x_1);
x_1428 = l_Lean_mkAppN(x_1418, x_1427);
lean_dec(x_1427);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1429 = l_Lean_Meta_expandCoe(x_1428, x_3, x_4, x_5, x_6, x_1415);
if (lean_obj_tag(x_1429) == 0)
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
x_1430 = lean_ctor_get(x_1429, 0);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_1429, 1);
lean_inc(x_1431);
lean_dec(x_1429);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1430);
x_1432 = lean_infer_type(x_1430, x_3, x_4, x_5, x_6, x_1431);
if (lean_obj_tag(x_1432) == 0)
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1433 = lean_ctor_get(x_1432, 0);
lean_inc(x_1433);
x_1434 = lean_ctor_get(x_1432, 1);
lean_inc(x_1434);
lean_dec(x_1432);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1435 = l_Lean_Meta_isExprDefEq(x_32, x_1433, x_3, x_4, x_5, x_6, x_1434);
if (lean_obj_tag(x_1435) == 0)
{
lean_object* x_1436; uint8_t x_1437; 
x_1436 = lean_ctor_get(x_1435, 0);
lean_inc(x_1436);
x_1437 = lean_unbox(x_1436);
lean_dec(x_1436);
if (x_1437 == 0)
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
lean_dec(x_1430);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1438 = lean_ctor_get(x_1435, 1);
lean_inc(x_1438);
if (lean_is_exclusive(x_1435)) {
 lean_ctor_release(x_1435, 0);
 lean_ctor_release(x_1435, 1);
 x_1439 = x_1435;
} else {
 lean_dec_ref(x_1435);
 x_1439 = lean_box(0);
}
if (lean_is_scalar(x_1439)) {
 x_1440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1440 = x_1439;
}
lean_ctor_set(x_1440, 0, x_1349);
lean_ctor_set(x_1440, 1, x_1438);
return x_1440;
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
x_1441 = lean_ctor_get(x_1435, 1);
lean_inc(x_1441);
lean_dec(x_1435);
x_1442 = lean_box(0);
x_1443 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1430, x_1442, x_3, x_4, x_5, x_6, x_1441);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1444 = lean_ctor_get(x_1443, 0);
lean_inc(x_1444);
x_1445 = lean_ctor_get(x_1443, 1);
lean_inc(x_1445);
if (lean_is_exclusive(x_1443)) {
 lean_ctor_release(x_1443, 0);
 lean_ctor_release(x_1443, 1);
 x_1446 = x_1443;
} else {
 lean_dec_ref(x_1443);
 x_1446 = lean_box(0);
}
if (lean_is_scalar(x_1446)) {
 x_1447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1447 = x_1446;
}
lean_ctor_set(x_1447, 0, x_1444);
lean_ctor_set(x_1447, 1, x_1445);
return x_1447;
}
}
else
{
lean_object* x_1448; lean_object* x_1449; 
lean_dec(x_1430);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1448 = lean_ctor_get(x_1435, 0);
lean_inc(x_1448);
x_1449 = lean_ctor_get(x_1435, 1);
lean_inc(x_1449);
lean_dec(x_1435);
x_8 = x_1448;
x_9 = x_1449;
goto block_16;
}
}
else
{
lean_object* x_1450; lean_object* x_1451; 
lean_dec(x_1430);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1450 = lean_ctor_get(x_1432, 0);
lean_inc(x_1450);
x_1451 = lean_ctor_get(x_1432, 1);
lean_inc(x_1451);
lean_dec(x_1432);
x_8 = x_1450;
x_9 = x_1451;
goto block_16;
}
}
else
{
lean_object* x_1452; lean_object* x_1453; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1452 = lean_ctor_get(x_1429, 0);
lean_inc(x_1452);
x_1453 = lean_ctor_get(x_1429, 1);
lean_inc(x_1453);
lean_dec(x_1429);
x_8 = x_1452;
x_9 = x_1453;
goto block_16;
}
}
else
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; 
lean_dec(x_1414);
lean_dec(x_1391);
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1454 = lean_ctor_get(x_1413, 1);
lean_inc(x_1454);
if (lean_is_exclusive(x_1413)) {
 lean_ctor_release(x_1413, 0);
 lean_ctor_release(x_1413, 1);
 x_1455 = x_1413;
} else {
 lean_dec_ref(x_1413);
 x_1455 = lean_box(0);
}
if (lean_is_scalar(x_1455)) {
 x_1456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1456 = x_1455;
}
lean_ctor_set(x_1456, 0, x_1349);
lean_ctor_set(x_1456, 1, x_1454);
return x_1456;
}
}
else
{
lean_object* x_1457; lean_object* x_1458; 
lean_dec(x_1391);
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1457 = lean_ctor_get(x_1413, 0);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1413, 1);
lean_inc(x_1458);
lean_dec(x_1413);
x_8 = x_1457;
x_9 = x_1458;
goto block_16;
}
}
else
{
lean_object* x_1459; lean_object* x_1460; 
lean_dec(x_1395);
lean_dec(x_1393);
lean_dec(x_1391);
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1459 = lean_ctor_get(x_1396, 0);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1396, 1);
lean_inc(x_1460);
lean_dec(x_1396);
x_8 = x_1459;
x_9 = x_1460;
goto block_16;
}
}
else
{
lean_object* x_1461; lean_object* x_1462; 
lean_dec(x_1391);
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1461 = lean_ctor_get(x_1392, 0);
lean_inc(x_1461);
x_1462 = lean_ctor_get(x_1392, 1);
lean_inc(x_1462);
lean_dec(x_1392);
x_8 = x_1461;
x_9 = x_1462;
goto block_16;
}
}
}
else
{
lean_object* x_1463; lean_object* x_1464; 
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1463 = lean_ctor_get(x_1385, 0);
lean_inc(x_1463);
x_1464 = lean_ctor_get(x_1385, 1);
lean_inc(x_1464);
lean_dec(x_1385);
x_8 = x_1463;
x_9 = x_1464;
goto block_16;
}
}
else
{
lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1465 = lean_ctor_get(x_1381, 1);
lean_inc(x_1465);
if (lean_is_exclusive(x_1381)) {
 lean_ctor_release(x_1381, 0);
 lean_ctor_release(x_1381, 1);
 x_1466 = x_1381;
} else {
 lean_dec_ref(x_1381);
 x_1466 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_1377);
if (lean_is_scalar(x_1466)) {
 x_1467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1467 = x_1466;
}
lean_ctor_set(x_1467, 0, x_54);
lean_ctor_set(x_1467, 1, x_1465);
return x_1467;
}
}
else
{
lean_object* x_1468; lean_object* x_1469; 
lean_dec(x_1377);
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1468 = lean_ctor_get(x_1381, 0);
lean_inc(x_1468);
x_1469 = lean_ctor_get(x_1381, 1);
lean_inc(x_1469);
lean_dec(x_1381);
x_8 = x_1468;
x_9 = x_1469;
goto block_16;
}
}
else
{
lean_object* x_1470; lean_object* x_1471; 
lean_dec(x_1377);
lean_dec(x_1368);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1470 = lean_ctor_get(x_1378, 0);
lean_inc(x_1470);
x_1471 = lean_ctor_get(x_1378, 1);
lean_inc(x_1471);
lean_dec(x_1378);
x_8 = x_1470;
x_9 = x_1471;
goto block_16;
}
}
else
{
lean_object* x_1472; lean_object* x_1473; 
lean_dec(x_1361);
lean_dec(x_1359);
lean_dec(x_1357);
lean_dec(x_1355);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1472 = lean_ctor_get(x_1362, 0);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1362, 1);
lean_inc(x_1473);
lean_dec(x_1362);
x_8 = x_1472;
x_9 = x_1473;
goto block_16;
}
}
else
{
lean_object* x_1474; lean_object* x_1475; 
lean_dec(x_1357);
lean_dec(x_1355);
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1474 = lean_ctor_get(x_1358, 0);
lean_inc(x_1474);
x_1475 = lean_ctor_get(x_1358, 1);
lean_inc(x_1475);
lean_dec(x_1358);
x_8 = x_1474;
x_9 = x_1475;
goto block_16;
}
}
else
{
lean_object* x_1476; lean_object* x_1477; 
lean_dec(x_1353);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1476 = lean_ctor_get(x_1354, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1354, 1);
lean_inc(x_1477);
lean_dec(x_1354);
x_8 = x_1476;
x_9 = x_1477;
goto block_16;
}
}
else
{
lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; 
lean_dec(x_1351);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1478 = lean_ctor_get(x_1350, 1);
lean_inc(x_1478);
if (lean_is_exclusive(x_1350)) {
 lean_ctor_release(x_1350, 0);
 lean_ctor_release(x_1350, 1);
 x_1479 = x_1350;
} else {
 lean_dec_ref(x_1350);
 x_1479 = lean_box(0);
}
if (lean_is_scalar(x_1479)) {
 x_1480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1480 = x_1479;
}
lean_ctor_set(x_1480, 0, x_1349);
lean_ctor_set(x_1480, 1, x_1478);
return x_1480;
}
}
else
{
lean_object* x_1481; lean_object* x_1482; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1481 = lean_ctor_get(x_1350, 0);
lean_inc(x_1481);
x_1482 = lean_ctor_get(x_1350, 1);
lean_inc(x_1482);
lean_dec(x_1350);
x_8 = x_1481;
x_9 = x_1482;
goto block_16;
}
}
else
{
lean_object* x_1483; lean_object* x_1484; 
lean_dec(x_1334);
lean_dec(x_1332);
lean_dec(x_1321);
lean_dec(x_1316);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1483 = lean_ctor_get(x_1335, 0);
lean_inc(x_1483);
x_1484 = lean_ctor_get(x_1335, 1);
lean_inc(x_1484);
lean_dec(x_1335);
x_8 = x_1483;
x_9 = x_1484;
goto block_16;
}
}
else
{
lean_object* x_1485; lean_object* x_1486; 
lean_dec(x_1321);
lean_dec(x_1316);
lean_dec(x_1314);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1485 = lean_ctor_get(x_1331, 0);
lean_inc(x_1485);
x_1486 = lean_ctor_get(x_1331, 1);
lean_inc(x_1486);
lean_dec(x_1331);
x_8 = x_1485;
x_9 = x_1486;
goto block_16;
}
}
}
else
{
lean_object* x_1487; lean_object* x_1488; 
lean_dec(x_1321);
lean_dec(x_1316);
lean_dec(x_1314);
lean_dec(x_1304);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1487 = lean_ctor_get(x_1323, 0);
lean_inc(x_1487);
x_1488 = lean_ctor_get(x_1323, 1);
lean_inc(x_1488);
lean_dec(x_1323);
x_8 = x_1487;
x_9 = x_1488;
goto block_16;
}
}
else
{
lean_object* x_1489; lean_object* x_1490; 
lean_dec(x_1316);
lean_dec(x_1314);
lean_dec(x_1304);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1489 = lean_ctor_get(x_1318, 0);
lean_inc(x_1489);
x_1490 = lean_ctor_get(x_1318, 1);
lean_inc(x_1490);
lean_dec(x_1318);
x_8 = x_1489;
x_9 = x_1490;
goto block_16;
}
}
else
{
lean_object* x_1491; lean_object* x_1492; 
lean_dec(x_1314);
lean_dec(x_1313);
lean_dec(x_1304);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1491 = lean_ctor_get(x_1315, 0);
lean_inc(x_1491);
x_1492 = lean_ctor_get(x_1315, 1);
lean_inc(x_1492);
lean_dec(x_1315);
x_8 = x_1491;
x_9 = x_1492;
goto block_16;
}
}
else
{
lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; 
lean_dec(x_1311);
lean_dec(x_1310);
lean_dec(x_1304);
lean_dec(x_1303);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1493 = lean_ctor_get(x_1308, 1);
lean_inc(x_1493);
if (lean_is_exclusive(x_1308)) {
 lean_ctor_release(x_1308, 0);
 lean_ctor_release(x_1308, 1);
 x_1494 = x_1308;
} else {
 lean_dec_ref(x_1308);
 x_1494 = lean_box(0);
}
x_1495 = lean_box(0);
if (lean_is_scalar(x_1494)) {
 x_1496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1496 = x_1494;
}
lean_ctor_set(x_1496, 0, x_1495);
lean_ctor_set(x_1496, 1, x_1493);
return x_1496;
}
}
else
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
lean_dec(x_1310);
lean_dec(x_1309);
lean_dec(x_1304);
lean_dec(x_1303);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1497 = lean_ctor_get(x_1308, 1);
lean_inc(x_1497);
if (lean_is_exclusive(x_1308)) {
 lean_ctor_release(x_1308, 0);
 lean_ctor_release(x_1308, 1);
 x_1498 = x_1308;
} else {
 lean_dec_ref(x_1308);
 x_1498 = lean_box(0);
}
x_1499 = lean_box(0);
if (lean_is_scalar(x_1498)) {
 x_1500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1500 = x_1498;
}
lean_ctor_set(x_1500, 0, x_1499);
lean_ctor_set(x_1500, 1, x_1497);
return x_1500;
}
}
else
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; 
lean_dec(x_1309);
lean_dec(x_1304);
lean_dec(x_1303);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1501 = lean_ctor_get(x_1308, 1);
lean_inc(x_1501);
if (lean_is_exclusive(x_1308)) {
 lean_ctor_release(x_1308, 0);
 lean_ctor_release(x_1308, 1);
 x_1502 = x_1308;
} else {
 lean_dec_ref(x_1308);
 x_1502 = lean_box(0);
}
x_1503 = lean_box(0);
if (lean_is_scalar(x_1502)) {
 x_1504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1504 = x_1502;
}
lean_ctor_set(x_1504, 0, x_1503);
lean_ctor_set(x_1504, 1, x_1501);
return x_1504;
}
}
else
{
lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; uint8_t x_1508; 
lean_dec(x_1304);
lean_dec(x_1303);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1505 = lean_ctor_get(x_1308, 0);
lean_inc(x_1505);
x_1506 = lean_ctor_get(x_1308, 1);
lean_inc(x_1506);
if (lean_is_exclusive(x_1308)) {
 lean_ctor_release(x_1308, 0);
 lean_ctor_release(x_1308, 1);
 x_1507 = x_1308;
} else {
 lean_dec_ref(x_1308);
 x_1507 = lean_box(0);
}
x_1508 = l_Lean_Exception_isInterrupt(x_1505);
if (x_1508 == 0)
{
uint8_t x_1509; 
x_1509 = l_Lean_Exception_isRuntime(x_1505);
if (x_1509 == 0)
{
lean_object* x_1510; lean_object* x_1511; 
lean_dec(x_1505);
x_1510 = lean_box(0);
if (lean_is_scalar(x_1507)) {
 x_1511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1511 = x_1507;
 lean_ctor_set_tag(x_1511, 0);
}
lean_ctor_set(x_1511, 0, x_1510);
lean_ctor_set(x_1511, 1, x_1506);
return x_1511;
}
else
{
lean_object* x_1512; 
if (lean_is_scalar(x_1507)) {
 x_1512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1512 = x_1507;
}
lean_ctor_set(x_1512, 0, x_1505);
lean_ctor_set(x_1512, 1, x_1506);
return x_1512;
}
}
else
{
lean_object* x_1513; 
if (lean_is_scalar(x_1507)) {
 x_1513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1513 = x_1507;
}
lean_ctor_set(x_1513, 0, x_1505);
lean_ctor_set(x_1513, 1, x_1506);
return x_1513;
}
}
}
else
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; uint8_t x_1517; 
lean_dec(x_1304);
lean_dec(x_1303);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1514 = lean_ctor_get(x_1305, 0);
lean_inc(x_1514);
x_1515 = lean_ctor_get(x_1305, 1);
lean_inc(x_1515);
if (lean_is_exclusive(x_1305)) {
 lean_ctor_release(x_1305, 0);
 lean_ctor_release(x_1305, 1);
 x_1516 = x_1305;
} else {
 lean_dec_ref(x_1305);
 x_1516 = lean_box(0);
}
x_1517 = l_Lean_Exception_isInterrupt(x_1514);
if (x_1517 == 0)
{
uint8_t x_1518; 
x_1518 = l_Lean_Exception_isRuntime(x_1514);
if (x_1518 == 0)
{
lean_object* x_1519; lean_object* x_1520; 
lean_dec(x_1514);
x_1519 = lean_box(0);
if (lean_is_scalar(x_1516)) {
 x_1520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1520 = x_1516;
 lean_ctor_set_tag(x_1520, 0);
}
lean_ctor_set(x_1520, 0, x_1519);
lean_ctor_set(x_1520, 1, x_1515);
return x_1520;
}
else
{
lean_object* x_1521; 
if (lean_is_scalar(x_1516)) {
 x_1521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1521 = x_1516;
}
lean_ctor_set(x_1521, 0, x_1514);
lean_ctor_set(x_1521, 1, x_1515);
return x_1521;
}
}
else
{
lean_object* x_1522; 
if (lean_is_scalar(x_1516)) {
 x_1522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1522 = x_1516;
}
lean_ctor_set(x_1522, 0, x_1514);
lean_ctor_set(x_1522, 1, x_1515);
return x_1522;
}
}
}
else
{
lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; 
lean_dec(x_1301);
lean_dec(x_1300);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1523 = lean_ctor_get(x_1298, 1);
lean_inc(x_1523);
if (lean_is_exclusive(x_1298)) {
 lean_ctor_release(x_1298, 0);
 lean_ctor_release(x_1298, 1);
 x_1524 = x_1298;
} else {
 lean_dec_ref(x_1298);
 x_1524 = lean_box(0);
}
x_1525 = lean_box(0);
if (lean_is_scalar(x_1524)) {
 x_1526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1526 = x_1524;
}
lean_ctor_set(x_1526, 0, x_1525);
lean_ctor_set(x_1526, 1, x_1523);
return x_1526;
}
}
else
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; 
lean_dec(x_1300);
lean_dec(x_1299);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1527 = lean_ctor_get(x_1298, 1);
lean_inc(x_1527);
if (lean_is_exclusive(x_1298)) {
 lean_ctor_release(x_1298, 0);
 lean_ctor_release(x_1298, 1);
 x_1528 = x_1298;
} else {
 lean_dec_ref(x_1298);
 x_1528 = lean_box(0);
}
x_1529 = lean_box(0);
if (lean_is_scalar(x_1528)) {
 x_1530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1530 = x_1528;
}
lean_ctor_set(x_1530, 0, x_1529);
lean_ctor_set(x_1530, 1, x_1527);
return x_1530;
}
}
else
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
lean_dec(x_1299);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1531 = lean_ctor_get(x_1298, 1);
lean_inc(x_1531);
if (lean_is_exclusive(x_1298)) {
 lean_ctor_release(x_1298, 0);
 lean_ctor_release(x_1298, 1);
 x_1532 = x_1298;
} else {
 lean_dec_ref(x_1298);
 x_1532 = lean_box(0);
}
x_1533 = lean_box(0);
if (lean_is_scalar(x_1532)) {
 x_1534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1534 = x_1532;
}
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set(x_1534, 1, x_1531);
return x_1534;
}
}
else
{
lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; uint8_t x_1538; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1535 = lean_ctor_get(x_1298, 0);
lean_inc(x_1535);
x_1536 = lean_ctor_get(x_1298, 1);
lean_inc(x_1536);
if (lean_is_exclusive(x_1298)) {
 lean_ctor_release(x_1298, 0);
 lean_ctor_release(x_1298, 1);
 x_1537 = x_1298;
} else {
 lean_dec_ref(x_1298);
 x_1537 = lean_box(0);
}
x_1538 = l_Lean_Exception_isInterrupt(x_1535);
if (x_1538 == 0)
{
uint8_t x_1539; 
x_1539 = l_Lean_Exception_isRuntime(x_1535);
if (x_1539 == 0)
{
lean_object* x_1540; lean_object* x_1541; 
lean_dec(x_1535);
x_1540 = lean_box(0);
if (lean_is_scalar(x_1537)) {
 x_1541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1541 = x_1537;
 lean_ctor_set_tag(x_1541, 0);
}
lean_ctor_set(x_1541, 0, x_1540);
lean_ctor_set(x_1541, 1, x_1536);
return x_1541;
}
else
{
lean_object* x_1542; 
if (lean_is_scalar(x_1537)) {
 x_1542 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1542 = x_1537;
}
lean_ctor_set(x_1542, 0, x_1535);
lean_ctor_set(x_1542, 1, x_1536);
return x_1542;
}
}
else
{
lean_object* x_1543; 
if (lean_is_scalar(x_1537)) {
 x_1543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1543 = x_1537;
}
lean_ctor_set(x_1543, 0, x_1535);
lean_ctor_set(x_1543, 1, x_1536);
return x_1543;
}
}
}
else
{
lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; uint8_t x_1547; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1544 = lean_ctor_get(x_1295, 0);
lean_inc(x_1544);
x_1545 = lean_ctor_get(x_1295, 1);
lean_inc(x_1545);
if (lean_is_exclusive(x_1295)) {
 lean_ctor_release(x_1295, 0);
 lean_ctor_release(x_1295, 1);
 x_1546 = x_1295;
} else {
 lean_dec_ref(x_1295);
 x_1546 = lean_box(0);
}
x_1547 = l_Lean_Exception_isInterrupt(x_1544);
if (x_1547 == 0)
{
uint8_t x_1548; 
x_1548 = l_Lean_Exception_isRuntime(x_1544);
if (x_1548 == 0)
{
lean_object* x_1549; lean_object* x_1550; 
lean_dec(x_1544);
x_1549 = lean_box(0);
if (lean_is_scalar(x_1546)) {
 x_1550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1550 = x_1546;
 lean_ctor_set_tag(x_1550, 0);
}
lean_ctor_set(x_1550, 0, x_1549);
lean_ctor_set(x_1550, 1, x_1545);
return x_1550;
}
else
{
lean_object* x_1551; 
if (lean_is_scalar(x_1546)) {
 x_1551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1551 = x_1546;
}
lean_ctor_set(x_1551, 0, x_1544);
lean_ctor_set(x_1551, 1, x_1545);
return x_1551;
}
}
else
{
lean_object* x_1552; 
if (lean_is_scalar(x_1546)) {
 x_1552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1552 = x_1546;
}
lean_ctor_set(x_1552, 0, x_1544);
lean_ctor_set(x_1552, 1, x_1545);
return x_1552;
}
}
}
}
}
else
{
lean_object* x_1553; lean_object* x_1554; 
lean_dec(x_38);
lean_dec(x_32);
x_1553 = lean_ctor_get(x_67, 1);
lean_inc(x_1553);
lean_dec(x_67);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1554 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_1553);
if (lean_obj_tag(x_1554) == 0)
{
lean_object* x_1555; 
x_1555 = lean_ctor_get(x_1554, 0);
lean_inc(x_1555);
if (lean_obj_tag(x_1555) == 0)
{
uint8_t x_1556; 
lean_free_object(x_62);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_free_object(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1556 = !lean_is_exclusive(x_1554);
if (x_1556 == 0)
{
lean_object* x_1557; lean_object* x_1558; 
x_1557 = lean_ctor_get(x_1554, 0);
lean_dec(x_1557);
x_1558 = lean_box(0);
lean_ctor_set(x_1554, 0, x_1558);
return x_1554;
}
else
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
x_1559 = lean_ctor_get(x_1554, 1);
lean_inc(x_1559);
lean_dec(x_1554);
x_1560 = lean_box(0);
x_1561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1561, 0, x_1560);
lean_ctor_set(x_1561, 1, x_1559);
return x_1561;
}
}
else
{
lean_object* x_1562; uint8_t x_1563; 
x_1562 = lean_ctor_get(x_1554, 1);
lean_inc(x_1562);
lean_dec(x_1554);
x_1563 = !lean_is_exclusive(x_1555);
if (x_1563 == 0)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
x_1564 = lean_ctor_get(x_1555, 0);
lean_ctor_set(x_1555, 0, x_65);
lean_ctor_set(x_54, 0, x_66);
lean_ctor_set(x_41, 0, x_52);
x_1565 = lean_box(0);
x_1566 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1566, 0, x_1564);
x_1567 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1567, 0, x_1);
x_1568 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_1569 = lean_array_push(x_1568, x_1555);
x_1570 = lean_array_push(x_1569, x_54);
x_1571 = lean_array_push(x_1570, x_41);
x_1572 = lean_array_push(x_1571, x_1565);
x_1573 = lean_array_push(x_1572, x_1566);
x_1574 = lean_array_push(x_1573, x_1567);
x_1575 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1576 = l_Lean_Meta_mkAppOptM(x_1575, x_1574, x_3, x_4, x_5, x_6, x_1562);
if (lean_obj_tag(x_1576) == 0)
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; 
x_1577 = lean_ctor_get(x_1576, 0);
lean_inc(x_1577);
x_1578 = lean_ctor_get(x_1576, 1);
lean_inc(x_1578);
lean_dec(x_1576);
x_1579 = l_Lean_Meta_expandCoe(x_1577, x_3, x_4, x_5, x_6, x_1578);
if (lean_obj_tag(x_1579) == 0)
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; 
x_1580 = lean_ctor_get(x_1579, 0);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_1579, 1);
lean_inc(x_1581);
lean_dec(x_1579);
x_1582 = lean_box(0);
lean_ctor_set(x_62, 1, x_1582);
lean_ctor_set(x_62, 0, x_1580);
x_17 = x_62;
x_18 = x_1581;
goto block_30;
}
else
{
uint8_t x_1583; 
lean_free_object(x_62);
x_1583 = !lean_is_exclusive(x_1579);
if (x_1583 == 0)
{
lean_object* x_1584; lean_object* x_1585; uint8_t x_1586; 
x_1584 = lean_ctor_get(x_1579, 0);
x_1585 = lean_ctor_get(x_1579, 1);
x_1586 = l_Lean_Exception_isInterrupt(x_1584);
if (x_1586 == 0)
{
uint8_t x_1587; 
x_1587 = l_Lean_Exception_isRuntime(x_1584);
if (x_1587 == 0)
{
lean_object* x_1588; 
lean_free_object(x_1579);
lean_dec(x_1584);
x_1588 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_1588;
x_18 = x_1585;
goto block_30;
}
else
{
return x_1579;
}
}
else
{
return x_1579;
}
}
else
{
lean_object* x_1589; lean_object* x_1590; uint8_t x_1591; 
x_1589 = lean_ctor_get(x_1579, 0);
x_1590 = lean_ctor_get(x_1579, 1);
lean_inc(x_1590);
lean_inc(x_1589);
lean_dec(x_1579);
x_1591 = l_Lean_Exception_isInterrupt(x_1589);
if (x_1591 == 0)
{
uint8_t x_1592; 
x_1592 = l_Lean_Exception_isRuntime(x_1589);
if (x_1592 == 0)
{
lean_object* x_1593; 
lean_dec(x_1589);
x_1593 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_1593;
x_18 = x_1590;
goto block_30;
}
else
{
lean_object* x_1594; 
x_1594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1594, 0, x_1589);
lean_ctor_set(x_1594, 1, x_1590);
return x_1594;
}
}
else
{
lean_object* x_1595; 
x_1595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1595, 0, x_1589);
lean_ctor_set(x_1595, 1, x_1590);
return x_1595;
}
}
}
}
else
{
uint8_t x_1596; 
lean_free_object(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1596 = !lean_is_exclusive(x_1576);
if (x_1596 == 0)
{
lean_object* x_1597; lean_object* x_1598; uint8_t x_1599; 
x_1597 = lean_ctor_get(x_1576, 0);
x_1598 = lean_ctor_get(x_1576, 1);
x_1599 = l_Lean_Exception_isInterrupt(x_1597);
if (x_1599 == 0)
{
uint8_t x_1600; 
x_1600 = l_Lean_Exception_isRuntime(x_1597);
if (x_1600 == 0)
{
lean_object* x_1601; 
lean_free_object(x_1576);
lean_dec(x_1597);
x_1601 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_1601;
x_18 = x_1598;
goto block_30;
}
else
{
return x_1576;
}
}
else
{
return x_1576;
}
}
else
{
lean_object* x_1602; lean_object* x_1603; uint8_t x_1604; 
x_1602 = lean_ctor_get(x_1576, 0);
x_1603 = lean_ctor_get(x_1576, 1);
lean_inc(x_1603);
lean_inc(x_1602);
lean_dec(x_1576);
x_1604 = l_Lean_Exception_isInterrupt(x_1602);
if (x_1604 == 0)
{
uint8_t x_1605; 
x_1605 = l_Lean_Exception_isRuntime(x_1602);
if (x_1605 == 0)
{
lean_object* x_1606; 
lean_dec(x_1602);
x_1606 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_1606;
x_18 = x_1603;
goto block_30;
}
else
{
lean_object* x_1607; 
x_1607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1607, 0, x_1602);
lean_ctor_set(x_1607, 1, x_1603);
return x_1607;
}
}
else
{
lean_object* x_1608; 
x_1608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1608, 0, x_1602);
lean_ctor_set(x_1608, 1, x_1603);
return x_1608;
}
}
}
}
else
{
lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
x_1609 = lean_ctor_get(x_1555, 0);
lean_inc(x_1609);
lean_dec(x_1555);
x_1610 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1610, 0, x_65);
lean_ctor_set(x_54, 0, x_66);
lean_ctor_set(x_41, 0, x_52);
x_1611 = lean_box(0);
x_1612 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1612, 0, x_1609);
x_1613 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1613, 0, x_1);
x_1614 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_1615 = lean_array_push(x_1614, x_1610);
x_1616 = lean_array_push(x_1615, x_54);
x_1617 = lean_array_push(x_1616, x_41);
x_1618 = lean_array_push(x_1617, x_1611);
x_1619 = lean_array_push(x_1618, x_1612);
x_1620 = lean_array_push(x_1619, x_1613);
x_1621 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1622 = l_Lean_Meta_mkAppOptM(x_1621, x_1620, x_3, x_4, x_5, x_6, x_1562);
if (lean_obj_tag(x_1622) == 0)
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; 
x_1623 = lean_ctor_get(x_1622, 0);
lean_inc(x_1623);
x_1624 = lean_ctor_get(x_1622, 1);
lean_inc(x_1624);
lean_dec(x_1622);
x_1625 = l_Lean_Meta_expandCoe(x_1623, x_3, x_4, x_5, x_6, x_1624);
if (lean_obj_tag(x_1625) == 0)
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; 
x_1626 = lean_ctor_get(x_1625, 0);
lean_inc(x_1626);
x_1627 = lean_ctor_get(x_1625, 1);
lean_inc(x_1627);
lean_dec(x_1625);
x_1628 = lean_box(0);
lean_ctor_set(x_62, 1, x_1628);
lean_ctor_set(x_62, 0, x_1626);
x_17 = x_62;
x_18 = x_1627;
goto block_30;
}
else
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; uint8_t x_1632; 
lean_free_object(x_62);
x_1629 = lean_ctor_get(x_1625, 0);
lean_inc(x_1629);
x_1630 = lean_ctor_get(x_1625, 1);
lean_inc(x_1630);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1631 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1631 = lean_box(0);
}
x_1632 = l_Lean_Exception_isInterrupt(x_1629);
if (x_1632 == 0)
{
uint8_t x_1633; 
x_1633 = l_Lean_Exception_isRuntime(x_1629);
if (x_1633 == 0)
{
lean_object* x_1634; 
lean_dec(x_1631);
lean_dec(x_1629);
x_1634 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_1634;
x_18 = x_1630;
goto block_30;
}
else
{
lean_object* x_1635; 
if (lean_is_scalar(x_1631)) {
 x_1635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1635 = x_1631;
}
lean_ctor_set(x_1635, 0, x_1629);
lean_ctor_set(x_1635, 1, x_1630);
return x_1635;
}
}
else
{
lean_object* x_1636; 
if (lean_is_scalar(x_1631)) {
 x_1636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1636 = x_1631;
}
lean_ctor_set(x_1636, 0, x_1629);
lean_ctor_set(x_1636, 1, x_1630);
return x_1636;
}
}
}
else
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; uint8_t x_1640; 
lean_free_object(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1637 = lean_ctor_get(x_1622, 0);
lean_inc(x_1637);
x_1638 = lean_ctor_get(x_1622, 1);
lean_inc(x_1638);
if (lean_is_exclusive(x_1622)) {
 lean_ctor_release(x_1622, 0);
 lean_ctor_release(x_1622, 1);
 x_1639 = x_1622;
} else {
 lean_dec_ref(x_1622);
 x_1639 = lean_box(0);
}
x_1640 = l_Lean_Exception_isInterrupt(x_1637);
if (x_1640 == 0)
{
uint8_t x_1641; 
x_1641 = l_Lean_Exception_isRuntime(x_1637);
if (x_1641 == 0)
{
lean_object* x_1642; 
lean_dec(x_1639);
lean_dec(x_1637);
x_1642 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_1642;
x_18 = x_1638;
goto block_30;
}
else
{
lean_object* x_1643; 
if (lean_is_scalar(x_1639)) {
 x_1643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1643 = x_1639;
}
lean_ctor_set(x_1643, 0, x_1637);
lean_ctor_set(x_1643, 1, x_1638);
return x_1643;
}
}
else
{
lean_object* x_1644; 
if (lean_is_scalar(x_1639)) {
 x_1644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1644 = x_1639;
}
lean_ctor_set(x_1644, 0, x_1637);
lean_ctor_set(x_1644, 1, x_1638);
return x_1644;
}
}
}
}
}
else
{
uint8_t x_1645; 
lean_free_object(x_62);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_free_object(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1645 = !lean_is_exclusive(x_1554);
if (x_1645 == 0)
{
return x_1554;
}
else
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; 
x_1646 = lean_ctor_get(x_1554, 0);
x_1647 = lean_ctor_get(x_1554, 1);
lean_inc(x_1647);
lean_inc(x_1646);
lean_dec(x_1554);
x_1648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1648, 0, x_1646);
lean_ctor_set(x_1648, 1, x_1647);
return x_1648;
}
}
}
}
else
{
uint8_t x_1649; 
lean_free_object(x_62);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_free_object(x_41);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1649 = !lean_is_exclusive(x_67);
if (x_1649 == 0)
{
return x_67;
}
else
{
lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; 
x_1650 = lean_ctor_get(x_67, 0);
x_1651 = lean_ctor_get(x_67, 1);
lean_inc(x_1651);
lean_inc(x_1650);
lean_dec(x_67);
x_1652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1652, 0, x_1650);
lean_ctor_set(x_1652, 1, x_1651);
return x_1652;
}
}
}
else
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; 
x_1653 = lean_ctor_get(x_62, 0);
x_1654 = lean_ctor_get(x_62, 1);
lean_inc(x_1654);
lean_inc(x_1653);
lean_dec(x_62);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
lean_inc(x_1653);
x_1655 = l_Lean_Meta_isExprDefEq(x_1653, x_51, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_1655) == 0)
{
lean_object* x_1656; uint8_t x_1657; 
x_1656 = lean_ctor_get(x_1655, 0);
lean_inc(x_1656);
x_1657 = lean_unbox(x_1656);
lean_dec(x_1656);
if (x_1657 == 0)
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; uint8_t x_1662; 
lean_free_object(x_41);
x_1658 = lean_ctor_get(x_1655, 1);
lean_inc(x_1658);
if (lean_is_exclusive(x_1655)) {
 lean_ctor_release(x_1655, 0);
 lean_ctor_release(x_1655, 1);
 x_1659 = x_1655;
} else {
 lean_dec_ref(x_1655);
 x_1659 = lean_box(0);
}
x_1660 = lean_ctor_get(x_5, 2);
lean_inc(x_1660);
x_1661 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1662 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1660, x_1661);
lean_dec(x_1660);
if (x_1662 == 0)
{
lean_object* x_1663; lean_object* x_1664; 
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1663 = lean_box(0);
if (lean_is_scalar(x_1659)) {
 x_1664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1664 = x_1659;
}
lean_ctor_set(x_1664, 0, x_1663);
lean_ctor_set(x_1664, 1, x_1658);
return x_1664;
}
else
{
lean_object* x_1665; 
lean_dec(x_1659);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1653);
x_1665 = lean_infer_type(x_1653, x_3, x_4, x_5, x_6, x_1658);
if (lean_obj_tag(x_1665) == 0)
{
lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; 
x_1666 = lean_ctor_get(x_1665, 0);
lean_inc(x_1666);
x_1667 = lean_ctor_get(x_1665, 1);
lean_inc(x_1667);
lean_dec(x_1665);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1668 = lean_whnf(x_1666, x_3, x_4, x_5, x_6, x_1667);
if (lean_obj_tag(x_1668) == 0)
{
lean_object* x_1669; 
x_1669 = lean_ctor_get(x_1668, 0);
lean_inc(x_1669);
if (lean_obj_tag(x_1669) == 7)
{
lean_object* x_1670; 
x_1670 = lean_ctor_get(x_1669, 1);
lean_inc(x_1670);
if (lean_obj_tag(x_1670) == 3)
{
lean_object* x_1671; 
x_1671 = lean_ctor_get(x_1669, 2);
lean_inc(x_1671);
lean_dec(x_1669);
if (lean_obj_tag(x_1671) == 3)
{
lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; 
x_1672 = lean_ctor_get(x_1668, 1);
lean_inc(x_1672);
lean_dec(x_1668);
x_1673 = lean_ctor_get(x_1670, 0);
lean_inc(x_1673);
lean_dec(x_1670);
x_1674 = lean_ctor_get(x_1671, 0);
lean_inc(x_1674);
lean_dec(x_1671);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_1675 = lean_infer_type(x_51, x_3, x_4, x_5, x_6, x_1672);
if (lean_obj_tag(x_1675) == 0)
{
lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
x_1676 = lean_ctor_get(x_1675, 0);
lean_inc(x_1676);
x_1677 = lean_ctor_get(x_1675, 1);
lean_inc(x_1677);
lean_dec(x_1675);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1678 = lean_whnf(x_1676, x_3, x_4, x_5, x_6, x_1677);
if (lean_obj_tag(x_1678) == 0)
{
lean_object* x_1679; 
x_1679 = lean_ctor_get(x_1678, 0);
lean_inc(x_1679);
if (lean_obj_tag(x_1679) == 7)
{
lean_object* x_1680; 
x_1680 = lean_ctor_get(x_1679, 1);
lean_inc(x_1680);
if (lean_obj_tag(x_1680) == 3)
{
lean_object* x_1681; 
x_1681 = lean_ctor_get(x_1679, 2);
lean_inc(x_1681);
lean_dec(x_1679);
if (lean_obj_tag(x_1681) == 3)
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
x_1682 = lean_ctor_get(x_1678, 1);
lean_inc(x_1682);
lean_dec(x_1678);
x_1683 = lean_ctor_get(x_1680, 0);
lean_inc(x_1683);
lean_dec(x_1680);
x_1684 = lean_ctor_get(x_1681, 0);
lean_inc(x_1684);
lean_dec(x_1681);
x_1685 = l_Lean_Meta_decLevel(x_1673, x_3, x_4, x_5, x_6, x_1682);
if (lean_obj_tag(x_1685) == 0)
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; 
x_1686 = lean_ctor_get(x_1685, 0);
lean_inc(x_1686);
x_1687 = lean_ctor_get(x_1685, 1);
lean_inc(x_1687);
lean_dec(x_1685);
x_1688 = l_Lean_Meta_decLevel(x_1683, x_3, x_4, x_5, x_6, x_1687);
if (lean_obj_tag(x_1688) == 0)
{
lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; uint8_t x_1692; lean_object* x_1693; 
x_1689 = lean_ctor_get(x_1688, 0);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1688, 1);
lean_inc(x_1690);
if (lean_is_exclusive(x_1688)) {
 lean_ctor_release(x_1688, 0);
 lean_ctor_release(x_1688, 1);
 x_1691 = x_1688;
} else {
 lean_dec_ref(x_1688);
 x_1691 = lean_box(0);
}
x_1692 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1686);
x_1693 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1686, x_1689, x_1692, x_3, x_4, x_5, x_6, x_1690);
if (lean_obj_tag(x_1693) == 0)
{
lean_object* x_1694; uint8_t x_1695; 
x_1694 = lean_ctor_get(x_1693, 0);
lean_inc(x_1694);
x_1695 = lean_unbox(x_1694);
lean_dec(x_1694);
if (x_1695 == 0)
{
lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; 
lean_dec(x_1691);
lean_dec(x_1686);
lean_dec(x_1684);
lean_dec(x_1674);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1696 = lean_ctor_get(x_1693, 1);
lean_inc(x_1696);
if (lean_is_exclusive(x_1693)) {
 lean_ctor_release(x_1693, 0);
 lean_ctor_release(x_1693, 1);
 x_1697 = x_1693;
} else {
 lean_dec_ref(x_1693);
 x_1697 = lean_box(0);
}
x_1698 = lean_box(0);
if (lean_is_scalar(x_1697)) {
 x_1699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1699 = x_1697;
}
lean_ctor_set(x_1699, 0, x_1698);
lean_ctor_set(x_1699, 1, x_1696);
return x_1699;
}
else
{
lean_object* x_1700; lean_object* x_1701; 
x_1700 = lean_ctor_get(x_1693, 1);
lean_inc(x_1700);
lean_dec(x_1693);
x_1701 = l_Lean_Meta_decLevel(x_1674, x_3, x_4, x_5, x_6, x_1700);
if (lean_obj_tag(x_1701) == 0)
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; 
x_1702 = lean_ctor_get(x_1701, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1701, 1);
lean_inc(x_1703);
if (lean_is_exclusive(x_1701)) {
 lean_ctor_release(x_1701, 0);
 lean_ctor_release(x_1701, 1);
 x_1704 = x_1701;
} else {
 lean_dec_ref(x_1701);
 x_1704 = lean_box(0);
}
x_1705 = l_Lean_Meta_decLevel(x_1684, x_3, x_4, x_5, x_6, x_1703);
if (lean_obj_tag(x_1705) == 0)
{
lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; 
x_1706 = lean_ctor_get(x_1705, 0);
lean_inc(x_1706);
x_1707 = lean_ctor_get(x_1705, 1);
lean_inc(x_1707);
if (lean_is_exclusive(x_1705)) {
 lean_ctor_release(x_1705, 0);
 lean_ctor_release(x_1705, 1);
 x_1708 = x_1705;
} else {
 lean_dec_ref(x_1705);
 x_1708 = lean_box(0);
}
x_1709 = lean_box(0);
if (lean_is_scalar(x_1708)) {
 x_1710 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1710 = x_1708;
 lean_ctor_set_tag(x_1710, 1);
}
lean_ctor_set(x_1710, 0, x_1706);
lean_ctor_set(x_1710, 1, x_1709);
if (lean_is_scalar(x_1704)) {
 x_1711 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1711 = x_1704;
 lean_ctor_set_tag(x_1711, 1);
}
lean_ctor_set(x_1711, 0, x_1702);
lean_ctor_set(x_1711, 1, x_1710);
if (lean_is_scalar(x_1691)) {
 x_1712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1712 = x_1691;
 lean_ctor_set_tag(x_1712, 1);
}
lean_ctor_set(x_1712, 0, x_1686);
lean_ctor_set(x_1712, 1, x_1711);
x_1713 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1714 = l_Lean_Expr_const___override(x_1713, x_1712);
x_1715 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_1653);
x_1716 = lean_array_push(x_1715, x_1653);
lean_inc(x_51);
x_1717 = lean_array_push(x_1716, x_51);
x_1718 = l_Lean_mkAppN(x_1714, x_1717);
lean_dec(x_1717);
x_1719 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1720 = l_Lean_Meta_trySynthInstance(x_1718, x_1719, x_3, x_4, x_5, x_6, x_1707);
if (lean_obj_tag(x_1720) == 0)
{
lean_object* x_1721; 
x_1721 = lean_ctor_get(x_1720, 0);
lean_inc(x_1721);
if (lean_obj_tag(x_1721) == 1)
{
lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; 
x_1722 = lean_ctor_get(x_1720, 1);
lean_inc(x_1722);
lean_dec(x_1720);
x_1723 = lean_ctor_get(x_1721, 0);
lean_inc(x_1723);
lean_dec(x_1721);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1654);
x_1724 = l_Lean_Meta_getDecLevel(x_1654, x_3, x_4, x_5, x_6, x_1722);
if (lean_obj_tag(x_1724) == 0)
{
lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; 
x_1725 = lean_ctor_get(x_1724, 0);
lean_inc(x_1725);
x_1726 = lean_ctor_get(x_1724, 1);
lean_inc(x_1726);
if (lean_is_exclusive(x_1724)) {
 lean_ctor_release(x_1724, 0);
 lean_ctor_release(x_1724, 1);
 x_1727 = x_1724;
} else {
 lean_dec_ref(x_1724);
 x_1727 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1728 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_1726);
if (lean_obj_tag(x_1728) == 0)
{
lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; 
x_1729 = lean_ctor_get(x_1728, 0);
lean_inc(x_1729);
x_1730 = lean_ctor_get(x_1728, 1);
lean_inc(x_1730);
if (lean_is_exclusive(x_1728)) {
 lean_ctor_release(x_1728, 0);
 lean_ctor_release(x_1728, 1);
 x_1731 = x_1728;
} else {
 lean_dec_ref(x_1728);
 x_1731 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_1732 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_1730);
if (lean_obj_tag(x_1732) == 0)
{
lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; 
x_1733 = lean_ctor_get(x_1732, 0);
lean_inc(x_1733);
x_1734 = lean_ctor_get(x_1732, 1);
lean_inc(x_1734);
if (lean_is_exclusive(x_1732)) {
 lean_ctor_release(x_1732, 0);
 lean_ctor_release(x_1732, 1);
 x_1735 = x_1732;
} else {
 lean_dec_ref(x_1732);
 x_1735 = lean_box(0);
}
if (lean_is_scalar(x_1735)) {
 x_1736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1736 = x_1735;
 lean_ctor_set_tag(x_1736, 1);
}
lean_ctor_set(x_1736, 0, x_1733);
lean_ctor_set(x_1736, 1, x_1709);
if (lean_is_scalar(x_1731)) {
 x_1737 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1737 = x_1731;
 lean_ctor_set_tag(x_1737, 1);
}
lean_ctor_set(x_1737, 0, x_1729);
lean_ctor_set(x_1737, 1, x_1736);
if (lean_is_scalar(x_1727)) {
 x_1738 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1738 = x_1727;
 lean_ctor_set_tag(x_1738, 1);
}
lean_ctor_set(x_1738, 0, x_1725);
lean_ctor_set(x_1738, 1, x_1737);
x_1739 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_1738);
x_1740 = l_Lean_Expr_const___override(x_1739, x_1738);
x_1741 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_1653);
x_1742 = lean_array_push(x_1741, x_1653);
lean_inc(x_51);
x_1743 = lean_array_push(x_1742, x_51);
lean_inc(x_1723);
x_1744 = lean_array_push(x_1743, x_1723);
lean_inc(x_1654);
x_1745 = lean_array_push(x_1744, x_1654);
lean_inc(x_1);
x_1746 = lean_array_push(x_1745, x_1);
x_1747 = l_Lean_mkAppN(x_1740, x_1746);
lean_dec(x_1746);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1747);
x_1748 = lean_infer_type(x_1747, x_3, x_4, x_5, x_6, x_1734);
if (lean_obj_tag(x_1748) == 0)
{
lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; 
x_1749 = lean_ctor_get(x_1748, 0);
lean_inc(x_1749);
x_1750 = lean_ctor_get(x_1748, 1);
lean_inc(x_1750);
lean_dec(x_1748);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_1751 = l_Lean_Meta_isExprDefEq(x_32, x_1749, x_3, x_4, x_5, x_6, x_1750);
if (lean_obj_tag(x_1751) == 0)
{
lean_object* x_1752; uint8_t x_1753; 
x_1752 = lean_ctor_get(x_1751, 0);
lean_inc(x_1752);
x_1753 = lean_unbox(x_1752);
lean_dec(x_1752);
if (x_1753 == 0)
{
lean_object* x_1754; lean_object* x_1755; 
lean_dec(x_1747);
lean_free_object(x_54);
x_1754 = lean_ctor_get(x_1751, 1);
lean_inc(x_1754);
lean_dec(x_1751);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_1755 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_1754);
if (lean_obj_tag(x_1755) == 0)
{
lean_object* x_1756; 
x_1756 = lean_ctor_get(x_1755, 0);
lean_inc(x_1756);
if (lean_obj_tag(x_1756) == 0)
{
lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; 
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1757 = lean_ctor_get(x_1755, 1);
lean_inc(x_1757);
if (lean_is_exclusive(x_1755)) {
 lean_ctor_release(x_1755, 0);
 lean_ctor_release(x_1755, 1);
 x_1758 = x_1755;
} else {
 lean_dec_ref(x_1755);
 x_1758 = lean_box(0);
}
if (lean_is_scalar(x_1758)) {
 x_1759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1759 = x_1758;
}
lean_ctor_set(x_1759, 0, x_1719);
lean_ctor_set(x_1759, 1, x_1757);
return x_1759;
}
else
{
lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; 
x_1760 = lean_ctor_get(x_1755, 1);
lean_inc(x_1760);
lean_dec(x_1755);
x_1761 = lean_ctor_get(x_1756, 0);
lean_inc(x_1761);
lean_dec(x_1756);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1654);
x_1762 = l_Lean_Meta_getLevel(x_1654, x_3, x_4, x_5, x_6, x_1760);
if (lean_obj_tag(x_1762) == 0)
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; 
x_1763 = lean_ctor_get(x_1762, 0);
lean_inc(x_1763);
x_1764 = lean_ctor_get(x_1762, 1);
lean_inc(x_1764);
if (lean_is_exclusive(x_1762)) {
 lean_ctor_release(x_1762, 0);
 lean_ctor_release(x_1762, 1);
 x_1765 = x_1762;
} else {
 lean_dec_ref(x_1762);
 x_1765 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_1766 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_1764);
if (lean_obj_tag(x_1766) == 0)
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; uint8_t x_1781; lean_object* x_1782; lean_object* x_1783; 
x_1767 = lean_ctor_get(x_1766, 0);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1766, 1);
lean_inc(x_1768);
if (lean_is_exclusive(x_1766)) {
 lean_ctor_release(x_1766, 0);
 lean_ctor_release(x_1766, 1);
 x_1769 = x_1766;
} else {
 lean_dec_ref(x_1766);
 x_1769 = lean_box(0);
}
if (lean_is_scalar(x_1769)) {
 x_1770 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1770 = x_1769;
 lean_ctor_set_tag(x_1770, 1);
}
lean_ctor_set(x_1770, 0, x_1767);
lean_ctor_set(x_1770, 1, x_1709);
if (lean_is_scalar(x_1765)) {
 x_1771 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1771 = x_1765;
 lean_ctor_set_tag(x_1771, 1);
}
lean_ctor_set(x_1771, 0, x_1763);
lean_ctor_set(x_1771, 1, x_1770);
x_1772 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1773 = l_Lean_Expr_const___override(x_1772, x_1771);
x_1774 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_1654);
x_1775 = lean_array_push(x_1774, x_1654);
x_1776 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_1777 = lean_array_push(x_1775, x_1776);
lean_inc(x_52);
x_1778 = lean_array_push(x_1777, x_52);
x_1779 = l_Lean_mkAppN(x_1773, x_1778);
lean_dec(x_1778);
x_1780 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_1781 = 0;
lean_inc(x_1654);
x_1782 = l_Lean_Expr_forallE___override(x_1780, x_1654, x_1779, x_1781);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1783 = l_Lean_Meta_trySynthInstance(x_1782, x_1719, x_3, x_4, x_5, x_6, x_1768);
if (lean_obj_tag(x_1783) == 0)
{
lean_object* x_1784; 
x_1784 = lean_ctor_get(x_1783, 0);
lean_inc(x_1784);
if (lean_obj_tag(x_1784) == 1)
{
lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; 
x_1785 = lean_ctor_get(x_1783, 1);
lean_inc(x_1785);
lean_dec(x_1783);
x_1786 = lean_ctor_get(x_1784, 0);
lean_inc(x_1786);
lean_dec(x_1784);
x_1787 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_1788 = l_Lean_Expr_const___override(x_1787, x_1738);
x_1789 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_1790 = lean_array_push(x_1789, x_1653);
x_1791 = lean_array_push(x_1790, x_51);
x_1792 = lean_array_push(x_1791, x_1654);
x_1793 = lean_array_push(x_1792, x_52);
x_1794 = lean_array_push(x_1793, x_1723);
x_1795 = lean_array_push(x_1794, x_1786);
x_1796 = lean_array_push(x_1795, x_1761);
x_1797 = lean_array_push(x_1796, x_1);
x_1798 = l_Lean_mkAppN(x_1788, x_1797);
lean_dec(x_1797);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1799 = l_Lean_Meta_expandCoe(x_1798, x_3, x_4, x_5, x_6, x_1785);
if (lean_obj_tag(x_1799) == 0)
{
lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; 
x_1800 = lean_ctor_get(x_1799, 0);
lean_inc(x_1800);
x_1801 = lean_ctor_get(x_1799, 1);
lean_inc(x_1801);
lean_dec(x_1799);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1800);
x_1802 = lean_infer_type(x_1800, x_3, x_4, x_5, x_6, x_1801);
if (lean_obj_tag(x_1802) == 0)
{
lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; 
x_1803 = lean_ctor_get(x_1802, 0);
lean_inc(x_1803);
x_1804 = lean_ctor_get(x_1802, 1);
lean_inc(x_1804);
lean_dec(x_1802);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1805 = l_Lean_Meta_isExprDefEq(x_32, x_1803, x_3, x_4, x_5, x_6, x_1804);
if (lean_obj_tag(x_1805) == 0)
{
lean_object* x_1806; uint8_t x_1807; 
x_1806 = lean_ctor_get(x_1805, 0);
lean_inc(x_1806);
x_1807 = lean_unbox(x_1806);
lean_dec(x_1806);
if (x_1807 == 0)
{
lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; 
lean_dec(x_1800);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1808 = lean_ctor_get(x_1805, 1);
lean_inc(x_1808);
if (lean_is_exclusive(x_1805)) {
 lean_ctor_release(x_1805, 0);
 lean_ctor_release(x_1805, 1);
 x_1809 = x_1805;
} else {
 lean_dec_ref(x_1805);
 x_1809 = lean_box(0);
}
if (lean_is_scalar(x_1809)) {
 x_1810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1810 = x_1809;
}
lean_ctor_set(x_1810, 0, x_1719);
lean_ctor_set(x_1810, 1, x_1808);
return x_1810;
}
else
{
lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; 
x_1811 = lean_ctor_get(x_1805, 1);
lean_inc(x_1811);
lean_dec(x_1805);
x_1812 = lean_box(0);
x_1813 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1800, x_1812, x_3, x_4, x_5, x_6, x_1811);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1814 = lean_ctor_get(x_1813, 0);
lean_inc(x_1814);
x_1815 = lean_ctor_get(x_1813, 1);
lean_inc(x_1815);
if (lean_is_exclusive(x_1813)) {
 lean_ctor_release(x_1813, 0);
 lean_ctor_release(x_1813, 1);
 x_1816 = x_1813;
} else {
 lean_dec_ref(x_1813);
 x_1816 = lean_box(0);
}
if (lean_is_scalar(x_1816)) {
 x_1817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1817 = x_1816;
}
lean_ctor_set(x_1817, 0, x_1814);
lean_ctor_set(x_1817, 1, x_1815);
return x_1817;
}
}
else
{
lean_object* x_1818; lean_object* x_1819; 
lean_dec(x_1800);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1818 = lean_ctor_get(x_1805, 0);
lean_inc(x_1818);
x_1819 = lean_ctor_get(x_1805, 1);
lean_inc(x_1819);
lean_dec(x_1805);
x_8 = x_1818;
x_9 = x_1819;
goto block_16;
}
}
else
{
lean_object* x_1820; lean_object* x_1821; 
lean_dec(x_1800);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1820 = lean_ctor_get(x_1802, 0);
lean_inc(x_1820);
x_1821 = lean_ctor_get(x_1802, 1);
lean_inc(x_1821);
lean_dec(x_1802);
x_8 = x_1820;
x_9 = x_1821;
goto block_16;
}
}
else
{
lean_object* x_1822; lean_object* x_1823; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1822 = lean_ctor_get(x_1799, 0);
lean_inc(x_1822);
x_1823 = lean_ctor_get(x_1799, 1);
lean_inc(x_1823);
lean_dec(x_1799);
x_8 = x_1822;
x_9 = x_1823;
goto block_16;
}
}
else
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; 
lean_dec(x_1784);
lean_dec(x_1761);
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1824 = lean_ctor_get(x_1783, 1);
lean_inc(x_1824);
if (lean_is_exclusive(x_1783)) {
 lean_ctor_release(x_1783, 0);
 lean_ctor_release(x_1783, 1);
 x_1825 = x_1783;
} else {
 lean_dec_ref(x_1783);
 x_1825 = lean_box(0);
}
if (lean_is_scalar(x_1825)) {
 x_1826 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1826 = x_1825;
}
lean_ctor_set(x_1826, 0, x_1719);
lean_ctor_set(x_1826, 1, x_1824);
return x_1826;
}
}
else
{
lean_object* x_1827; lean_object* x_1828; 
lean_dec(x_1761);
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1827 = lean_ctor_get(x_1783, 0);
lean_inc(x_1827);
x_1828 = lean_ctor_get(x_1783, 1);
lean_inc(x_1828);
lean_dec(x_1783);
x_8 = x_1827;
x_9 = x_1828;
goto block_16;
}
}
else
{
lean_object* x_1829; lean_object* x_1830; 
lean_dec(x_1765);
lean_dec(x_1763);
lean_dec(x_1761);
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1829 = lean_ctor_get(x_1766, 0);
lean_inc(x_1829);
x_1830 = lean_ctor_get(x_1766, 1);
lean_inc(x_1830);
lean_dec(x_1766);
x_8 = x_1829;
x_9 = x_1830;
goto block_16;
}
}
else
{
lean_object* x_1831; lean_object* x_1832; 
lean_dec(x_1761);
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1831 = lean_ctor_get(x_1762, 0);
lean_inc(x_1831);
x_1832 = lean_ctor_get(x_1762, 1);
lean_inc(x_1832);
lean_dec(x_1762);
x_8 = x_1831;
x_9 = x_1832;
goto block_16;
}
}
}
else
{
lean_object* x_1833; lean_object* x_1834; 
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1833 = lean_ctor_get(x_1755, 0);
lean_inc(x_1833);
x_1834 = lean_ctor_get(x_1755, 1);
lean_inc(x_1834);
lean_dec(x_1755);
x_8 = x_1833;
x_9 = x_1834;
goto block_16;
}
}
else
{
lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; 
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1835 = lean_ctor_get(x_1751, 1);
lean_inc(x_1835);
if (lean_is_exclusive(x_1751)) {
 lean_ctor_release(x_1751, 0);
 lean_ctor_release(x_1751, 1);
 x_1836 = x_1751;
} else {
 lean_dec_ref(x_1751);
 x_1836 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_1747);
if (lean_is_scalar(x_1836)) {
 x_1837 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1837 = x_1836;
}
lean_ctor_set(x_1837, 0, x_54);
lean_ctor_set(x_1837, 1, x_1835);
return x_1837;
}
}
else
{
lean_object* x_1838; lean_object* x_1839; 
lean_dec(x_1747);
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1838 = lean_ctor_get(x_1751, 0);
lean_inc(x_1838);
x_1839 = lean_ctor_get(x_1751, 1);
lean_inc(x_1839);
lean_dec(x_1751);
x_8 = x_1838;
x_9 = x_1839;
goto block_16;
}
}
else
{
lean_object* x_1840; lean_object* x_1841; 
lean_dec(x_1747);
lean_dec(x_1738);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1840 = lean_ctor_get(x_1748, 0);
lean_inc(x_1840);
x_1841 = lean_ctor_get(x_1748, 1);
lean_inc(x_1841);
lean_dec(x_1748);
x_8 = x_1840;
x_9 = x_1841;
goto block_16;
}
}
else
{
lean_object* x_1842; lean_object* x_1843; 
lean_dec(x_1731);
lean_dec(x_1729);
lean_dec(x_1727);
lean_dec(x_1725);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1842 = lean_ctor_get(x_1732, 0);
lean_inc(x_1842);
x_1843 = lean_ctor_get(x_1732, 1);
lean_inc(x_1843);
lean_dec(x_1732);
x_8 = x_1842;
x_9 = x_1843;
goto block_16;
}
}
else
{
lean_object* x_1844; lean_object* x_1845; 
lean_dec(x_1727);
lean_dec(x_1725);
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1844 = lean_ctor_get(x_1728, 0);
lean_inc(x_1844);
x_1845 = lean_ctor_get(x_1728, 1);
lean_inc(x_1845);
lean_dec(x_1728);
x_8 = x_1844;
x_9 = x_1845;
goto block_16;
}
}
else
{
lean_object* x_1846; lean_object* x_1847; 
lean_dec(x_1723);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1846 = lean_ctor_get(x_1724, 0);
lean_inc(x_1846);
x_1847 = lean_ctor_get(x_1724, 1);
lean_inc(x_1847);
lean_dec(x_1724);
x_8 = x_1846;
x_9 = x_1847;
goto block_16;
}
}
else
{
lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; 
lean_dec(x_1721);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1848 = lean_ctor_get(x_1720, 1);
lean_inc(x_1848);
if (lean_is_exclusive(x_1720)) {
 lean_ctor_release(x_1720, 0);
 lean_ctor_release(x_1720, 1);
 x_1849 = x_1720;
} else {
 lean_dec_ref(x_1720);
 x_1849 = lean_box(0);
}
if (lean_is_scalar(x_1849)) {
 x_1850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1850 = x_1849;
}
lean_ctor_set(x_1850, 0, x_1719);
lean_ctor_set(x_1850, 1, x_1848);
return x_1850;
}
}
else
{
lean_object* x_1851; lean_object* x_1852; 
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1851 = lean_ctor_get(x_1720, 0);
lean_inc(x_1851);
x_1852 = lean_ctor_get(x_1720, 1);
lean_inc(x_1852);
lean_dec(x_1720);
x_8 = x_1851;
x_9 = x_1852;
goto block_16;
}
}
else
{
lean_object* x_1853; lean_object* x_1854; 
lean_dec(x_1704);
lean_dec(x_1702);
lean_dec(x_1691);
lean_dec(x_1686);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1853 = lean_ctor_get(x_1705, 0);
lean_inc(x_1853);
x_1854 = lean_ctor_get(x_1705, 1);
lean_inc(x_1854);
lean_dec(x_1705);
x_8 = x_1853;
x_9 = x_1854;
goto block_16;
}
}
else
{
lean_object* x_1855; lean_object* x_1856; 
lean_dec(x_1691);
lean_dec(x_1686);
lean_dec(x_1684);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1855 = lean_ctor_get(x_1701, 0);
lean_inc(x_1855);
x_1856 = lean_ctor_get(x_1701, 1);
lean_inc(x_1856);
lean_dec(x_1701);
x_8 = x_1855;
x_9 = x_1856;
goto block_16;
}
}
}
else
{
lean_object* x_1857; lean_object* x_1858; 
lean_dec(x_1691);
lean_dec(x_1686);
lean_dec(x_1684);
lean_dec(x_1674);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1857 = lean_ctor_get(x_1693, 0);
lean_inc(x_1857);
x_1858 = lean_ctor_get(x_1693, 1);
lean_inc(x_1858);
lean_dec(x_1693);
x_8 = x_1857;
x_9 = x_1858;
goto block_16;
}
}
else
{
lean_object* x_1859; lean_object* x_1860; 
lean_dec(x_1686);
lean_dec(x_1684);
lean_dec(x_1674);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1859 = lean_ctor_get(x_1688, 0);
lean_inc(x_1859);
x_1860 = lean_ctor_get(x_1688, 1);
lean_inc(x_1860);
lean_dec(x_1688);
x_8 = x_1859;
x_9 = x_1860;
goto block_16;
}
}
else
{
lean_object* x_1861; lean_object* x_1862; 
lean_dec(x_1684);
lean_dec(x_1683);
lean_dec(x_1674);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1861 = lean_ctor_get(x_1685, 0);
lean_inc(x_1861);
x_1862 = lean_ctor_get(x_1685, 1);
lean_inc(x_1862);
lean_dec(x_1685);
x_8 = x_1861;
x_9 = x_1862;
goto block_16;
}
}
else
{
lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; 
lean_dec(x_1681);
lean_dec(x_1680);
lean_dec(x_1674);
lean_dec(x_1673);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1863 = lean_ctor_get(x_1678, 1);
lean_inc(x_1863);
if (lean_is_exclusive(x_1678)) {
 lean_ctor_release(x_1678, 0);
 lean_ctor_release(x_1678, 1);
 x_1864 = x_1678;
} else {
 lean_dec_ref(x_1678);
 x_1864 = lean_box(0);
}
x_1865 = lean_box(0);
if (lean_is_scalar(x_1864)) {
 x_1866 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1866 = x_1864;
}
lean_ctor_set(x_1866, 0, x_1865);
lean_ctor_set(x_1866, 1, x_1863);
return x_1866;
}
}
else
{
lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; 
lean_dec(x_1680);
lean_dec(x_1679);
lean_dec(x_1674);
lean_dec(x_1673);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1867 = lean_ctor_get(x_1678, 1);
lean_inc(x_1867);
if (lean_is_exclusive(x_1678)) {
 lean_ctor_release(x_1678, 0);
 lean_ctor_release(x_1678, 1);
 x_1868 = x_1678;
} else {
 lean_dec_ref(x_1678);
 x_1868 = lean_box(0);
}
x_1869 = lean_box(0);
if (lean_is_scalar(x_1868)) {
 x_1870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1870 = x_1868;
}
lean_ctor_set(x_1870, 0, x_1869);
lean_ctor_set(x_1870, 1, x_1867);
return x_1870;
}
}
else
{
lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
lean_dec(x_1679);
lean_dec(x_1674);
lean_dec(x_1673);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1871 = lean_ctor_get(x_1678, 1);
lean_inc(x_1871);
if (lean_is_exclusive(x_1678)) {
 lean_ctor_release(x_1678, 0);
 lean_ctor_release(x_1678, 1);
 x_1872 = x_1678;
} else {
 lean_dec_ref(x_1678);
 x_1872 = lean_box(0);
}
x_1873 = lean_box(0);
if (lean_is_scalar(x_1872)) {
 x_1874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1874 = x_1872;
}
lean_ctor_set(x_1874, 0, x_1873);
lean_ctor_set(x_1874, 1, x_1871);
return x_1874;
}
}
else
{
lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; uint8_t x_1878; 
lean_dec(x_1674);
lean_dec(x_1673);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1875 = lean_ctor_get(x_1678, 0);
lean_inc(x_1875);
x_1876 = lean_ctor_get(x_1678, 1);
lean_inc(x_1876);
if (lean_is_exclusive(x_1678)) {
 lean_ctor_release(x_1678, 0);
 lean_ctor_release(x_1678, 1);
 x_1877 = x_1678;
} else {
 lean_dec_ref(x_1678);
 x_1877 = lean_box(0);
}
x_1878 = l_Lean_Exception_isInterrupt(x_1875);
if (x_1878 == 0)
{
uint8_t x_1879; 
x_1879 = l_Lean_Exception_isRuntime(x_1875);
if (x_1879 == 0)
{
lean_object* x_1880; lean_object* x_1881; 
lean_dec(x_1875);
x_1880 = lean_box(0);
if (lean_is_scalar(x_1877)) {
 x_1881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1881 = x_1877;
 lean_ctor_set_tag(x_1881, 0);
}
lean_ctor_set(x_1881, 0, x_1880);
lean_ctor_set(x_1881, 1, x_1876);
return x_1881;
}
else
{
lean_object* x_1882; 
if (lean_is_scalar(x_1877)) {
 x_1882 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1882 = x_1877;
}
lean_ctor_set(x_1882, 0, x_1875);
lean_ctor_set(x_1882, 1, x_1876);
return x_1882;
}
}
else
{
lean_object* x_1883; 
if (lean_is_scalar(x_1877)) {
 x_1883 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1883 = x_1877;
}
lean_ctor_set(x_1883, 0, x_1875);
lean_ctor_set(x_1883, 1, x_1876);
return x_1883;
}
}
}
else
{
lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; uint8_t x_1887; 
lean_dec(x_1674);
lean_dec(x_1673);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1884 = lean_ctor_get(x_1675, 0);
lean_inc(x_1884);
x_1885 = lean_ctor_get(x_1675, 1);
lean_inc(x_1885);
if (lean_is_exclusive(x_1675)) {
 lean_ctor_release(x_1675, 0);
 lean_ctor_release(x_1675, 1);
 x_1886 = x_1675;
} else {
 lean_dec_ref(x_1675);
 x_1886 = lean_box(0);
}
x_1887 = l_Lean_Exception_isInterrupt(x_1884);
if (x_1887 == 0)
{
uint8_t x_1888; 
x_1888 = l_Lean_Exception_isRuntime(x_1884);
if (x_1888 == 0)
{
lean_object* x_1889; lean_object* x_1890; 
lean_dec(x_1884);
x_1889 = lean_box(0);
if (lean_is_scalar(x_1886)) {
 x_1890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1890 = x_1886;
 lean_ctor_set_tag(x_1890, 0);
}
lean_ctor_set(x_1890, 0, x_1889);
lean_ctor_set(x_1890, 1, x_1885);
return x_1890;
}
else
{
lean_object* x_1891; 
if (lean_is_scalar(x_1886)) {
 x_1891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1891 = x_1886;
}
lean_ctor_set(x_1891, 0, x_1884);
lean_ctor_set(x_1891, 1, x_1885);
return x_1891;
}
}
else
{
lean_object* x_1892; 
if (lean_is_scalar(x_1886)) {
 x_1892 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1892 = x_1886;
}
lean_ctor_set(x_1892, 0, x_1884);
lean_ctor_set(x_1892, 1, x_1885);
return x_1892;
}
}
}
else
{
lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; 
lean_dec(x_1671);
lean_dec(x_1670);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1893 = lean_ctor_get(x_1668, 1);
lean_inc(x_1893);
if (lean_is_exclusive(x_1668)) {
 lean_ctor_release(x_1668, 0);
 lean_ctor_release(x_1668, 1);
 x_1894 = x_1668;
} else {
 lean_dec_ref(x_1668);
 x_1894 = lean_box(0);
}
x_1895 = lean_box(0);
if (lean_is_scalar(x_1894)) {
 x_1896 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1896 = x_1894;
}
lean_ctor_set(x_1896, 0, x_1895);
lean_ctor_set(x_1896, 1, x_1893);
return x_1896;
}
}
else
{
lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; 
lean_dec(x_1670);
lean_dec(x_1669);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1897 = lean_ctor_get(x_1668, 1);
lean_inc(x_1897);
if (lean_is_exclusive(x_1668)) {
 lean_ctor_release(x_1668, 0);
 lean_ctor_release(x_1668, 1);
 x_1898 = x_1668;
} else {
 lean_dec_ref(x_1668);
 x_1898 = lean_box(0);
}
x_1899 = lean_box(0);
if (lean_is_scalar(x_1898)) {
 x_1900 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1900 = x_1898;
}
lean_ctor_set(x_1900, 0, x_1899);
lean_ctor_set(x_1900, 1, x_1897);
return x_1900;
}
}
else
{
lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; 
lean_dec(x_1669);
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1901 = lean_ctor_get(x_1668, 1);
lean_inc(x_1901);
if (lean_is_exclusive(x_1668)) {
 lean_ctor_release(x_1668, 0);
 lean_ctor_release(x_1668, 1);
 x_1902 = x_1668;
} else {
 lean_dec_ref(x_1668);
 x_1902 = lean_box(0);
}
x_1903 = lean_box(0);
if (lean_is_scalar(x_1902)) {
 x_1904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1904 = x_1902;
}
lean_ctor_set(x_1904, 0, x_1903);
lean_ctor_set(x_1904, 1, x_1901);
return x_1904;
}
}
else
{
lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; uint8_t x_1908; 
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1905 = lean_ctor_get(x_1668, 0);
lean_inc(x_1905);
x_1906 = lean_ctor_get(x_1668, 1);
lean_inc(x_1906);
if (lean_is_exclusive(x_1668)) {
 lean_ctor_release(x_1668, 0);
 lean_ctor_release(x_1668, 1);
 x_1907 = x_1668;
} else {
 lean_dec_ref(x_1668);
 x_1907 = lean_box(0);
}
x_1908 = l_Lean_Exception_isInterrupt(x_1905);
if (x_1908 == 0)
{
uint8_t x_1909; 
x_1909 = l_Lean_Exception_isRuntime(x_1905);
if (x_1909 == 0)
{
lean_object* x_1910; lean_object* x_1911; 
lean_dec(x_1905);
x_1910 = lean_box(0);
if (lean_is_scalar(x_1907)) {
 x_1911 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1911 = x_1907;
 lean_ctor_set_tag(x_1911, 0);
}
lean_ctor_set(x_1911, 0, x_1910);
lean_ctor_set(x_1911, 1, x_1906);
return x_1911;
}
else
{
lean_object* x_1912; 
if (lean_is_scalar(x_1907)) {
 x_1912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1912 = x_1907;
}
lean_ctor_set(x_1912, 0, x_1905);
lean_ctor_set(x_1912, 1, x_1906);
return x_1912;
}
}
else
{
lean_object* x_1913; 
if (lean_is_scalar(x_1907)) {
 x_1913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1913 = x_1907;
}
lean_ctor_set(x_1913, 0, x_1905);
lean_ctor_set(x_1913, 1, x_1906);
return x_1913;
}
}
}
else
{
lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; uint8_t x_1917; 
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1914 = lean_ctor_get(x_1665, 0);
lean_inc(x_1914);
x_1915 = lean_ctor_get(x_1665, 1);
lean_inc(x_1915);
if (lean_is_exclusive(x_1665)) {
 lean_ctor_release(x_1665, 0);
 lean_ctor_release(x_1665, 1);
 x_1916 = x_1665;
} else {
 lean_dec_ref(x_1665);
 x_1916 = lean_box(0);
}
x_1917 = l_Lean_Exception_isInterrupt(x_1914);
if (x_1917 == 0)
{
uint8_t x_1918; 
x_1918 = l_Lean_Exception_isRuntime(x_1914);
if (x_1918 == 0)
{
lean_object* x_1919; lean_object* x_1920; 
lean_dec(x_1914);
x_1919 = lean_box(0);
if (lean_is_scalar(x_1916)) {
 x_1920 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1920 = x_1916;
 lean_ctor_set_tag(x_1920, 0);
}
lean_ctor_set(x_1920, 0, x_1919);
lean_ctor_set(x_1920, 1, x_1915);
return x_1920;
}
else
{
lean_object* x_1921; 
if (lean_is_scalar(x_1916)) {
 x_1921 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1921 = x_1916;
}
lean_ctor_set(x_1921, 0, x_1914);
lean_ctor_set(x_1921, 1, x_1915);
return x_1921;
}
}
else
{
lean_object* x_1922; 
if (lean_is_scalar(x_1916)) {
 x_1922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1922 = x_1916;
}
lean_ctor_set(x_1922, 0, x_1914);
lean_ctor_set(x_1922, 1, x_1915);
return x_1922;
}
}
}
}
else
{
lean_object* x_1923; lean_object* x_1924; 
lean_dec(x_38);
lean_dec(x_32);
x_1923 = lean_ctor_get(x_1655, 1);
lean_inc(x_1923);
lean_dec(x_1655);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1924 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_1923);
if (lean_obj_tag(x_1924) == 0)
{
lean_object* x_1925; 
x_1925 = lean_ctor_get(x_1924, 0);
lean_inc(x_1925);
if (lean_obj_tag(x_1925) == 0)
{
lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; 
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_free_object(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_1928 = lean_box(0);
if (lean_is_scalar(x_1927)) {
 x_1929 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1929 = x_1927;
}
lean_ctor_set(x_1929, 0, x_1928);
lean_ctor_set(x_1929, 1, x_1926);
return x_1929;
}
else
{
lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; 
x_1930 = lean_ctor_get(x_1924, 1);
lean_inc(x_1930);
lean_dec(x_1924);
x_1931 = lean_ctor_get(x_1925, 0);
lean_inc(x_1931);
if (lean_is_exclusive(x_1925)) {
 lean_ctor_release(x_1925, 0);
 x_1932 = x_1925;
} else {
 lean_dec_ref(x_1925);
 x_1932 = lean_box(0);
}
if (lean_is_scalar(x_1932)) {
 x_1933 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1933 = x_1932;
}
lean_ctor_set(x_1933, 0, x_1653);
lean_ctor_set(x_54, 0, x_1654);
lean_ctor_set(x_41, 0, x_52);
x_1934 = lean_box(0);
x_1935 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1935, 0, x_1931);
x_1936 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1936, 0, x_1);
x_1937 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_1938 = lean_array_push(x_1937, x_1933);
x_1939 = lean_array_push(x_1938, x_54);
x_1940 = lean_array_push(x_1939, x_41);
x_1941 = lean_array_push(x_1940, x_1934);
x_1942 = lean_array_push(x_1941, x_1935);
x_1943 = lean_array_push(x_1942, x_1936);
x_1944 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1945 = l_Lean_Meta_mkAppOptM(x_1944, x_1943, x_3, x_4, x_5, x_6, x_1930);
if (lean_obj_tag(x_1945) == 0)
{
lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; 
x_1946 = lean_ctor_get(x_1945, 0);
lean_inc(x_1946);
x_1947 = lean_ctor_get(x_1945, 1);
lean_inc(x_1947);
lean_dec(x_1945);
x_1948 = l_Lean_Meta_expandCoe(x_1946, x_3, x_4, x_5, x_6, x_1947);
if (lean_obj_tag(x_1948) == 0)
{
lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; 
x_1949 = lean_ctor_get(x_1948, 0);
lean_inc(x_1949);
x_1950 = lean_ctor_get(x_1948, 1);
lean_inc(x_1950);
lean_dec(x_1948);
x_1951 = lean_box(0);
x_1952 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1952, 0, x_1949);
lean_ctor_set(x_1952, 1, x_1951);
x_17 = x_1952;
x_18 = x_1950;
goto block_30;
}
else
{
lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; uint8_t x_1956; 
x_1953 = lean_ctor_get(x_1948, 0);
lean_inc(x_1953);
x_1954 = lean_ctor_get(x_1948, 1);
lean_inc(x_1954);
if (lean_is_exclusive(x_1948)) {
 lean_ctor_release(x_1948, 0);
 lean_ctor_release(x_1948, 1);
 x_1955 = x_1948;
} else {
 lean_dec_ref(x_1948);
 x_1955 = lean_box(0);
}
x_1956 = l_Lean_Exception_isInterrupt(x_1953);
if (x_1956 == 0)
{
uint8_t x_1957; 
x_1957 = l_Lean_Exception_isRuntime(x_1953);
if (x_1957 == 0)
{
lean_object* x_1958; 
lean_dec(x_1955);
lean_dec(x_1953);
x_1958 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_1958;
x_18 = x_1954;
goto block_30;
}
else
{
lean_object* x_1959; 
if (lean_is_scalar(x_1955)) {
 x_1959 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1959 = x_1955;
}
lean_ctor_set(x_1959, 0, x_1953);
lean_ctor_set(x_1959, 1, x_1954);
return x_1959;
}
}
else
{
lean_object* x_1960; 
if (lean_is_scalar(x_1955)) {
 x_1960 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1960 = x_1955;
}
lean_ctor_set(x_1960, 0, x_1953);
lean_ctor_set(x_1960, 1, x_1954);
return x_1960;
}
}
}
else
{
lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; uint8_t x_1964; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1961 = lean_ctor_get(x_1945, 0);
lean_inc(x_1961);
x_1962 = lean_ctor_get(x_1945, 1);
lean_inc(x_1962);
if (lean_is_exclusive(x_1945)) {
 lean_ctor_release(x_1945, 0);
 lean_ctor_release(x_1945, 1);
 x_1963 = x_1945;
} else {
 lean_dec_ref(x_1945);
 x_1963 = lean_box(0);
}
x_1964 = l_Lean_Exception_isInterrupt(x_1961);
if (x_1964 == 0)
{
uint8_t x_1965; 
x_1965 = l_Lean_Exception_isRuntime(x_1961);
if (x_1965 == 0)
{
lean_object* x_1966; 
lean_dec(x_1963);
lean_dec(x_1961);
x_1966 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_1966;
x_18 = x_1962;
goto block_30;
}
else
{
lean_object* x_1967; 
if (lean_is_scalar(x_1963)) {
 x_1967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1967 = x_1963;
}
lean_ctor_set(x_1967, 0, x_1961);
lean_ctor_set(x_1967, 1, x_1962);
return x_1967;
}
}
else
{
lean_object* x_1968; 
if (lean_is_scalar(x_1963)) {
 x_1968 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1968 = x_1963;
}
lean_ctor_set(x_1968, 0, x_1961);
lean_ctor_set(x_1968, 1, x_1962);
return x_1968;
}
}
}
}
else
{
lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; 
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_free_object(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1969 = lean_ctor_get(x_1924, 0);
lean_inc(x_1969);
x_1970 = lean_ctor_get(x_1924, 1);
lean_inc(x_1970);
if (lean_is_exclusive(x_1924)) {
 lean_ctor_release(x_1924, 0);
 lean_ctor_release(x_1924, 1);
 x_1971 = x_1924;
} else {
 lean_dec_ref(x_1924);
 x_1971 = lean_box(0);
}
if (lean_is_scalar(x_1971)) {
 x_1972 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1972 = x_1971;
}
lean_ctor_set(x_1972, 0, x_1969);
lean_ctor_set(x_1972, 1, x_1970);
return x_1972;
}
}
}
else
{
lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; 
lean_dec(x_1654);
lean_dec(x_1653);
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_free_object(x_41);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1973 = lean_ctor_get(x_1655, 0);
lean_inc(x_1973);
x_1974 = lean_ctor_get(x_1655, 1);
lean_inc(x_1974);
if (lean_is_exclusive(x_1655)) {
 lean_ctor_release(x_1655, 0);
 lean_ctor_release(x_1655, 1);
 x_1975 = x_1655;
} else {
 lean_dec_ref(x_1655);
 x_1975 = lean_box(0);
}
if (lean_is_scalar(x_1975)) {
 x_1976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1976 = x_1975;
}
lean_ctor_set(x_1976, 0, x_1973);
lean_ctor_set(x_1976, 1, x_1974);
return x_1976;
}
}
}
else
{
lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; 
x_1977 = lean_ctor_get(x_54, 0);
lean_inc(x_1977);
lean_dec(x_54);
x_1978 = lean_ctor_get(x_53, 1);
lean_inc(x_1978);
lean_dec(x_53);
x_1979 = lean_ctor_get(x_1977, 0);
lean_inc(x_1979);
x_1980 = lean_ctor_get(x_1977, 1);
lean_inc(x_1980);
if (lean_is_exclusive(x_1977)) {
 lean_ctor_release(x_1977, 0);
 lean_ctor_release(x_1977, 1);
 x_1981 = x_1977;
} else {
 lean_dec_ref(x_1977);
 x_1981 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
lean_inc(x_1979);
x_1982 = l_Lean_Meta_isExprDefEq(x_1979, x_51, x_3, x_4, x_5, x_6, x_1978);
if (lean_obj_tag(x_1982) == 0)
{
lean_object* x_1983; uint8_t x_1984; 
x_1983 = lean_ctor_get(x_1982, 0);
lean_inc(x_1983);
x_1984 = lean_unbox(x_1983);
lean_dec(x_1983);
if (x_1984 == 0)
{
lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; uint8_t x_1989; 
lean_dec(x_1981);
lean_free_object(x_41);
x_1985 = lean_ctor_get(x_1982, 1);
lean_inc(x_1985);
if (lean_is_exclusive(x_1982)) {
 lean_ctor_release(x_1982, 0);
 lean_ctor_release(x_1982, 1);
 x_1986 = x_1982;
} else {
 lean_dec_ref(x_1982);
 x_1986 = lean_box(0);
}
x_1987 = lean_ctor_get(x_5, 2);
lean_inc(x_1987);
x_1988 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1989 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1987, x_1988);
lean_dec(x_1987);
if (x_1989 == 0)
{
lean_object* x_1990; lean_object* x_1991; 
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1990 = lean_box(0);
if (lean_is_scalar(x_1986)) {
 x_1991 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1991 = x_1986;
}
lean_ctor_set(x_1991, 0, x_1990);
lean_ctor_set(x_1991, 1, x_1985);
return x_1991;
}
else
{
lean_object* x_1992; 
lean_dec(x_1986);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1979);
x_1992 = lean_infer_type(x_1979, x_3, x_4, x_5, x_6, x_1985);
if (lean_obj_tag(x_1992) == 0)
{
lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; 
x_1993 = lean_ctor_get(x_1992, 0);
lean_inc(x_1993);
x_1994 = lean_ctor_get(x_1992, 1);
lean_inc(x_1994);
lean_dec(x_1992);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1995 = lean_whnf(x_1993, x_3, x_4, x_5, x_6, x_1994);
if (lean_obj_tag(x_1995) == 0)
{
lean_object* x_1996; 
x_1996 = lean_ctor_get(x_1995, 0);
lean_inc(x_1996);
if (lean_obj_tag(x_1996) == 7)
{
lean_object* x_1997; 
x_1997 = lean_ctor_get(x_1996, 1);
lean_inc(x_1997);
if (lean_obj_tag(x_1997) == 3)
{
lean_object* x_1998; 
x_1998 = lean_ctor_get(x_1996, 2);
lean_inc(x_1998);
lean_dec(x_1996);
if (lean_obj_tag(x_1998) == 3)
{
lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; 
x_1999 = lean_ctor_get(x_1995, 1);
lean_inc(x_1999);
lean_dec(x_1995);
x_2000 = lean_ctor_get(x_1997, 0);
lean_inc(x_2000);
lean_dec(x_1997);
x_2001 = lean_ctor_get(x_1998, 0);
lean_inc(x_2001);
lean_dec(x_1998);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_2002 = lean_infer_type(x_51, x_3, x_4, x_5, x_6, x_1999);
if (lean_obj_tag(x_2002) == 0)
{
lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; 
x_2003 = lean_ctor_get(x_2002, 0);
lean_inc(x_2003);
x_2004 = lean_ctor_get(x_2002, 1);
lean_inc(x_2004);
lean_dec(x_2002);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2005 = lean_whnf(x_2003, x_3, x_4, x_5, x_6, x_2004);
if (lean_obj_tag(x_2005) == 0)
{
lean_object* x_2006; 
x_2006 = lean_ctor_get(x_2005, 0);
lean_inc(x_2006);
if (lean_obj_tag(x_2006) == 7)
{
lean_object* x_2007; 
x_2007 = lean_ctor_get(x_2006, 1);
lean_inc(x_2007);
if (lean_obj_tag(x_2007) == 3)
{
lean_object* x_2008; 
x_2008 = lean_ctor_get(x_2006, 2);
lean_inc(x_2008);
lean_dec(x_2006);
if (lean_obj_tag(x_2008) == 3)
{
lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; 
x_2009 = lean_ctor_get(x_2005, 1);
lean_inc(x_2009);
lean_dec(x_2005);
x_2010 = lean_ctor_get(x_2007, 0);
lean_inc(x_2010);
lean_dec(x_2007);
x_2011 = lean_ctor_get(x_2008, 0);
lean_inc(x_2011);
lean_dec(x_2008);
x_2012 = l_Lean_Meta_decLevel(x_2000, x_3, x_4, x_5, x_6, x_2009);
if (lean_obj_tag(x_2012) == 0)
{
lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; 
x_2013 = lean_ctor_get(x_2012, 0);
lean_inc(x_2013);
x_2014 = lean_ctor_get(x_2012, 1);
lean_inc(x_2014);
lean_dec(x_2012);
x_2015 = l_Lean_Meta_decLevel(x_2010, x_3, x_4, x_5, x_6, x_2014);
if (lean_obj_tag(x_2015) == 0)
{
lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; uint8_t x_2019; lean_object* x_2020; 
x_2016 = lean_ctor_get(x_2015, 0);
lean_inc(x_2016);
x_2017 = lean_ctor_get(x_2015, 1);
lean_inc(x_2017);
if (lean_is_exclusive(x_2015)) {
 lean_ctor_release(x_2015, 0);
 lean_ctor_release(x_2015, 1);
 x_2018 = x_2015;
} else {
 lean_dec_ref(x_2015);
 x_2018 = lean_box(0);
}
x_2019 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2013);
x_2020 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_2013, x_2016, x_2019, x_3, x_4, x_5, x_6, x_2017);
if (lean_obj_tag(x_2020) == 0)
{
lean_object* x_2021; uint8_t x_2022; 
x_2021 = lean_ctor_get(x_2020, 0);
lean_inc(x_2021);
x_2022 = lean_unbox(x_2021);
lean_dec(x_2021);
if (x_2022 == 0)
{
lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; 
lean_dec(x_2018);
lean_dec(x_2013);
lean_dec(x_2011);
lean_dec(x_2001);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2023 = lean_ctor_get(x_2020, 1);
lean_inc(x_2023);
if (lean_is_exclusive(x_2020)) {
 lean_ctor_release(x_2020, 0);
 lean_ctor_release(x_2020, 1);
 x_2024 = x_2020;
} else {
 lean_dec_ref(x_2020);
 x_2024 = lean_box(0);
}
x_2025 = lean_box(0);
if (lean_is_scalar(x_2024)) {
 x_2026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2026 = x_2024;
}
lean_ctor_set(x_2026, 0, x_2025);
lean_ctor_set(x_2026, 1, x_2023);
return x_2026;
}
else
{
lean_object* x_2027; lean_object* x_2028; 
x_2027 = lean_ctor_get(x_2020, 1);
lean_inc(x_2027);
lean_dec(x_2020);
x_2028 = l_Lean_Meta_decLevel(x_2001, x_3, x_4, x_5, x_6, x_2027);
if (lean_obj_tag(x_2028) == 0)
{
lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; 
x_2029 = lean_ctor_get(x_2028, 0);
lean_inc(x_2029);
x_2030 = lean_ctor_get(x_2028, 1);
lean_inc(x_2030);
if (lean_is_exclusive(x_2028)) {
 lean_ctor_release(x_2028, 0);
 lean_ctor_release(x_2028, 1);
 x_2031 = x_2028;
} else {
 lean_dec_ref(x_2028);
 x_2031 = lean_box(0);
}
x_2032 = l_Lean_Meta_decLevel(x_2011, x_3, x_4, x_5, x_6, x_2030);
if (lean_obj_tag(x_2032) == 0)
{
lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; 
x_2033 = lean_ctor_get(x_2032, 0);
lean_inc(x_2033);
x_2034 = lean_ctor_get(x_2032, 1);
lean_inc(x_2034);
if (lean_is_exclusive(x_2032)) {
 lean_ctor_release(x_2032, 0);
 lean_ctor_release(x_2032, 1);
 x_2035 = x_2032;
} else {
 lean_dec_ref(x_2032);
 x_2035 = lean_box(0);
}
x_2036 = lean_box(0);
if (lean_is_scalar(x_2035)) {
 x_2037 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2037 = x_2035;
 lean_ctor_set_tag(x_2037, 1);
}
lean_ctor_set(x_2037, 0, x_2033);
lean_ctor_set(x_2037, 1, x_2036);
if (lean_is_scalar(x_2031)) {
 x_2038 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2038 = x_2031;
 lean_ctor_set_tag(x_2038, 1);
}
lean_ctor_set(x_2038, 0, x_2029);
lean_ctor_set(x_2038, 1, x_2037);
if (lean_is_scalar(x_2018)) {
 x_2039 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2039 = x_2018;
 lean_ctor_set_tag(x_2039, 1);
}
lean_ctor_set(x_2039, 0, x_2013);
lean_ctor_set(x_2039, 1, x_2038);
x_2040 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2041 = l_Lean_Expr_const___override(x_2040, x_2039);
x_2042 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_1979);
x_2043 = lean_array_push(x_2042, x_1979);
lean_inc(x_51);
x_2044 = lean_array_push(x_2043, x_51);
x_2045 = l_Lean_mkAppN(x_2041, x_2044);
lean_dec(x_2044);
x_2046 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2047 = l_Lean_Meta_trySynthInstance(x_2045, x_2046, x_3, x_4, x_5, x_6, x_2034);
if (lean_obj_tag(x_2047) == 0)
{
lean_object* x_2048; 
x_2048 = lean_ctor_get(x_2047, 0);
lean_inc(x_2048);
if (lean_obj_tag(x_2048) == 1)
{
lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; 
x_2049 = lean_ctor_get(x_2047, 1);
lean_inc(x_2049);
lean_dec(x_2047);
x_2050 = lean_ctor_get(x_2048, 0);
lean_inc(x_2050);
lean_dec(x_2048);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1980);
x_2051 = l_Lean_Meta_getDecLevel(x_1980, x_3, x_4, x_5, x_6, x_2049);
if (lean_obj_tag(x_2051) == 0)
{
lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; 
x_2052 = lean_ctor_get(x_2051, 0);
lean_inc(x_2052);
x_2053 = lean_ctor_get(x_2051, 1);
lean_inc(x_2053);
if (lean_is_exclusive(x_2051)) {
 lean_ctor_release(x_2051, 0);
 lean_ctor_release(x_2051, 1);
 x_2054 = x_2051;
} else {
 lean_dec_ref(x_2051);
 x_2054 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2055 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_2053);
if (lean_obj_tag(x_2055) == 0)
{
lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; 
x_2056 = lean_ctor_get(x_2055, 0);
lean_inc(x_2056);
x_2057 = lean_ctor_get(x_2055, 1);
lean_inc(x_2057);
if (lean_is_exclusive(x_2055)) {
 lean_ctor_release(x_2055, 0);
 lean_ctor_release(x_2055, 1);
 x_2058 = x_2055;
} else {
 lean_dec_ref(x_2055);
 x_2058 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_2059 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_2057);
if (lean_obj_tag(x_2059) == 0)
{
lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; 
x_2060 = lean_ctor_get(x_2059, 0);
lean_inc(x_2060);
x_2061 = lean_ctor_get(x_2059, 1);
lean_inc(x_2061);
if (lean_is_exclusive(x_2059)) {
 lean_ctor_release(x_2059, 0);
 lean_ctor_release(x_2059, 1);
 x_2062 = x_2059;
} else {
 lean_dec_ref(x_2059);
 x_2062 = lean_box(0);
}
if (lean_is_scalar(x_2062)) {
 x_2063 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2063 = x_2062;
 lean_ctor_set_tag(x_2063, 1);
}
lean_ctor_set(x_2063, 0, x_2060);
lean_ctor_set(x_2063, 1, x_2036);
if (lean_is_scalar(x_2058)) {
 x_2064 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2064 = x_2058;
 lean_ctor_set_tag(x_2064, 1);
}
lean_ctor_set(x_2064, 0, x_2056);
lean_ctor_set(x_2064, 1, x_2063);
if (lean_is_scalar(x_2054)) {
 x_2065 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2065 = x_2054;
 lean_ctor_set_tag(x_2065, 1);
}
lean_ctor_set(x_2065, 0, x_2052);
lean_ctor_set(x_2065, 1, x_2064);
x_2066 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_2065);
x_2067 = l_Lean_Expr_const___override(x_2066, x_2065);
x_2068 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_1979);
x_2069 = lean_array_push(x_2068, x_1979);
lean_inc(x_51);
x_2070 = lean_array_push(x_2069, x_51);
lean_inc(x_2050);
x_2071 = lean_array_push(x_2070, x_2050);
lean_inc(x_1980);
x_2072 = lean_array_push(x_2071, x_1980);
lean_inc(x_1);
x_2073 = lean_array_push(x_2072, x_1);
x_2074 = l_Lean_mkAppN(x_2067, x_2073);
lean_dec(x_2073);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2074);
x_2075 = lean_infer_type(x_2074, x_3, x_4, x_5, x_6, x_2061);
if (lean_obj_tag(x_2075) == 0)
{
lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; 
x_2076 = lean_ctor_get(x_2075, 0);
lean_inc(x_2076);
x_2077 = lean_ctor_get(x_2075, 1);
lean_inc(x_2077);
lean_dec(x_2075);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_2078 = l_Lean_Meta_isExprDefEq(x_32, x_2076, x_3, x_4, x_5, x_6, x_2077);
if (lean_obj_tag(x_2078) == 0)
{
lean_object* x_2079; uint8_t x_2080; 
x_2079 = lean_ctor_get(x_2078, 0);
lean_inc(x_2079);
x_2080 = lean_unbox(x_2079);
lean_dec(x_2079);
if (x_2080 == 0)
{
lean_object* x_2081; lean_object* x_2082; 
lean_dec(x_2074);
x_2081 = lean_ctor_get(x_2078, 1);
lean_inc(x_2081);
lean_dec(x_2078);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_2082 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_2081);
if (lean_obj_tag(x_2082) == 0)
{
lean_object* x_2083; 
x_2083 = lean_ctor_get(x_2082, 0);
lean_inc(x_2083);
if (lean_obj_tag(x_2083) == 0)
{
lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; 
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2084 = lean_ctor_get(x_2082, 1);
lean_inc(x_2084);
if (lean_is_exclusive(x_2082)) {
 lean_ctor_release(x_2082, 0);
 lean_ctor_release(x_2082, 1);
 x_2085 = x_2082;
} else {
 lean_dec_ref(x_2082);
 x_2085 = lean_box(0);
}
if (lean_is_scalar(x_2085)) {
 x_2086 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2086 = x_2085;
}
lean_ctor_set(x_2086, 0, x_2046);
lean_ctor_set(x_2086, 1, x_2084);
return x_2086;
}
else
{
lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; 
x_2087 = lean_ctor_get(x_2082, 1);
lean_inc(x_2087);
lean_dec(x_2082);
x_2088 = lean_ctor_get(x_2083, 0);
lean_inc(x_2088);
lean_dec(x_2083);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1980);
x_2089 = l_Lean_Meta_getLevel(x_1980, x_3, x_4, x_5, x_6, x_2087);
if (lean_obj_tag(x_2089) == 0)
{
lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; 
x_2090 = lean_ctor_get(x_2089, 0);
lean_inc(x_2090);
x_2091 = lean_ctor_get(x_2089, 1);
lean_inc(x_2091);
if (lean_is_exclusive(x_2089)) {
 lean_ctor_release(x_2089, 0);
 lean_ctor_release(x_2089, 1);
 x_2092 = x_2089;
} else {
 lean_dec_ref(x_2089);
 x_2092 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_2093 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_2091);
if (lean_obj_tag(x_2093) == 0)
{
lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; uint8_t x_2108; lean_object* x_2109; lean_object* x_2110; 
x_2094 = lean_ctor_get(x_2093, 0);
lean_inc(x_2094);
x_2095 = lean_ctor_get(x_2093, 1);
lean_inc(x_2095);
if (lean_is_exclusive(x_2093)) {
 lean_ctor_release(x_2093, 0);
 lean_ctor_release(x_2093, 1);
 x_2096 = x_2093;
} else {
 lean_dec_ref(x_2093);
 x_2096 = lean_box(0);
}
if (lean_is_scalar(x_2096)) {
 x_2097 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2097 = x_2096;
 lean_ctor_set_tag(x_2097, 1);
}
lean_ctor_set(x_2097, 0, x_2094);
lean_ctor_set(x_2097, 1, x_2036);
if (lean_is_scalar(x_2092)) {
 x_2098 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2098 = x_2092;
 lean_ctor_set_tag(x_2098, 1);
}
lean_ctor_set(x_2098, 0, x_2090);
lean_ctor_set(x_2098, 1, x_2097);
x_2099 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_2100 = l_Lean_Expr_const___override(x_2099, x_2098);
x_2101 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_1980);
x_2102 = lean_array_push(x_2101, x_1980);
x_2103 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_2104 = lean_array_push(x_2102, x_2103);
lean_inc(x_52);
x_2105 = lean_array_push(x_2104, x_52);
x_2106 = l_Lean_mkAppN(x_2100, x_2105);
lean_dec(x_2105);
x_2107 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_2108 = 0;
lean_inc(x_1980);
x_2109 = l_Lean_Expr_forallE___override(x_2107, x_1980, x_2106, x_2108);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2110 = l_Lean_Meta_trySynthInstance(x_2109, x_2046, x_3, x_4, x_5, x_6, x_2095);
if (lean_obj_tag(x_2110) == 0)
{
lean_object* x_2111; 
x_2111 = lean_ctor_get(x_2110, 0);
lean_inc(x_2111);
if (lean_obj_tag(x_2111) == 1)
{
lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; 
x_2112 = lean_ctor_get(x_2110, 1);
lean_inc(x_2112);
lean_dec(x_2110);
x_2113 = lean_ctor_get(x_2111, 0);
lean_inc(x_2113);
lean_dec(x_2111);
x_2114 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_2115 = l_Lean_Expr_const___override(x_2114, x_2065);
x_2116 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_2117 = lean_array_push(x_2116, x_1979);
x_2118 = lean_array_push(x_2117, x_51);
x_2119 = lean_array_push(x_2118, x_1980);
x_2120 = lean_array_push(x_2119, x_52);
x_2121 = lean_array_push(x_2120, x_2050);
x_2122 = lean_array_push(x_2121, x_2113);
x_2123 = lean_array_push(x_2122, x_2088);
x_2124 = lean_array_push(x_2123, x_1);
x_2125 = l_Lean_mkAppN(x_2115, x_2124);
lean_dec(x_2124);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2126 = l_Lean_Meta_expandCoe(x_2125, x_3, x_4, x_5, x_6, x_2112);
if (lean_obj_tag(x_2126) == 0)
{
lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
x_2127 = lean_ctor_get(x_2126, 0);
lean_inc(x_2127);
x_2128 = lean_ctor_get(x_2126, 1);
lean_inc(x_2128);
lean_dec(x_2126);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2127);
x_2129 = lean_infer_type(x_2127, x_3, x_4, x_5, x_6, x_2128);
if (lean_obj_tag(x_2129) == 0)
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; 
x_2130 = lean_ctor_get(x_2129, 0);
lean_inc(x_2130);
x_2131 = lean_ctor_get(x_2129, 1);
lean_inc(x_2131);
lean_dec(x_2129);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2132 = l_Lean_Meta_isExprDefEq(x_32, x_2130, x_3, x_4, x_5, x_6, x_2131);
if (lean_obj_tag(x_2132) == 0)
{
lean_object* x_2133; uint8_t x_2134; 
x_2133 = lean_ctor_get(x_2132, 0);
lean_inc(x_2133);
x_2134 = lean_unbox(x_2133);
lean_dec(x_2133);
if (x_2134 == 0)
{
lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; 
lean_dec(x_2127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2135 = lean_ctor_get(x_2132, 1);
lean_inc(x_2135);
if (lean_is_exclusive(x_2132)) {
 lean_ctor_release(x_2132, 0);
 lean_ctor_release(x_2132, 1);
 x_2136 = x_2132;
} else {
 lean_dec_ref(x_2132);
 x_2136 = lean_box(0);
}
if (lean_is_scalar(x_2136)) {
 x_2137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2137 = x_2136;
}
lean_ctor_set(x_2137, 0, x_2046);
lean_ctor_set(x_2137, 1, x_2135);
return x_2137;
}
else
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; 
x_2138 = lean_ctor_get(x_2132, 1);
lean_inc(x_2138);
lean_dec(x_2132);
x_2139 = lean_box(0);
x_2140 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2127, x_2139, x_3, x_4, x_5, x_6, x_2138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2141 = lean_ctor_get(x_2140, 0);
lean_inc(x_2141);
x_2142 = lean_ctor_get(x_2140, 1);
lean_inc(x_2142);
if (lean_is_exclusive(x_2140)) {
 lean_ctor_release(x_2140, 0);
 lean_ctor_release(x_2140, 1);
 x_2143 = x_2140;
} else {
 lean_dec_ref(x_2140);
 x_2143 = lean_box(0);
}
if (lean_is_scalar(x_2143)) {
 x_2144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2144 = x_2143;
}
lean_ctor_set(x_2144, 0, x_2141);
lean_ctor_set(x_2144, 1, x_2142);
return x_2144;
}
}
else
{
lean_object* x_2145; lean_object* x_2146; 
lean_dec(x_2127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2145 = lean_ctor_get(x_2132, 0);
lean_inc(x_2145);
x_2146 = lean_ctor_get(x_2132, 1);
lean_inc(x_2146);
lean_dec(x_2132);
x_8 = x_2145;
x_9 = x_2146;
goto block_16;
}
}
else
{
lean_object* x_2147; lean_object* x_2148; 
lean_dec(x_2127);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2147 = lean_ctor_get(x_2129, 0);
lean_inc(x_2147);
x_2148 = lean_ctor_get(x_2129, 1);
lean_inc(x_2148);
lean_dec(x_2129);
x_8 = x_2147;
x_9 = x_2148;
goto block_16;
}
}
else
{
lean_object* x_2149; lean_object* x_2150; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2149 = lean_ctor_get(x_2126, 0);
lean_inc(x_2149);
x_2150 = lean_ctor_get(x_2126, 1);
lean_inc(x_2150);
lean_dec(x_2126);
x_8 = x_2149;
x_9 = x_2150;
goto block_16;
}
}
else
{
lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; 
lean_dec(x_2111);
lean_dec(x_2088);
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2151 = lean_ctor_get(x_2110, 1);
lean_inc(x_2151);
if (lean_is_exclusive(x_2110)) {
 lean_ctor_release(x_2110, 0);
 lean_ctor_release(x_2110, 1);
 x_2152 = x_2110;
} else {
 lean_dec_ref(x_2110);
 x_2152 = lean_box(0);
}
if (lean_is_scalar(x_2152)) {
 x_2153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2153 = x_2152;
}
lean_ctor_set(x_2153, 0, x_2046);
lean_ctor_set(x_2153, 1, x_2151);
return x_2153;
}
}
else
{
lean_object* x_2154; lean_object* x_2155; 
lean_dec(x_2088);
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2154 = lean_ctor_get(x_2110, 0);
lean_inc(x_2154);
x_2155 = lean_ctor_get(x_2110, 1);
lean_inc(x_2155);
lean_dec(x_2110);
x_8 = x_2154;
x_9 = x_2155;
goto block_16;
}
}
else
{
lean_object* x_2156; lean_object* x_2157; 
lean_dec(x_2092);
lean_dec(x_2090);
lean_dec(x_2088);
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2156 = lean_ctor_get(x_2093, 0);
lean_inc(x_2156);
x_2157 = lean_ctor_get(x_2093, 1);
lean_inc(x_2157);
lean_dec(x_2093);
x_8 = x_2156;
x_9 = x_2157;
goto block_16;
}
}
else
{
lean_object* x_2158; lean_object* x_2159; 
lean_dec(x_2088);
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2158 = lean_ctor_get(x_2089, 0);
lean_inc(x_2158);
x_2159 = lean_ctor_get(x_2089, 1);
lean_inc(x_2159);
lean_dec(x_2089);
x_8 = x_2158;
x_9 = x_2159;
goto block_16;
}
}
}
else
{
lean_object* x_2160; lean_object* x_2161; 
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2160 = lean_ctor_get(x_2082, 0);
lean_inc(x_2160);
x_2161 = lean_ctor_get(x_2082, 1);
lean_inc(x_2161);
lean_dec(x_2082);
x_8 = x_2160;
x_9 = x_2161;
goto block_16;
}
}
else
{
lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; 
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2162 = lean_ctor_get(x_2078, 1);
lean_inc(x_2162);
if (lean_is_exclusive(x_2078)) {
 lean_ctor_release(x_2078, 0);
 lean_ctor_release(x_2078, 1);
 x_2163 = x_2078;
} else {
 lean_dec_ref(x_2078);
 x_2163 = lean_box(0);
}
x_2164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2164, 0, x_2074);
if (lean_is_scalar(x_2163)) {
 x_2165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2165 = x_2163;
}
lean_ctor_set(x_2165, 0, x_2164);
lean_ctor_set(x_2165, 1, x_2162);
return x_2165;
}
}
else
{
lean_object* x_2166; lean_object* x_2167; 
lean_dec(x_2074);
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2166 = lean_ctor_get(x_2078, 0);
lean_inc(x_2166);
x_2167 = lean_ctor_get(x_2078, 1);
lean_inc(x_2167);
lean_dec(x_2078);
x_8 = x_2166;
x_9 = x_2167;
goto block_16;
}
}
else
{
lean_object* x_2168; lean_object* x_2169; 
lean_dec(x_2074);
lean_dec(x_2065);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2168 = lean_ctor_get(x_2075, 0);
lean_inc(x_2168);
x_2169 = lean_ctor_get(x_2075, 1);
lean_inc(x_2169);
lean_dec(x_2075);
x_8 = x_2168;
x_9 = x_2169;
goto block_16;
}
}
else
{
lean_object* x_2170; lean_object* x_2171; 
lean_dec(x_2058);
lean_dec(x_2056);
lean_dec(x_2054);
lean_dec(x_2052);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2170 = lean_ctor_get(x_2059, 0);
lean_inc(x_2170);
x_2171 = lean_ctor_get(x_2059, 1);
lean_inc(x_2171);
lean_dec(x_2059);
x_8 = x_2170;
x_9 = x_2171;
goto block_16;
}
}
else
{
lean_object* x_2172; lean_object* x_2173; 
lean_dec(x_2054);
lean_dec(x_2052);
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2172 = lean_ctor_get(x_2055, 0);
lean_inc(x_2172);
x_2173 = lean_ctor_get(x_2055, 1);
lean_inc(x_2173);
lean_dec(x_2055);
x_8 = x_2172;
x_9 = x_2173;
goto block_16;
}
}
else
{
lean_object* x_2174; lean_object* x_2175; 
lean_dec(x_2050);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2174 = lean_ctor_get(x_2051, 0);
lean_inc(x_2174);
x_2175 = lean_ctor_get(x_2051, 1);
lean_inc(x_2175);
lean_dec(x_2051);
x_8 = x_2174;
x_9 = x_2175;
goto block_16;
}
}
else
{
lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; 
lean_dec(x_2048);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2176 = lean_ctor_get(x_2047, 1);
lean_inc(x_2176);
if (lean_is_exclusive(x_2047)) {
 lean_ctor_release(x_2047, 0);
 lean_ctor_release(x_2047, 1);
 x_2177 = x_2047;
} else {
 lean_dec_ref(x_2047);
 x_2177 = lean_box(0);
}
if (lean_is_scalar(x_2177)) {
 x_2178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2178 = x_2177;
}
lean_ctor_set(x_2178, 0, x_2046);
lean_ctor_set(x_2178, 1, x_2176);
return x_2178;
}
}
else
{
lean_object* x_2179; lean_object* x_2180; 
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2179 = lean_ctor_get(x_2047, 0);
lean_inc(x_2179);
x_2180 = lean_ctor_get(x_2047, 1);
lean_inc(x_2180);
lean_dec(x_2047);
x_8 = x_2179;
x_9 = x_2180;
goto block_16;
}
}
else
{
lean_object* x_2181; lean_object* x_2182; 
lean_dec(x_2031);
lean_dec(x_2029);
lean_dec(x_2018);
lean_dec(x_2013);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2181 = lean_ctor_get(x_2032, 0);
lean_inc(x_2181);
x_2182 = lean_ctor_get(x_2032, 1);
lean_inc(x_2182);
lean_dec(x_2032);
x_8 = x_2181;
x_9 = x_2182;
goto block_16;
}
}
else
{
lean_object* x_2183; lean_object* x_2184; 
lean_dec(x_2018);
lean_dec(x_2013);
lean_dec(x_2011);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2183 = lean_ctor_get(x_2028, 0);
lean_inc(x_2183);
x_2184 = lean_ctor_get(x_2028, 1);
lean_inc(x_2184);
lean_dec(x_2028);
x_8 = x_2183;
x_9 = x_2184;
goto block_16;
}
}
}
else
{
lean_object* x_2185; lean_object* x_2186; 
lean_dec(x_2018);
lean_dec(x_2013);
lean_dec(x_2011);
lean_dec(x_2001);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2185 = lean_ctor_get(x_2020, 0);
lean_inc(x_2185);
x_2186 = lean_ctor_get(x_2020, 1);
lean_inc(x_2186);
lean_dec(x_2020);
x_8 = x_2185;
x_9 = x_2186;
goto block_16;
}
}
else
{
lean_object* x_2187; lean_object* x_2188; 
lean_dec(x_2013);
lean_dec(x_2011);
lean_dec(x_2001);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2187 = lean_ctor_get(x_2015, 0);
lean_inc(x_2187);
x_2188 = lean_ctor_get(x_2015, 1);
lean_inc(x_2188);
lean_dec(x_2015);
x_8 = x_2187;
x_9 = x_2188;
goto block_16;
}
}
else
{
lean_object* x_2189; lean_object* x_2190; 
lean_dec(x_2011);
lean_dec(x_2010);
lean_dec(x_2001);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2189 = lean_ctor_get(x_2012, 0);
lean_inc(x_2189);
x_2190 = lean_ctor_get(x_2012, 1);
lean_inc(x_2190);
lean_dec(x_2012);
x_8 = x_2189;
x_9 = x_2190;
goto block_16;
}
}
else
{
lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; 
lean_dec(x_2008);
lean_dec(x_2007);
lean_dec(x_2001);
lean_dec(x_2000);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2191 = lean_ctor_get(x_2005, 1);
lean_inc(x_2191);
if (lean_is_exclusive(x_2005)) {
 lean_ctor_release(x_2005, 0);
 lean_ctor_release(x_2005, 1);
 x_2192 = x_2005;
} else {
 lean_dec_ref(x_2005);
 x_2192 = lean_box(0);
}
x_2193 = lean_box(0);
if (lean_is_scalar(x_2192)) {
 x_2194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2194 = x_2192;
}
lean_ctor_set(x_2194, 0, x_2193);
lean_ctor_set(x_2194, 1, x_2191);
return x_2194;
}
}
else
{
lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; 
lean_dec(x_2007);
lean_dec(x_2006);
lean_dec(x_2001);
lean_dec(x_2000);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2195 = lean_ctor_get(x_2005, 1);
lean_inc(x_2195);
if (lean_is_exclusive(x_2005)) {
 lean_ctor_release(x_2005, 0);
 lean_ctor_release(x_2005, 1);
 x_2196 = x_2005;
} else {
 lean_dec_ref(x_2005);
 x_2196 = lean_box(0);
}
x_2197 = lean_box(0);
if (lean_is_scalar(x_2196)) {
 x_2198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2198 = x_2196;
}
lean_ctor_set(x_2198, 0, x_2197);
lean_ctor_set(x_2198, 1, x_2195);
return x_2198;
}
}
else
{
lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; 
lean_dec(x_2006);
lean_dec(x_2001);
lean_dec(x_2000);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2199 = lean_ctor_get(x_2005, 1);
lean_inc(x_2199);
if (lean_is_exclusive(x_2005)) {
 lean_ctor_release(x_2005, 0);
 lean_ctor_release(x_2005, 1);
 x_2200 = x_2005;
} else {
 lean_dec_ref(x_2005);
 x_2200 = lean_box(0);
}
x_2201 = lean_box(0);
if (lean_is_scalar(x_2200)) {
 x_2202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2202 = x_2200;
}
lean_ctor_set(x_2202, 0, x_2201);
lean_ctor_set(x_2202, 1, x_2199);
return x_2202;
}
}
else
{
lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; uint8_t x_2206; 
lean_dec(x_2001);
lean_dec(x_2000);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2203 = lean_ctor_get(x_2005, 0);
lean_inc(x_2203);
x_2204 = lean_ctor_get(x_2005, 1);
lean_inc(x_2204);
if (lean_is_exclusive(x_2005)) {
 lean_ctor_release(x_2005, 0);
 lean_ctor_release(x_2005, 1);
 x_2205 = x_2005;
} else {
 lean_dec_ref(x_2005);
 x_2205 = lean_box(0);
}
x_2206 = l_Lean_Exception_isInterrupt(x_2203);
if (x_2206 == 0)
{
uint8_t x_2207; 
x_2207 = l_Lean_Exception_isRuntime(x_2203);
if (x_2207 == 0)
{
lean_object* x_2208; lean_object* x_2209; 
lean_dec(x_2203);
x_2208 = lean_box(0);
if (lean_is_scalar(x_2205)) {
 x_2209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2209 = x_2205;
 lean_ctor_set_tag(x_2209, 0);
}
lean_ctor_set(x_2209, 0, x_2208);
lean_ctor_set(x_2209, 1, x_2204);
return x_2209;
}
else
{
lean_object* x_2210; 
if (lean_is_scalar(x_2205)) {
 x_2210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2210 = x_2205;
}
lean_ctor_set(x_2210, 0, x_2203);
lean_ctor_set(x_2210, 1, x_2204);
return x_2210;
}
}
else
{
lean_object* x_2211; 
if (lean_is_scalar(x_2205)) {
 x_2211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2211 = x_2205;
}
lean_ctor_set(x_2211, 0, x_2203);
lean_ctor_set(x_2211, 1, x_2204);
return x_2211;
}
}
}
else
{
lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; uint8_t x_2215; 
lean_dec(x_2001);
lean_dec(x_2000);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2212 = lean_ctor_get(x_2002, 0);
lean_inc(x_2212);
x_2213 = lean_ctor_get(x_2002, 1);
lean_inc(x_2213);
if (lean_is_exclusive(x_2002)) {
 lean_ctor_release(x_2002, 0);
 lean_ctor_release(x_2002, 1);
 x_2214 = x_2002;
} else {
 lean_dec_ref(x_2002);
 x_2214 = lean_box(0);
}
x_2215 = l_Lean_Exception_isInterrupt(x_2212);
if (x_2215 == 0)
{
uint8_t x_2216; 
x_2216 = l_Lean_Exception_isRuntime(x_2212);
if (x_2216 == 0)
{
lean_object* x_2217; lean_object* x_2218; 
lean_dec(x_2212);
x_2217 = lean_box(0);
if (lean_is_scalar(x_2214)) {
 x_2218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2218 = x_2214;
 lean_ctor_set_tag(x_2218, 0);
}
lean_ctor_set(x_2218, 0, x_2217);
lean_ctor_set(x_2218, 1, x_2213);
return x_2218;
}
else
{
lean_object* x_2219; 
if (lean_is_scalar(x_2214)) {
 x_2219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2219 = x_2214;
}
lean_ctor_set(x_2219, 0, x_2212);
lean_ctor_set(x_2219, 1, x_2213);
return x_2219;
}
}
else
{
lean_object* x_2220; 
if (lean_is_scalar(x_2214)) {
 x_2220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2220 = x_2214;
}
lean_ctor_set(x_2220, 0, x_2212);
lean_ctor_set(x_2220, 1, x_2213);
return x_2220;
}
}
}
else
{
lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; 
lean_dec(x_1998);
lean_dec(x_1997);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2221 = lean_ctor_get(x_1995, 1);
lean_inc(x_2221);
if (lean_is_exclusive(x_1995)) {
 lean_ctor_release(x_1995, 0);
 lean_ctor_release(x_1995, 1);
 x_2222 = x_1995;
} else {
 lean_dec_ref(x_1995);
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
}
else
{
lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; 
lean_dec(x_1997);
lean_dec(x_1996);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2225 = lean_ctor_get(x_1995, 1);
lean_inc(x_2225);
if (lean_is_exclusive(x_1995)) {
 lean_ctor_release(x_1995, 0);
 lean_ctor_release(x_1995, 1);
 x_2226 = x_1995;
} else {
 lean_dec_ref(x_1995);
 x_2226 = lean_box(0);
}
x_2227 = lean_box(0);
if (lean_is_scalar(x_2226)) {
 x_2228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2228 = x_2226;
}
lean_ctor_set(x_2228, 0, x_2227);
lean_ctor_set(x_2228, 1, x_2225);
return x_2228;
}
}
else
{
lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; 
lean_dec(x_1996);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2229 = lean_ctor_get(x_1995, 1);
lean_inc(x_2229);
if (lean_is_exclusive(x_1995)) {
 lean_ctor_release(x_1995, 0);
 lean_ctor_release(x_1995, 1);
 x_2230 = x_1995;
} else {
 lean_dec_ref(x_1995);
 x_2230 = lean_box(0);
}
x_2231 = lean_box(0);
if (lean_is_scalar(x_2230)) {
 x_2232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2232 = x_2230;
}
lean_ctor_set(x_2232, 0, x_2231);
lean_ctor_set(x_2232, 1, x_2229);
return x_2232;
}
}
else
{
lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; uint8_t x_2236; 
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2233 = lean_ctor_get(x_1995, 0);
lean_inc(x_2233);
x_2234 = lean_ctor_get(x_1995, 1);
lean_inc(x_2234);
if (lean_is_exclusive(x_1995)) {
 lean_ctor_release(x_1995, 0);
 lean_ctor_release(x_1995, 1);
 x_2235 = x_1995;
} else {
 lean_dec_ref(x_1995);
 x_2235 = lean_box(0);
}
x_2236 = l_Lean_Exception_isInterrupt(x_2233);
if (x_2236 == 0)
{
uint8_t x_2237; 
x_2237 = l_Lean_Exception_isRuntime(x_2233);
if (x_2237 == 0)
{
lean_object* x_2238; lean_object* x_2239; 
lean_dec(x_2233);
x_2238 = lean_box(0);
if (lean_is_scalar(x_2235)) {
 x_2239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2239 = x_2235;
 lean_ctor_set_tag(x_2239, 0);
}
lean_ctor_set(x_2239, 0, x_2238);
lean_ctor_set(x_2239, 1, x_2234);
return x_2239;
}
else
{
lean_object* x_2240; 
if (lean_is_scalar(x_2235)) {
 x_2240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2240 = x_2235;
}
lean_ctor_set(x_2240, 0, x_2233);
lean_ctor_set(x_2240, 1, x_2234);
return x_2240;
}
}
else
{
lean_object* x_2241; 
if (lean_is_scalar(x_2235)) {
 x_2241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2241 = x_2235;
}
lean_ctor_set(x_2241, 0, x_2233);
lean_ctor_set(x_2241, 1, x_2234);
return x_2241;
}
}
}
else
{
lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; uint8_t x_2245; 
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2242 = lean_ctor_get(x_1992, 0);
lean_inc(x_2242);
x_2243 = lean_ctor_get(x_1992, 1);
lean_inc(x_2243);
if (lean_is_exclusive(x_1992)) {
 lean_ctor_release(x_1992, 0);
 lean_ctor_release(x_1992, 1);
 x_2244 = x_1992;
} else {
 lean_dec_ref(x_1992);
 x_2244 = lean_box(0);
}
x_2245 = l_Lean_Exception_isInterrupt(x_2242);
if (x_2245 == 0)
{
uint8_t x_2246; 
x_2246 = l_Lean_Exception_isRuntime(x_2242);
if (x_2246 == 0)
{
lean_object* x_2247; lean_object* x_2248; 
lean_dec(x_2242);
x_2247 = lean_box(0);
if (lean_is_scalar(x_2244)) {
 x_2248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2248 = x_2244;
 lean_ctor_set_tag(x_2248, 0);
}
lean_ctor_set(x_2248, 0, x_2247);
lean_ctor_set(x_2248, 1, x_2243);
return x_2248;
}
else
{
lean_object* x_2249; 
if (lean_is_scalar(x_2244)) {
 x_2249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2249 = x_2244;
}
lean_ctor_set(x_2249, 0, x_2242);
lean_ctor_set(x_2249, 1, x_2243);
return x_2249;
}
}
else
{
lean_object* x_2250; 
if (lean_is_scalar(x_2244)) {
 x_2250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2250 = x_2244;
}
lean_ctor_set(x_2250, 0, x_2242);
lean_ctor_set(x_2250, 1, x_2243);
return x_2250;
}
}
}
}
else
{
lean_object* x_2251; lean_object* x_2252; 
lean_dec(x_38);
lean_dec(x_32);
x_2251 = lean_ctor_get(x_1982, 1);
lean_inc(x_2251);
lean_dec(x_1982);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2252 = l_Lean_Meta_isMonad_x3f(x_51, x_3, x_4, x_5, x_6, x_2251);
if (lean_obj_tag(x_2252) == 0)
{
lean_object* x_2253; 
x_2253 = lean_ctor_get(x_2252, 0);
lean_inc(x_2253);
if (lean_obj_tag(x_2253) == 0)
{
lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; 
lean_dec(x_1981);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_free_object(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2254 = lean_ctor_get(x_2252, 1);
lean_inc(x_2254);
if (lean_is_exclusive(x_2252)) {
 lean_ctor_release(x_2252, 0);
 lean_ctor_release(x_2252, 1);
 x_2255 = x_2252;
} else {
 lean_dec_ref(x_2252);
 x_2255 = lean_box(0);
}
x_2256 = lean_box(0);
if (lean_is_scalar(x_2255)) {
 x_2257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2257 = x_2255;
}
lean_ctor_set(x_2257, 0, x_2256);
lean_ctor_set(x_2257, 1, x_2254);
return x_2257;
}
else
{
lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; 
x_2258 = lean_ctor_get(x_2252, 1);
lean_inc(x_2258);
lean_dec(x_2252);
x_2259 = lean_ctor_get(x_2253, 0);
lean_inc(x_2259);
if (lean_is_exclusive(x_2253)) {
 lean_ctor_release(x_2253, 0);
 x_2260 = x_2253;
} else {
 lean_dec_ref(x_2253);
 x_2260 = lean_box(0);
}
if (lean_is_scalar(x_2260)) {
 x_2261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2261 = x_2260;
}
lean_ctor_set(x_2261, 0, x_1979);
x_2262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2262, 0, x_1980);
lean_ctor_set(x_41, 0, x_52);
x_2263 = lean_box(0);
x_2264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2264, 0, x_2259);
x_2265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2265, 0, x_1);
x_2266 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_2267 = lean_array_push(x_2266, x_2261);
x_2268 = lean_array_push(x_2267, x_2262);
x_2269 = lean_array_push(x_2268, x_41);
x_2270 = lean_array_push(x_2269, x_2263);
x_2271 = lean_array_push(x_2270, x_2264);
x_2272 = lean_array_push(x_2271, x_2265);
x_2273 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2274 = l_Lean_Meta_mkAppOptM(x_2273, x_2272, x_3, x_4, x_5, x_6, x_2258);
if (lean_obj_tag(x_2274) == 0)
{
lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; 
x_2275 = lean_ctor_get(x_2274, 0);
lean_inc(x_2275);
x_2276 = lean_ctor_get(x_2274, 1);
lean_inc(x_2276);
lean_dec(x_2274);
x_2277 = l_Lean_Meta_expandCoe(x_2275, x_3, x_4, x_5, x_6, x_2276);
if (lean_obj_tag(x_2277) == 0)
{
lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; 
x_2278 = lean_ctor_get(x_2277, 0);
lean_inc(x_2278);
x_2279 = lean_ctor_get(x_2277, 1);
lean_inc(x_2279);
lean_dec(x_2277);
x_2280 = lean_box(0);
if (lean_is_scalar(x_1981)) {
 x_2281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2281 = x_1981;
}
lean_ctor_set(x_2281, 0, x_2278);
lean_ctor_set(x_2281, 1, x_2280);
x_17 = x_2281;
x_18 = x_2279;
goto block_30;
}
else
{
lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; uint8_t x_2285; 
lean_dec(x_1981);
x_2282 = lean_ctor_get(x_2277, 0);
lean_inc(x_2282);
x_2283 = lean_ctor_get(x_2277, 1);
lean_inc(x_2283);
if (lean_is_exclusive(x_2277)) {
 lean_ctor_release(x_2277, 0);
 lean_ctor_release(x_2277, 1);
 x_2284 = x_2277;
} else {
 lean_dec_ref(x_2277);
 x_2284 = lean_box(0);
}
x_2285 = l_Lean_Exception_isInterrupt(x_2282);
if (x_2285 == 0)
{
uint8_t x_2286; 
x_2286 = l_Lean_Exception_isRuntime(x_2282);
if (x_2286 == 0)
{
lean_object* x_2287; 
lean_dec(x_2284);
lean_dec(x_2282);
x_2287 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_2287;
x_18 = x_2283;
goto block_30;
}
else
{
lean_object* x_2288; 
if (lean_is_scalar(x_2284)) {
 x_2288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2288 = x_2284;
}
lean_ctor_set(x_2288, 0, x_2282);
lean_ctor_set(x_2288, 1, x_2283);
return x_2288;
}
}
else
{
lean_object* x_2289; 
if (lean_is_scalar(x_2284)) {
 x_2289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2289 = x_2284;
}
lean_ctor_set(x_2289, 0, x_2282);
lean_ctor_set(x_2289, 1, x_2283);
return x_2289;
}
}
}
else
{
lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; uint8_t x_2293; 
lean_dec(x_1981);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2290 = lean_ctor_get(x_2274, 0);
lean_inc(x_2290);
x_2291 = lean_ctor_get(x_2274, 1);
lean_inc(x_2291);
if (lean_is_exclusive(x_2274)) {
 lean_ctor_release(x_2274, 0);
 lean_ctor_release(x_2274, 1);
 x_2292 = x_2274;
} else {
 lean_dec_ref(x_2274);
 x_2292 = lean_box(0);
}
x_2293 = l_Lean_Exception_isInterrupt(x_2290);
if (x_2293 == 0)
{
uint8_t x_2294; 
x_2294 = l_Lean_Exception_isRuntime(x_2290);
if (x_2294 == 0)
{
lean_object* x_2295; 
lean_dec(x_2292);
lean_dec(x_2290);
x_2295 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_2295;
x_18 = x_2291;
goto block_30;
}
else
{
lean_object* x_2296; 
if (lean_is_scalar(x_2292)) {
 x_2296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2296 = x_2292;
}
lean_ctor_set(x_2296, 0, x_2290);
lean_ctor_set(x_2296, 1, x_2291);
return x_2296;
}
}
else
{
lean_object* x_2297; 
if (lean_is_scalar(x_2292)) {
 x_2297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2297 = x_2292;
}
lean_ctor_set(x_2297, 0, x_2290);
lean_ctor_set(x_2297, 1, x_2291);
return x_2297;
}
}
}
}
else
{
lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; 
lean_dec(x_1981);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_free_object(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2298 = lean_ctor_get(x_2252, 0);
lean_inc(x_2298);
x_2299 = lean_ctor_get(x_2252, 1);
lean_inc(x_2299);
if (lean_is_exclusive(x_2252)) {
 lean_ctor_release(x_2252, 0);
 lean_ctor_release(x_2252, 1);
 x_2300 = x_2252;
} else {
 lean_dec_ref(x_2252);
 x_2300 = lean_box(0);
}
if (lean_is_scalar(x_2300)) {
 x_2301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2301 = x_2300;
}
lean_ctor_set(x_2301, 0, x_2298);
lean_ctor_set(x_2301, 1, x_2299);
return x_2301;
}
}
}
else
{
lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; 
lean_dec(x_1981);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_52);
lean_dec(x_51);
lean_free_object(x_41);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2302 = lean_ctor_get(x_1982, 0);
lean_inc(x_2302);
x_2303 = lean_ctor_get(x_1982, 1);
lean_inc(x_2303);
if (lean_is_exclusive(x_1982)) {
 lean_ctor_release(x_1982, 0);
 lean_ctor_release(x_1982, 1);
 x_2304 = x_1982;
} else {
 lean_dec_ref(x_1982);
 x_2304 = lean_box(0);
}
if (lean_is_scalar(x_2304)) {
 x_2305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2305 = x_2304;
}
lean_ctor_set(x_2305, 0, x_2302);
lean_ctor_set(x_2305, 1, x_2303);
return x_2305;
}
}
}
}
else
{
uint8_t x_2306; 
lean_dec(x_52);
lean_dec(x_51);
lean_free_object(x_41);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2306 = !lean_is_exclusive(x_53);
if (x_2306 == 0)
{
return x_53;
}
else
{
lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; 
x_2307 = lean_ctor_get(x_53, 0);
x_2308 = lean_ctor_get(x_53, 1);
lean_inc(x_2308);
lean_inc(x_2307);
lean_dec(x_53);
x_2309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2309, 0, x_2307);
lean_ctor_set(x_2309, 1, x_2308);
return x_2309;
}
}
}
else
{
lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; 
x_2310 = lean_ctor_get(x_41, 0);
lean_inc(x_2310);
lean_dec(x_41);
x_2311 = lean_ctor_get(x_40, 1);
lean_inc(x_2311);
lean_dec(x_40);
x_2312 = lean_ctor_get(x_2310, 0);
lean_inc(x_2312);
x_2313 = lean_ctor_get(x_2310, 1);
lean_inc(x_2313);
lean_dec(x_2310);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_38);
x_2314 = l_Lean_Meta_isTypeApp_x3f(x_38, x_3, x_4, x_5, x_6, x_2311);
if (lean_obj_tag(x_2314) == 0)
{
lean_object* x_2315; 
x_2315 = lean_ctor_get(x_2314, 0);
lean_inc(x_2315);
if (lean_obj_tag(x_2315) == 0)
{
lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; 
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2316 = lean_ctor_get(x_2314, 1);
lean_inc(x_2316);
if (lean_is_exclusive(x_2314)) {
 lean_ctor_release(x_2314, 0);
 lean_ctor_release(x_2314, 1);
 x_2317 = x_2314;
} else {
 lean_dec_ref(x_2314);
 x_2317 = lean_box(0);
}
x_2318 = lean_box(0);
if (lean_is_scalar(x_2317)) {
 x_2319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2319 = x_2317;
}
lean_ctor_set(x_2319, 0, x_2318);
lean_ctor_set(x_2319, 1, x_2316);
return x_2319;
}
else
{
lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; 
x_2320 = lean_ctor_get(x_2315, 0);
lean_inc(x_2320);
if (lean_is_exclusive(x_2315)) {
 lean_ctor_release(x_2315, 0);
 x_2321 = x_2315;
} else {
 lean_dec_ref(x_2315);
 x_2321 = lean_box(0);
}
x_2322 = lean_ctor_get(x_2314, 1);
lean_inc(x_2322);
lean_dec(x_2314);
x_2323 = lean_ctor_get(x_2320, 0);
lean_inc(x_2323);
x_2324 = lean_ctor_get(x_2320, 1);
lean_inc(x_2324);
if (lean_is_exclusive(x_2320)) {
 lean_ctor_release(x_2320, 0);
 lean_ctor_release(x_2320, 1);
 x_2325 = x_2320;
} else {
 lean_dec_ref(x_2320);
 x_2325 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2312);
lean_inc(x_2323);
x_2326 = l_Lean_Meta_isExprDefEq(x_2323, x_2312, x_3, x_4, x_5, x_6, x_2322);
if (lean_obj_tag(x_2326) == 0)
{
lean_object* x_2327; uint8_t x_2328; 
x_2327 = lean_ctor_get(x_2326, 0);
lean_inc(x_2327);
x_2328 = lean_unbox(x_2327);
lean_dec(x_2327);
if (x_2328 == 0)
{
lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; uint8_t x_2333; 
lean_dec(x_2325);
x_2329 = lean_ctor_get(x_2326, 1);
lean_inc(x_2329);
if (lean_is_exclusive(x_2326)) {
 lean_ctor_release(x_2326, 0);
 lean_ctor_release(x_2326, 1);
 x_2330 = x_2326;
} else {
 lean_dec_ref(x_2326);
 x_2330 = lean_box(0);
}
x_2331 = lean_ctor_get(x_5, 2);
lean_inc(x_2331);
x_2332 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_2333 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2331, x_2332);
lean_dec(x_2331);
if (x_2333 == 0)
{
lean_object* x_2334; lean_object* x_2335; 
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2334 = lean_box(0);
if (lean_is_scalar(x_2330)) {
 x_2335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2335 = x_2330;
}
lean_ctor_set(x_2335, 0, x_2334);
lean_ctor_set(x_2335, 1, x_2329);
return x_2335;
}
else
{
lean_object* x_2336; 
lean_dec(x_2330);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2323);
x_2336 = lean_infer_type(x_2323, x_3, x_4, x_5, x_6, x_2329);
if (lean_obj_tag(x_2336) == 0)
{
lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; 
x_2337 = lean_ctor_get(x_2336, 0);
lean_inc(x_2337);
x_2338 = lean_ctor_get(x_2336, 1);
lean_inc(x_2338);
lean_dec(x_2336);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2339 = lean_whnf(x_2337, x_3, x_4, x_5, x_6, x_2338);
if (lean_obj_tag(x_2339) == 0)
{
lean_object* x_2340; 
x_2340 = lean_ctor_get(x_2339, 0);
lean_inc(x_2340);
if (lean_obj_tag(x_2340) == 7)
{
lean_object* x_2341; 
x_2341 = lean_ctor_get(x_2340, 1);
lean_inc(x_2341);
if (lean_obj_tag(x_2341) == 3)
{
lean_object* x_2342; 
x_2342 = lean_ctor_get(x_2340, 2);
lean_inc(x_2342);
lean_dec(x_2340);
if (lean_obj_tag(x_2342) == 3)
{
lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; 
x_2343 = lean_ctor_get(x_2339, 1);
lean_inc(x_2343);
lean_dec(x_2339);
x_2344 = lean_ctor_get(x_2341, 0);
lean_inc(x_2344);
lean_dec(x_2341);
x_2345 = lean_ctor_get(x_2342, 0);
lean_inc(x_2345);
lean_dec(x_2342);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2312);
x_2346 = lean_infer_type(x_2312, x_3, x_4, x_5, x_6, x_2343);
if (lean_obj_tag(x_2346) == 0)
{
lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; 
x_2347 = lean_ctor_get(x_2346, 0);
lean_inc(x_2347);
x_2348 = lean_ctor_get(x_2346, 1);
lean_inc(x_2348);
lean_dec(x_2346);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2349 = lean_whnf(x_2347, x_3, x_4, x_5, x_6, x_2348);
if (lean_obj_tag(x_2349) == 0)
{
lean_object* x_2350; 
x_2350 = lean_ctor_get(x_2349, 0);
lean_inc(x_2350);
if (lean_obj_tag(x_2350) == 7)
{
lean_object* x_2351; 
x_2351 = lean_ctor_get(x_2350, 1);
lean_inc(x_2351);
if (lean_obj_tag(x_2351) == 3)
{
lean_object* x_2352; 
x_2352 = lean_ctor_get(x_2350, 2);
lean_inc(x_2352);
lean_dec(x_2350);
if (lean_obj_tag(x_2352) == 3)
{
lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; lean_object* x_2356; 
x_2353 = lean_ctor_get(x_2349, 1);
lean_inc(x_2353);
lean_dec(x_2349);
x_2354 = lean_ctor_get(x_2351, 0);
lean_inc(x_2354);
lean_dec(x_2351);
x_2355 = lean_ctor_get(x_2352, 0);
lean_inc(x_2355);
lean_dec(x_2352);
x_2356 = l_Lean_Meta_decLevel(x_2344, x_3, x_4, x_5, x_6, x_2353);
if (lean_obj_tag(x_2356) == 0)
{
lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; 
x_2357 = lean_ctor_get(x_2356, 0);
lean_inc(x_2357);
x_2358 = lean_ctor_get(x_2356, 1);
lean_inc(x_2358);
lean_dec(x_2356);
x_2359 = l_Lean_Meta_decLevel(x_2354, x_3, x_4, x_5, x_6, x_2358);
if (lean_obj_tag(x_2359) == 0)
{
lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; uint8_t x_2363; lean_object* x_2364; 
x_2360 = lean_ctor_get(x_2359, 0);
lean_inc(x_2360);
x_2361 = lean_ctor_get(x_2359, 1);
lean_inc(x_2361);
if (lean_is_exclusive(x_2359)) {
 lean_ctor_release(x_2359, 0);
 lean_ctor_release(x_2359, 1);
 x_2362 = x_2359;
} else {
 lean_dec_ref(x_2359);
 x_2362 = lean_box(0);
}
x_2363 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2357);
x_2364 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_2357, x_2360, x_2363, x_3, x_4, x_5, x_6, x_2361);
if (lean_obj_tag(x_2364) == 0)
{
lean_object* x_2365; uint8_t x_2366; 
x_2365 = lean_ctor_get(x_2364, 0);
lean_inc(x_2365);
x_2366 = lean_unbox(x_2365);
lean_dec(x_2365);
if (x_2366 == 0)
{
lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; 
lean_dec(x_2362);
lean_dec(x_2357);
lean_dec(x_2355);
lean_dec(x_2345);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2367 = lean_ctor_get(x_2364, 1);
lean_inc(x_2367);
if (lean_is_exclusive(x_2364)) {
 lean_ctor_release(x_2364, 0);
 lean_ctor_release(x_2364, 1);
 x_2368 = x_2364;
} else {
 lean_dec_ref(x_2364);
 x_2368 = lean_box(0);
}
x_2369 = lean_box(0);
if (lean_is_scalar(x_2368)) {
 x_2370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2370 = x_2368;
}
lean_ctor_set(x_2370, 0, x_2369);
lean_ctor_set(x_2370, 1, x_2367);
return x_2370;
}
else
{
lean_object* x_2371; lean_object* x_2372; 
x_2371 = lean_ctor_get(x_2364, 1);
lean_inc(x_2371);
lean_dec(x_2364);
x_2372 = l_Lean_Meta_decLevel(x_2345, x_3, x_4, x_5, x_6, x_2371);
if (lean_obj_tag(x_2372) == 0)
{
lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; lean_object* x_2376; 
x_2373 = lean_ctor_get(x_2372, 0);
lean_inc(x_2373);
x_2374 = lean_ctor_get(x_2372, 1);
lean_inc(x_2374);
if (lean_is_exclusive(x_2372)) {
 lean_ctor_release(x_2372, 0);
 lean_ctor_release(x_2372, 1);
 x_2375 = x_2372;
} else {
 lean_dec_ref(x_2372);
 x_2375 = lean_box(0);
}
x_2376 = l_Lean_Meta_decLevel(x_2355, x_3, x_4, x_5, x_6, x_2374);
if (lean_obj_tag(x_2376) == 0)
{
lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; 
x_2377 = lean_ctor_get(x_2376, 0);
lean_inc(x_2377);
x_2378 = lean_ctor_get(x_2376, 1);
lean_inc(x_2378);
if (lean_is_exclusive(x_2376)) {
 lean_ctor_release(x_2376, 0);
 lean_ctor_release(x_2376, 1);
 x_2379 = x_2376;
} else {
 lean_dec_ref(x_2376);
 x_2379 = lean_box(0);
}
x_2380 = lean_box(0);
if (lean_is_scalar(x_2379)) {
 x_2381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2381 = x_2379;
 lean_ctor_set_tag(x_2381, 1);
}
lean_ctor_set(x_2381, 0, x_2377);
lean_ctor_set(x_2381, 1, x_2380);
if (lean_is_scalar(x_2375)) {
 x_2382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2382 = x_2375;
 lean_ctor_set_tag(x_2382, 1);
}
lean_ctor_set(x_2382, 0, x_2373);
lean_ctor_set(x_2382, 1, x_2381);
if (lean_is_scalar(x_2362)) {
 x_2383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2383 = x_2362;
 lean_ctor_set_tag(x_2383, 1);
}
lean_ctor_set(x_2383, 0, x_2357);
lean_ctor_set(x_2383, 1, x_2382);
x_2384 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2385 = l_Lean_Expr_const___override(x_2384, x_2383);
x_2386 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_2323);
x_2387 = lean_array_push(x_2386, x_2323);
lean_inc(x_2312);
x_2388 = lean_array_push(x_2387, x_2312);
x_2389 = l_Lean_mkAppN(x_2385, x_2388);
lean_dec(x_2388);
x_2390 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2391 = l_Lean_Meta_trySynthInstance(x_2389, x_2390, x_3, x_4, x_5, x_6, x_2378);
if (lean_obj_tag(x_2391) == 0)
{
lean_object* x_2392; 
x_2392 = lean_ctor_get(x_2391, 0);
lean_inc(x_2392);
if (lean_obj_tag(x_2392) == 1)
{
lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; 
x_2393 = lean_ctor_get(x_2391, 1);
lean_inc(x_2393);
lean_dec(x_2391);
x_2394 = lean_ctor_get(x_2392, 0);
lean_inc(x_2394);
lean_dec(x_2392);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2324);
x_2395 = l_Lean_Meta_getDecLevel(x_2324, x_3, x_4, x_5, x_6, x_2393);
if (lean_obj_tag(x_2395) == 0)
{
lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; 
x_2396 = lean_ctor_get(x_2395, 0);
lean_inc(x_2396);
x_2397 = lean_ctor_get(x_2395, 1);
lean_inc(x_2397);
if (lean_is_exclusive(x_2395)) {
 lean_ctor_release(x_2395, 0);
 lean_ctor_release(x_2395, 1);
 x_2398 = x_2395;
} else {
 lean_dec_ref(x_2395);
 x_2398 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2399 = l_Lean_Meta_getDecLevel(x_38, x_3, x_4, x_5, x_6, x_2397);
if (lean_obj_tag(x_2399) == 0)
{
lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; 
x_2400 = lean_ctor_get(x_2399, 0);
lean_inc(x_2400);
x_2401 = lean_ctor_get(x_2399, 1);
lean_inc(x_2401);
if (lean_is_exclusive(x_2399)) {
 lean_ctor_release(x_2399, 0);
 lean_ctor_release(x_2399, 1);
 x_2402 = x_2399;
} else {
 lean_dec_ref(x_2399);
 x_2402 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_2403 = l_Lean_Meta_getDecLevel(x_32, x_3, x_4, x_5, x_6, x_2401);
if (lean_obj_tag(x_2403) == 0)
{
lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; 
x_2404 = lean_ctor_get(x_2403, 0);
lean_inc(x_2404);
x_2405 = lean_ctor_get(x_2403, 1);
lean_inc(x_2405);
if (lean_is_exclusive(x_2403)) {
 lean_ctor_release(x_2403, 0);
 lean_ctor_release(x_2403, 1);
 x_2406 = x_2403;
} else {
 lean_dec_ref(x_2403);
 x_2406 = lean_box(0);
}
if (lean_is_scalar(x_2406)) {
 x_2407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2407 = x_2406;
 lean_ctor_set_tag(x_2407, 1);
}
lean_ctor_set(x_2407, 0, x_2404);
lean_ctor_set(x_2407, 1, x_2380);
if (lean_is_scalar(x_2402)) {
 x_2408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2408 = x_2402;
 lean_ctor_set_tag(x_2408, 1);
}
lean_ctor_set(x_2408, 0, x_2400);
lean_ctor_set(x_2408, 1, x_2407);
if (lean_is_scalar(x_2398)) {
 x_2409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2409 = x_2398;
 lean_ctor_set_tag(x_2409, 1);
}
lean_ctor_set(x_2409, 0, x_2396);
lean_ctor_set(x_2409, 1, x_2408);
x_2410 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_2409);
x_2411 = l_Lean_Expr_const___override(x_2410, x_2409);
x_2412 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_2323);
x_2413 = lean_array_push(x_2412, x_2323);
lean_inc(x_2312);
x_2414 = lean_array_push(x_2413, x_2312);
lean_inc(x_2394);
x_2415 = lean_array_push(x_2414, x_2394);
lean_inc(x_2324);
x_2416 = lean_array_push(x_2415, x_2324);
lean_inc(x_1);
x_2417 = lean_array_push(x_2416, x_1);
x_2418 = l_Lean_mkAppN(x_2411, x_2417);
lean_dec(x_2417);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2418);
x_2419 = lean_infer_type(x_2418, x_3, x_4, x_5, x_6, x_2405);
if (lean_obj_tag(x_2419) == 0)
{
lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; 
x_2420 = lean_ctor_get(x_2419, 0);
lean_inc(x_2420);
x_2421 = lean_ctor_get(x_2419, 1);
lean_inc(x_2421);
lean_dec(x_2419);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_2422 = l_Lean_Meta_isExprDefEq(x_32, x_2420, x_3, x_4, x_5, x_6, x_2421);
if (lean_obj_tag(x_2422) == 0)
{
lean_object* x_2423; uint8_t x_2424; 
x_2423 = lean_ctor_get(x_2422, 0);
lean_inc(x_2423);
x_2424 = lean_unbox(x_2423);
lean_dec(x_2423);
if (x_2424 == 0)
{
lean_object* x_2425; lean_object* x_2426; 
lean_dec(x_2418);
lean_dec(x_2321);
x_2425 = lean_ctor_get(x_2422, 1);
lean_inc(x_2425);
lean_dec(x_2422);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2312);
x_2426 = l_Lean_Meta_isMonad_x3f(x_2312, x_3, x_4, x_5, x_6, x_2425);
if (lean_obj_tag(x_2426) == 0)
{
lean_object* x_2427; 
x_2427 = lean_ctor_get(x_2426, 0);
lean_inc(x_2427);
if (lean_obj_tag(x_2427) == 0)
{
lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; 
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2428 = lean_ctor_get(x_2426, 1);
lean_inc(x_2428);
if (lean_is_exclusive(x_2426)) {
 lean_ctor_release(x_2426, 0);
 lean_ctor_release(x_2426, 1);
 x_2429 = x_2426;
} else {
 lean_dec_ref(x_2426);
 x_2429 = lean_box(0);
}
if (lean_is_scalar(x_2429)) {
 x_2430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2430 = x_2429;
}
lean_ctor_set(x_2430, 0, x_2390);
lean_ctor_set(x_2430, 1, x_2428);
return x_2430;
}
else
{
lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; 
x_2431 = lean_ctor_get(x_2426, 1);
lean_inc(x_2431);
lean_dec(x_2426);
x_2432 = lean_ctor_get(x_2427, 0);
lean_inc(x_2432);
lean_dec(x_2427);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2324);
x_2433 = l_Lean_Meta_getLevel(x_2324, x_3, x_4, x_5, x_6, x_2431);
if (lean_obj_tag(x_2433) == 0)
{
lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; 
x_2434 = lean_ctor_get(x_2433, 0);
lean_inc(x_2434);
x_2435 = lean_ctor_get(x_2433, 1);
lean_inc(x_2435);
if (lean_is_exclusive(x_2433)) {
 lean_ctor_release(x_2433, 0);
 lean_ctor_release(x_2433, 1);
 x_2436 = x_2433;
} else {
 lean_dec_ref(x_2433);
 x_2436 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2313);
x_2437 = l_Lean_Meta_getLevel(x_2313, x_3, x_4, x_5, x_6, x_2435);
if (lean_obj_tag(x_2437) == 0)
{
lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; uint8_t x_2452; lean_object* x_2453; lean_object* x_2454; 
x_2438 = lean_ctor_get(x_2437, 0);
lean_inc(x_2438);
x_2439 = lean_ctor_get(x_2437, 1);
lean_inc(x_2439);
if (lean_is_exclusive(x_2437)) {
 lean_ctor_release(x_2437, 0);
 lean_ctor_release(x_2437, 1);
 x_2440 = x_2437;
} else {
 lean_dec_ref(x_2437);
 x_2440 = lean_box(0);
}
if (lean_is_scalar(x_2440)) {
 x_2441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2441 = x_2440;
 lean_ctor_set_tag(x_2441, 1);
}
lean_ctor_set(x_2441, 0, x_2438);
lean_ctor_set(x_2441, 1, x_2380);
if (lean_is_scalar(x_2436)) {
 x_2442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2442 = x_2436;
 lean_ctor_set_tag(x_2442, 1);
}
lean_ctor_set(x_2442, 0, x_2434);
lean_ctor_set(x_2442, 1, x_2441);
x_2443 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_2444 = l_Lean_Expr_const___override(x_2443, x_2442);
x_2445 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_2324);
x_2446 = lean_array_push(x_2445, x_2324);
x_2447 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_2448 = lean_array_push(x_2446, x_2447);
lean_inc(x_2313);
x_2449 = lean_array_push(x_2448, x_2313);
x_2450 = l_Lean_mkAppN(x_2444, x_2449);
lean_dec(x_2449);
x_2451 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_2452 = 0;
lean_inc(x_2324);
x_2453 = l_Lean_Expr_forallE___override(x_2451, x_2324, x_2450, x_2452);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2454 = l_Lean_Meta_trySynthInstance(x_2453, x_2390, x_3, x_4, x_5, x_6, x_2439);
if (lean_obj_tag(x_2454) == 0)
{
lean_object* x_2455; 
x_2455 = lean_ctor_get(x_2454, 0);
lean_inc(x_2455);
if (lean_obj_tag(x_2455) == 1)
{
lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; 
x_2456 = lean_ctor_get(x_2454, 1);
lean_inc(x_2456);
lean_dec(x_2454);
x_2457 = lean_ctor_get(x_2455, 0);
lean_inc(x_2457);
lean_dec(x_2455);
x_2458 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_2459 = l_Lean_Expr_const___override(x_2458, x_2409);
x_2460 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_2461 = lean_array_push(x_2460, x_2323);
x_2462 = lean_array_push(x_2461, x_2312);
x_2463 = lean_array_push(x_2462, x_2324);
x_2464 = lean_array_push(x_2463, x_2313);
x_2465 = lean_array_push(x_2464, x_2394);
x_2466 = lean_array_push(x_2465, x_2457);
x_2467 = lean_array_push(x_2466, x_2432);
x_2468 = lean_array_push(x_2467, x_1);
x_2469 = l_Lean_mkAppN(x_2459, x_2468);
lean_dec(x_2468);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2470 = l_Lean_Meta_expandCoe(x_2469, x_3, x_4, x_5, x_6, x_2456);
if (lean_obj_tag(x_2470) == 0)
{
lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; 
x_2471 = lean_ctor_get(x_2470, 0);
lean_inc(x_2471);
x_2472 = lean_ctor_get(x_2470, 1);
lean_inc(x_2472);
lean_dec(x_2470);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2471);
x_2473 = lean_infer_type(x_2471, x_3, x_4, x_5, x_6, x_2472);
if (lean_obj_tag(x_2473) == 0)
{
lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; 
x_2474 = lean_ctor_get(x_2473, 0);
lean_inc(x_2474);
x_2475 = lean_ctor_get(x_2473, 1);
lean_inc(x_2475);
lean_dec(x_2473);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2476 = l_Lean_Meta_isExprDefEq(x_32, x_2474, x_3, x_4, x_5, x_6, x_2475);
if (lean_obj_tag(x_2476) == 0)
{
lean_object* x_2477; uint8_t x_2478; 
x_2477 = lean_ctor_get(x_2476, 0);
lean_inc(x_2477);
x_2478 = lean_unbox(x_2477);
lean_dec(x_2477);
if (x_2478 == 0)
{
lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; 
lean_dec(x_2471);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2479 = lean_ctor_get(x_2476, 1);
lean_inc(x_2479);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2480 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2480 = lean_box(0);
}
if (lean_is_scalar(x_2480)) {
 x_2481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2481 = x_2480;
}
lean_ctor_set(x_2481, 0, x_2390);
lean_ctor_set(x_2481, 1, x_2479);
return x_2481;
}
else
{
lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; 
x_2482 = lean_ctor_get(x_2476, 1);
lean_inc(x_2482);
lean_dec(x_2476);
x_2483 = lean_box(0);
x_2484 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2471, x_2483, x_3, x_4, x_5, x_6, x_2482);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2485 = lean_ctor_get(x_2484, 0);
lean_inc(x_2485);
x_2486 = lean_ctor_get(x_2484, 1);
lean_inc(x_2486);
if (lean_is_exclusive(x_2484)) {
 lean_ctor_release(x_2484, 0);
 lean_ctor_release(x_2484, 1);
 x_2487 = x_2484;
} else {
 lean_dec_ref(x_2484);
 x_2487 = lean_box(0);
}
if (lean_is_scalar(x_2487)) {
 x_2488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2488 = x_2487;
}
lean_ctor_set(x_2488, 0, x_2485);
lean_ctor_set(x_2488, 1, x_2486);
return x_2488;
}
}
else
{
lean_object* x_2489; lean_object* x_2490; 
lean_dec(x_2471);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2489 = lean_ctor_get(x_2476, 0);
lean_inc(x_2489);
x_2490 = lean_ctor_get(x_2476, 1);
lean_inc(x_2490);
lean_dec(x_2476);
x_8 = x_2489;
x_9 = x_2490;
goto block_16;
}
}
else
{
lean_object* x_2491; lean_object* x_2492; 
lean_dec(x_2471);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2491 = lean_ctor_get(x_2473, 0);
lean_inc(x_2491);
x_2492 = lean_ctor_get(x_2473, 1);
lean_inc(x_2492);
lean_dec(x_2473);
x_8 = x_2491;
x_9 = x_2492;
goto block_16;
}
}
else
{
lean_object* x_2493; lean_object* x_2494; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2493 = lean_ctor_get(x_2470, 0);
lean_inc(x_2493);
x_2494 = lean_ctor_get(x_2470, 1);
lean_inc(x_2494);
lean_dec(x_2470);
x_8 = x_2493;
x_9 = x_2494;
goto block_16;
}
}
else
{
lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; 
lean_dec(x_2455);
lean_dec(x_2432);
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2495 = lean_ctor_get(x_2454, 1);
lean_inc(x_2495);
if (lean_is_exclusive(x_2454)) {
 lean_ctor_release(x_2454, 0);
 lean_ctor_release(x_2454, 1);
 x_2496 = x_2454;
} else {
 lean_dec_ref(x_2454);
 x_2496 = lean_box(0);
}
if (lean_is_scalar(x_2496)) {
 x_2497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2497 = x_2496;
}
lean_ctor_set(x_2497, 0, x_2390);
lean_ctor_set(x_2497, 1, x_2495);
return x_2497;
}
}
else
{
lean_object* x_2498; lean_object* x_2499; 
lean_dec(x_2432);
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2498 = lean_ctor_get(x_2454, 0);
lean_inc(x_2498);
x_2499 = lean_ctor_get(x_2454, 1);
lean_inc(x_2499);
lean_dec(x_2454);
x_8 = x_2498;
x_9 = x_2499;
goto block_16;
}
}
else
{
lean_object* x_2500; lean_object* x_2501; 
lean_dec(x_2436);
lean_dec(x_2434);
lean_dec(x_2432);
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2500 = lean_ctor_get(x_2437, 0);
lean_inc(x_2500);
x_2501 = lean_ctor_get(x_2437, 1);
lean_inc(x_2501);
lean_dec(x_2437);
x_8 = x_2500;
x_9 = x_2501;
goto block_16;
}
}
else
{
lean_object* x_2502; lean_object* x_2503; 
lean_dec(x_2432);
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2502 = lean_ctor_get(x_2433, 0);
lean_inc(x_2502);
x_2503 = lean_ctor_get(x_2433, 1);
lean_inc(x_2503);
lean_dec(x_2433);
x_8 = x_2502;
x_9 = x_2503;
goto block_16;
}
}
}
else
{
lean_object* x_2504; lean_object* x_2505; 
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2504 = lean_ctor_get(x_2426, 0);
lean_inc(x_2504);
x_2505 = lean_ctor_get(x_2426, 1);
lean_inc(x_2505);
lean_dec(x_2426);
x_8 = x_2504;
x_9 = x_2505;
goto block_16;
}
}
else
{
lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; 
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2506 = lean_ctor_get(x_2422, 1);
lean_inc(x_2506);
if (lean_is_exclusive(x_2422)) {
 lean_ctor_release(x_2422, 0);
 lean_ctor_release(x_2422, 1);
 x_2507 = x_2422;
} else {
 lean_dec_ref(x_2422);
 x_2507 = lean_box(0);
}
if (lean_is_scalar(x_2321)) {
 x_2508 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2508 = x_2321;
}
lean_ctor_set(x_2508, 0, x_2418);
if (lean_is_scalar(x_2507)) {
 x_2509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2509 = x_2507;
}
lean_ctor_set(x_2509, 0, x_2508);
lean_ctor_set(x_2509, 1, x_2506);
return x_2509;
}
}
else
{
lean_object* x_2510; lean_object* x_2511; 
lean_dec(x_2418);
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2510 = lean_ctor_get(x_2422, 0);
lean_inc(x_2510);
x_2511 = lean_ctor_get(x_2422, 1);
lean_inc(x_2511);
lean_dec(x_2422);
x_8 = x_2510;
x_9 = x_2511;
goto block_16;
}
}
else
{
lean_object* x_2512; lean_object* x_2513; 
lean_dec(x_2418);
lean_dec(x_2409);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2512 = lean_ctor_get(x_2419, 0);
lean_inc(x_2512);
x_2513 = lean_ctor_get(x_2419, 1);
lean_inc(x_2513);
lean_dec(x_2419);
x_8 = x_2512;
x_9 = x_2513;
goto block_16;
}
}
else
{
lean_object* x_2514; lean_object* x_2515; 
lean_dec(x_2402);
lean_dec(x_2400);
lean_dec(x_2398);
lean_dec(x_2396);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2514 = lean_ctor_get(x_2403, 0);
lean_inc(x_2514);
x_2515 = lean_ctor_get(x_2403, 1);
lean_inc(x_2515);
lean_dec(x_2403);
x_8 = x_2514;
x_9 = x_2515;
goto block_16;
}
}
else
{
lean_object* x_2516; lean_object* x_2517; 
lean_dec(x_2398);
lean_dec(x_2396);
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2516 = lean_ctor_get(x_2399, 0);
lean_inc(x_2516);
x_2517 = lean_ctor_get(x_2399, 1);
lean_inc(x_2517);
lean_dec(x_2399);
x_8 = x_2516;
x_9 = x_2517;
goto block_16;
}
}
else
{
lean_object* x_2518; lean_object* x_2519; 
lean_dec(x_2394);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2518 = lean_ctor_get(x_2395, 0);
lean_inc(x_2518);
x_2519 = lean_ctor_get(x_2395, 1);
lean_inc(x_2519);
lean_dec(x_2395);
x_8 = x_2518;
x_9 = x_2519;
goto block_16;
}
}
else
{
lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; 
lean_dec(x_2392);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2520 = lean_ctor_get(x_2391, 1);
lean_inc(x_2520);
if (lean_is_exclusive(x_2391)) {
 lean_ctor_release(x_2391, 0);
 lean_ctor_release(x_2391, 1);
 x_2521 = x_2391;
} else {
 lean_dec_ref(x_2391);
 x_2521 = lean_box(0);
}
if (lean_is_scalar(x_2521)) {
 x_2522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2522 = x_2521;
}
lean_ctor_set(x_2522, 0, x_2390);
lean_ctor_set(x_2522, 1, x_2520);
return x_2522;
}
}
else
{
lean_object* x_2523; lean_object* x_2524; 
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2523 = lean_ctor_get(x_2391, 0);
lean_inc(x_2523);
x_2524 = lean_ctor_get(x_2391, 1);
lean_inc(x_2524);
lean_dec(x_2391);
x_8 = x_2523;
x_9 = x_2524;
goto block_16;
}
}
else
{
lean_object* x_2525; lean_object* x_2526; 
lean_dec(x_2375);
lean_dec(x_2373);
lean_dec(x_2362);
lean_dec(x_2357);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2525 = lean_ctor_get(x_2376, 0);
lean_inc(x_2525);
x_2526 = lean_ctor_get(x_2376, 1);
lean_inc(x_2526);
lean_dec(x_2376);
x_8 = x_2525;
x_9 = x_2526;
goto block_16;
}
}
else
{
lean_object* x_2527; lean_object* x_2528; 
lean_dec(x_2362);
lean_dec(x_2357);
lean_dec(x_2355);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2527 = lean_ctor_get(x_2372, 0);
lean_inc(x_2527);
x_2528 = lean_ctor_get(x_2372, 1);
lean_inc(x_2528);
lean_dec(x_2372);
x_8 = x_2527;
x_9 = x_2528;
goto block_16;
}
}
}
else
{
lean_object* x_2529; lean_object* x_2530; 
lean_dec(x_2362);
lean_dec(x_2357);
lean_dec(x_2355);
lean_dec(x_2345);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2529 = lean_ctor_get(x_2364, 0);
lean_inc(x_2529);
x_2530 = lean_ctor_get(x_2364, 1);
lean_inc(x_2530);
lean_dec(x_2364);
x_8 = x_2529;
x_9 = x_2530;
goto block_16;
}
}
else
{
lean_object* x_2531; lean_object* x_2532; 
lean_dec(x_2357);
lean_dec(x_2355);
lean_dec(x_2345);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2531 = lean_ctor_get(x_2359, 0);
lean_inc(x_2531);
x_2532 = lean_ctor_get(x_2359, 1);
lean_inc(x_2532);
lean_dec(x_2359);
x_8 = x_2531;
x_9 = x_2532;
goto block_16;
}
}
else
{
lean_object* x_2533; lean_object* x_2534; 
lean_dec(x_2355);
lean_dec(x_2354);
lean_dec(x_2345);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2533 = lean_ctor_get(x_2356, 0);
lean_inc(x_2533);
x_2534 = lean_ctor_get(x_2356, 1);
lean_inc(x_2534);
lean_dec(x_2356);
x_8 = x_2533;
x_9 = x_2534;
goto block_16;
}
}
else
{
lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; 
lean_dec(x_2352);
lean_dec(x_2351);
lean_dec(x_2345);
lean_dec(x_2344);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2535 = lean_ctor_get(x_2349, 1);
lean_inc(x_2535);
if (lean_is_exclusive(x_2349)) {
 lean_ctor_release(x_2349, 0);
 lean_ctor_release(x_2349, 1);
 x_2536 = x_2349;
} else {
 lean_dec_ref(x_2349);
 x_2536 = lean_box(0);
}
x_2537 = lean_box(0);
if (lean_is_scalar(x_2536)) {
 x_2538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2538 = x_2536;
}
lean_ctor_set(x_2538, 0, x_2537);
lean_ctor_set(x_2538, 1, x_2535);
return x_2538;
}
}
else
{
lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; 
lean_dec(x_2351);
lean_dec(x_2350);
lean_dec(x_2345);
lean_dec(x_2344);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2539 = lean_ctor_get(x_2349, 1);
lean_inc(x_2539);
if (lean_is_exclusive(x_2349)) {
 lean_ctor_release(x_2349, 0);
 lean_ctor_release(x_2349, 1);
 x_2540 = x_2349;
} else {
 lean_dec_ref(x_2349);
 x_2540 = lean_box(0);
}
x_2541 = lean_box(0);
if (lean_is_scalar(x_2540)) {
 x_2542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2542 = x_2540;
}
lean_ctor_set(x_2542, 0, x_2541);
lean_ctor_set(x_2542, 1, x_2539);
return x_2542;
}
}
else
{
lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; 
lean_dec(x_2350);
lean_dec(x_2345);
lean_dec(x_2344);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2543 = lean_ctor_get(x_2349, 1);
lean_inc(x_2543);
if (lean_is_exclusive(x_2349)) {
 lean_ctor_release(x_2349, 0);
 lean_ctor_release(x_2349, 1);
 x_2544 = x_2349;
} else {
 lean_dec_ref(x_2349);
 x_2544 = lean_box(0);
}
x_2545 = lean_box(0);
if (lean_is_scalar(x_2544)) {
 x_2546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2546 = x_2544;
}
lean_ctor_set(x_2546, 0, x_2545);
lean_ctor_set(x_2546, 1, x_2543);
return x_2546;
}
}
else
{
lean_object* x_2547; lean_object* x_2548; lean_object* x_2549; uint8_t x_2550; 
lean_dec(x_2345);
lean_dec(x_2344);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2547 = lean_ctor_get(x_2349, 0);
lean_inc(x_2547);
x_2548 = lean_ctor_get(x_2349, 1);
lean_inc(x_2548);
if (lean_is_exclusive(x_2349)) {
 lean_ctor_release(x_2349, 0);
 lean_ctor_release(x_2349, 1);
 x_2549 = x_2349;
} else {
 lean_dec_ref(x_2349);
 x_2549 = lean_box(0);
}
x_2550 = l_Lean_Exception_isInterrupt(x_2547);
if (x_2550 == 0)
{
uint8_t x_2551; 
x_2551 = l_Lean_Exception_isRuntime(x_2547);
if (x_2551 == 0)
{
lean_object* x_2552; lean_object* x_2553; 
lean_dec(x_2547);
x_2552 = lean_box(0);
if (lean_is_scalar(x_2549)) {
 x_2553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2553 = x_2549;
 lean_ctor_set_tag(x_2553, 0);
}
lean_ctor_set(x_2553, 0, x_2552);
lean_ctor_set(x_2553, 1, x_2548);
return x_2553;
}
else
{
lean_object* x_2554; 
if (lean_is_scalar(x_2549)) {
 x_2554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2554 = x_2549;
}
lean_ctor_set(x_2554, 0, x_2547);
lean_ctor_set(x_2554, 1, x_2548);
return x_2554;
}
}
else
{
lean_object* x_2555; 
if (lean_is_scalar(x_2549)) {
 x_2555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2555 = x_2549;
}
lean_ctor_set(x_2555, 0, x_2547);
lean_ctor_set(x_2555, 1, x_2548);
return x_2555;
}
}
}
else
{
lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; uint8_t x_2559; 
lean_dec(x_2345);
lean_dec(x_2344);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2556 = lean_ctor_get(x_2346, 0);
lean_inc(x_2556);
x_2557 = lean_ctor_get(x_2346, 1);
lean_inc(x_2557);
if (lean_is_exclusive(x_2346)) {
 lean_ctor_release(x_2346, 0);
 lean_ctor_release(x_2346, 1);
 x_2558 = x_2346;
} else {
 lean_dec_ref(x_2346);
 x_2558 = lean_box(0);
}
x_2559 = l_Lean_Exception_isInterrupt(x_2556);
if (x_2559 == 0)
{
uint8_t x_2560; 
x_2560 = l_Lean_Exception_isRuntime(x_2556);
if (x_2560 == 0)
{
lean_object* x_2561; lean_object* x_2562; 
lean_dec(x_2556);
x_2561 = lean_box(0);
if (lean_is_scalar(x_2558)) {
 x_2562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2562 = x_2558;
 lean_ctor_set_tag(x_2562, 0);
}
lean_ctor_set(x_2562, 0, x_2561);
lean_ctor_set(x_2562, 1, x_2557);
return x_2562;
}
else
{
lean_object* x_2563; 
if (lean_is_scalar(x_2558)) {
 x_2563 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2563 = x_2558;
}
lean_ctor_set(x_2563, 0, x_2556);
lean_ctor_set(x_2563, 1, x_2557);
return x_2563;
}
}
else
{
lean_object* x_2564; 
if (lean_is_scalar(x_2558)) {
 x_2564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2564 = x_2558;
}
lean_ctor_set(x_2564, 0, x_2556);
lean_ctor_set(x_2564, 1, x_2557);
return x_2564;
}
}
}
else
{
lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; 
lean_dec(x_2342);
lean_dec(x_2341);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2565 = lean_ctor_get(x_2339, 1);
lean_inc(x_2565);
if (lean_is_exclusive(x_2339)) {
 lean_ctor_release(x_2339, 0);
 lean_ctor_release(x_2339, 1);
 x_2566 = x_2339;
} else {
 lean_dec_ref(x_2339);
 x_2566 = lean_box(0);
}
x_2567 = lean_box(0);
if (lean_is_scalar(x_2566)) {
 x_2568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2568 = x_2566;
}
lean_ctor_set(x_2568, 0, x_2567);
lean_ctor_set(x_2568, 1, x_2565);
return x_2568;
}
}
else
{
lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; 
lean_dec(x_2341);
lean_dec(x_2340);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2569 = lean_ctor_get(x_2339, 1);
lean_inc(x_2569);
if (lean_is_exclusive(x_2339)) {
 lean_ctor_release(x_2339, 0);
 lean_ctor_release(x_2339, 1);
 x_2570 = x_2339;
} else {
 lean_dec_ref(x_2339);
 x_2570 = lean_box(0);
}
x_2571 = lean_box(0);
if (lean_is_scalar(x_2570)) {
 x_2572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2572 = x_2570;
}
lean_ctor_set(x_2572, 0, x_2571);
lean_ctor_set(x_2572, 1, x_2569);
return x_2572;
}
}
else
{
lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; 
lean_dec(x_2340);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2573 = lean_ctor_get(x_2339, 1);
lean_inc(x_2573);
if (lean_is_exclusive(x_2339)) {
 lean_ctor_release(x_2339, 0);
 lean_ctor_release(x_2339, 1);
 x_2574 = x_2339;
} else {
 lean_dec_ref(x_2339);
 x_2574 = lean_box(0);
}
x_2575 = lean_box(0);
if (lean_is_scalar(x_2574)) {
 x_2576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2576 = x_2574;
}
lean_ctor_set(x_2576, 0, x_2575);
lean_ctor_set(x_2576, 1, x_2573);
return x_2576;
}
}
else
{
lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; uint8_t x_2580; 
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2577 = lean_ctor_get(x_2339, 0);
lean_inc(x_2577);
x_2578 = lean_ctor_get(x_2339, 1);
lean_inc(x_2578);
if (lean_is_exclusive(x_2339)) {
 lean_ctor_release(x_2339, 0);
 lean_ctor_release(x_2339, 1);
 x_2579 = x_2339;
} else {
 lean_dec_ref(x_2339);
 x_2579 = lean_box(0);
}
x_2580 = l_Lean_Exception_isInterrupt(x_2577);
if (x_2580 == 0)
{
uint8_t x_2581; 
x_2581 = l_Lean_Exception_isRuntime(x_2577);
if (x_2581 == 0)
{
lean_object* x_2582; lean_object* x_2583; 
lean_dec(x_2577);
x_2582 = lean_box(0);
if (lean_is_scalar(x_2579)) {
 x_2583 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2583 = x_2579;
 lean_ctor_set_tag(x_2583, 0);
}
lean_ctor_set(x_2583, 0, x_2582);
lean_ctor_set(x_2583, 1, x_2578);
return x_2583;
}
else
{
lean_object* x_2584; 
if (lean_is_scalar(x_2579)) {
 x_2584 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2584 = x_2579;
}
lean_ctor_set(x_2584, 0, x_2577);
lean_ctor_set(x_2584, 1, x_2578);
return x_2584;
}
}
else
{
lean_object* x_2585; 
if (lean_is_scalar(x_2579)) {
 x_2585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2585 = x_2579;
}
lean_ctor_set(x_2585, 0, x_2577);
lean_ctor_set(x_2585, 1, x_2578);
return x_2585;
}
}
}
else
{
lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; uint8_t x_2589; 
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2586 = lean_ctor_get(x_2336, 0);
lean_inc(x_2586);
x_2587 = lean_ctor_get(x_2336, 1);
lean_inc(x_2587);
if (lean_is_exclusive(x_2336)) {
 lean_ctor_release(x_2336, 0);
 lean_ctor_release(x_2336, 1);
 x_2588 = x_2336;
} else {
 lean_dec_ref(x_2336);
 x_2588 = lean_box(0);
}
x_2589 = l_Lean_Exception_isInterrupt(x_2586);
if (x_2589 == 0)
{
uint8_t x_2590; 
x_2590 = l_Lean_Exception_isRuntime(x_2586);
if (x_2590 == 0)
{
lean_object* x_2591; lean_object* x_2592; 
lean_dec(x_2586);
x_2591 = lean_box(0);
if (lean_is_scalar(x_2588)) {
 x_2592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2592 = x_2588;
 lean_ctor_set_tag(x_2592, 0);
}
lean_ctor_set(x_2592, 0, x_2591);
lean_ctor_set(x_2592, 1, x_2587);
return x_2592;
}
else
{
lean_object* x_2593; 
if (lean_is_scalar(x_2588)) {
 x_2593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2593 = x_2588;
}
lean_ctor_set(x_2593, 0, x_2586);
lean_ctor_set(x_2593, 1, x_2587);
return x_2593;
}
}
else
{
lean_object* x_2594; 
if (lean_is_scalar(x_2588)) {
 x_2594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2594 = x_2588;
}
lean_ctor_set(x_2594, 0, x_2586);
lean_ctor_set(x_2594, 1, x_2587);
return x_2594;
}
}
}
}
else
{
lean_object* x_2595; lean_object* x_2596; 
lean_dec(x_38);
lean_dec(x_32);
x_2595 = lean_ctor_get(x_2326, 1);
lean_inc(x_2595);
lean_dec(x_2326);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2596 = l_Lean_Meta_isMonad_x3f(x_2312, x_3, x_4, x_5, x_6, x_2595);
if (lean_obj_tag(x_2596) == 0)
{
lean_object* x_2597; 
x_2597 = lean_ctor_get(x_2596, 0);
lean_inc(x_2597);
if (lean_obj_tag(x_2597) == 0)
{
lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; 
lean_dec(x_2325);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2598 = lean_ctor_get(x_2596, 1);
lean_inc(x_2598);
if (lean_is_exclusive(x_2596)) {
 lean_ctor_release(x_2596, 0);
 lean_ctor_release(x_2596, 1);
 x_2599 = x_2596;
} else {
 lean_dec_ref(x_2596);
 x_2599 = lean_box(0);
}
x_2600 = lean_box(0);
if (lean_is_scalar(x_2599)) {
 x_2601 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2601 = x_2599;
}
lean_ctor_set(x_2601, 0, x_2600);
lean_ctor_set(x_2601, 1, x_2598);
return x_2601;
}
else
{
lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; 
x_2602 = lean_ctor_get(x_2596, 1);
lean_inc(x_2602);
lean_dec(x_2596);
x_2603 = lean_ctor_get(x_2597, 0);
lean_inc(x_2603);
if (lean_is_exclusive(x_2597)) {
 lean_ctor_release(x_2597, 0);
 x_2604 = x_2597;
} else {
 lean_dec_ref(x_2597);
 x_2604 = lean_box(0);
}
if (lean_is_scalar(x_2604)) {
 x_2605 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2605 = x_2604;
}
lean_ctor_set(x_2605, 0, x_2323);
if (lean_is_scalar(x_2321)) {
 x_2606 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2606 = x_2321;
}
lean_ctor_set(x_2606, 0, x_2324);
x_2607 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2607, 0, x_2313);
x_2608 = lean_box(0);
x_2609 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2609, 0, x_2603);
x_2610 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2610, 0, x_1);
x_2611 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_2612 = lean_array_push(x_2611, x_2605);
x_2613 = lean_array_push(x_2612, x_2606);
x_2614 = lean_array_push(x_2613, x_2607);
x_2615 = lean_array_push(x_2614, x_2608);
x_2616 = lean_array_push(x_2615, x_2609);
x_2617 = lean_array_push(x_2616, x_2610);
x_2618 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2619 = l_Lean_Meta_mkAppOptM(x_2618, x_2617, x_3, x_4, x_5, x_6, x_2602);
if (lean_obj_tag(x_2619) == 0)
{
lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; 
x_2620 = lean_ctor_get(x_2619, 0);
lean_inc(x_2620);
x_2621 = lean_ctor_get(x_2619, 1);
lean_inc(x_2621);
lean_dec(x_2619);
x_2622 = l_Lean_Meta_expandCoe(x_2620, x_3, x_4, x_5, x_6, x_2621);
if (lean_obj_tag(x_2622) == 0)
{
lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; 
x_2623 = lean_ctor_get(x_2622, 0);
lean_inc(x_2623);
x_2624 = lean_ctor_get(x_2622, 1);
lean_inc(x_2624);
lean_dec(x_2622);
x_2625 = lean_box(0);
if (lean_is_scalar(x_2325)) {
 x_2626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2626 = x_2325;
}
lean_ctor_set(x_2626, 0, x_2623);
lean_ctor_set(x_2626, 1, x_2625);
x_17 = x_2626;
x_18 = x_2624;
goto block_30;
}
else
{
lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; uint8_t x_2630; 
lean_dec(x_2325);
x_2627 = lean_ctor_get(x_2622, 0);
lean_inc(x_2627);
x_2628 = lean_ctor_get(x_2622, 1);
lean_inc(x_2628);
if (lean_is_exclusive(x_2622)) {
 lean_ctor_release(x_2622, 0);
 lean_ctor_release(x_2622, 1);
 x_2629 = x_2622;
} else {
 lean_dec_ref(x_2622);
 x_2629 = lean_box(0);
}
x_2630 = l_Lean_Exception_isInterrupt(x_2627);
if (x_2630 == 0)
{
uint8_t x_2631; 
x_2631 = l_Lean_Exception_isRuntime(x_2627);
if (x_2631 == 0)
{
lean_object* x_2632; 
lean_dec(x_2629);
lean_dec(x_2627);
x_2632 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_2632;
x_18 = x_2628;
goto block_30;
}
else
{
lean_object* x_2633; 
if (lean_is_scalar(x_2629)) {
 x_2633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2633 = x_2629;
}
lean_ctor_set(x_2633, 0, x_2627);
lean_ctor_set(x_2633, 1, x_2628);
return x_2633;
}
}
else
{
lean_object* x_2634; 
if (lean_is_scalar(x_2629)) {
 x_2634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2634 = x_2629;
}
lean_ctor_set(x_2634, 0, x_2627);
lean_ctor_set(x_2634, 1, x_2628);
return x_2634;
}
}
}
else
{
lean_object* x_2635; lean_object* x_2636; lean_object* x_2637; uint8_t x_2638; 
lean_dec(x_2325);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2635 = lean_ctor_get(x_2619, 0);
lean_inc(x_2635);
x_2636 = lean_ctor_get(x_2619, 1);
lean_inc(x_2636);
if (lean_is_exclusive(x_2619)) {
 lean_ctor_release(x_2619, 0);
 lean_ctor_release(x_2619, 1);
 x_2637 = x_2619;
} else {
 lean_dec_ref(x_2619);
 x_2637 = lean_box(0);
}
x_2638 = l_Lean_Exception_isInterrupt(x_2635);
if (x_2638 == 0)
{
uint8_t x_2639; 
x_2639 = l_Lean_Exception_isRuntime(x_2635);
if (x_2639 == 0)
{
lean_object* x_2640; 
lean_dec(x_2637);
lean_dec(x_2635);
x_2640 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_17 = x_2640;
x_18 = x_2636;
goto block_30;
}
else
{
lean_object* x_2641; 
if (lean_is_scalar(x_2637)) {
 x_2641 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2641 = x_2637;
}
lean_ctor_set(x_2641, 0, x_2635);
lean_ctor_set(x_2641, 1, x_2636);
return x_2641;
}
}
else
{
lean_object* x_2642; 
if (lean_is_scalar(x_2637)) {
 x_2642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2642 = x_2637;
}
lean_ctor_set(x_2642, 0, x_2635);
lean_ctor_set(x_2642, 1, x_2636);
return x_2642;
}
}
}
}
else
{
lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; 
lean_dec(x_2325);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2643 = lean_ctor_get(x_2596, 0);
lean_inc(x_2643);
x_2644 = lean_ctor_get(x_2596, 1);
lean_inc(x_2644);
if (lean_is_exclusive(x_2596)) {
 lean_ctor_release(x_2596, 0);
 lean_ctor_release(x_2596, 1);
 x_2645 = x_2596;
} else {
 lean_dec_ref(x_2596);
 x_2645 = lean_box(0);
}
if (lean_is_scalar(x_2645)) {
 x_2646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2646 = x_2645;
}
lean_ctor_set(x_2646, 0, x_2643);
lean_ctor_set(x_2646, 1, x_2644);
return x_2646;
}
}
}
else
{
lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; 
lean_dec(x_2325);
lean_dec(x_2324);
lean_dec(x_2323);
lean_dec(x_2321);
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2647 = lean_ctor_get(x_2326, 0);
lean_inc(x_2647);
x_2648 = lean_ctor_get(x_2326, 1);
lean_inc(x_2648);
if (lean_is_exclusive(x_2326)) {
 lean_ctor_release(x_2326, 0);
 lean_ctor_release(x_2326, 1);
 x_2649 = x_2326;
} else {
 lean_dec_ref(x_2326);
 x_2649 = lean_box(0);
}
if (lean_is_scalar(x_2649)) {
 x_2650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2650 = x_2649;
}
lean_ctor_set(x_2650, 0, x_2647);
lean_ctor_set(x_2650, 1, x_2648);
return x_2650;
}
}
}
else
{
lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; 
lean_dec(x_2313);
lean_dec(x_2312);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2651 = lean_ctor_get(x_2314, 0);
lean_inc(x_2651);
x_2652 = lean_ctor_get(x_2314, 1);
lean_inc(x_2652);
if (lean_is_exclusive(x_2314)) {
 lean_ctor_release(x_2314, 0);
 lean_ctor_release(x_2314, 1);
 x_2653 = x_2314;
} else {
 lean_dec_ref(x_2314);
 x_2653 = lean_box(0);
}
if (lean_is_scalar(x_2653)) {
 x_2654 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2654 = x_2653;
}
lean_ctor_set(x_2654, 0, x_2651);
lean_ctor_set(x_2654, 1, x_2652);
return x_2654;
}
}
}
}
else
{
uint8_t x_2655; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2655 = !lean_is_exclusive(x_40);
if (x_2655 == 0)
{
return x_40;
}
else
{
lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; 
x_2656 = lean_ctor_get(x_40, 0);
x_2657 = lean_ctor_get(x_40, 1);
lean_inc(x_2657);
lean_inc(x_2656);
lean_dec(x_40);
x_2658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2658, 0, x_2656);
lean_ctor_set(x_2658, 1, x_2657);
return x_2658;
}
}
}
else
{
uint8_t x_2659; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2659 = !lean_is_exclusive(x_34);
if (x_2659 == 0)
{
return x_34;
}
else
{
lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; 
x_2660 = lean_ctor_get(x_34, 0);
x_2661 = lean_ctor_get(x_34, 1);
lean_inc(x_2661);
lean_inc(x_2660);
lean_dec(x_34);
x_2662 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2662, 0, x_2660);
lean_ctor_set(x_2662, 1, x_2661);
return x_2662;
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
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_220_(lean_io_mk_world());
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
l_Lean_Meta_coerceMonadLift_x3f___closed__18 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__18();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__18);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
