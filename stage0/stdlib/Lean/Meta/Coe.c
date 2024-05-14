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
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
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
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__6;
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
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__1;
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
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__5;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__8;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216_(lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__1;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__6;
static lean_object* l_Lean_Meta_expandCoe___lambda__2___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__2;
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
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__4;
lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__3;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("autoLift", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("insert monadic lifts (i.e., `liftM` and coercions) when needed", 62);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_4____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__6;
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__3;
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
lean_object* x_8; lean_object* x_9; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_19, x_3, x_4, x_5, x_6, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_24 = l_Lean_Meta_isTypeApp_x3f(x_16, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
x_37 = l_Lean_Meta_isTypeApp_x3f(x_22, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
lean_inc(x_48);
x_50 = l_Lean_Meta_isExprDefEq(x_48, x_35, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
lean_free_object(x_25);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_50, 1);
x_55 = lean_ctor_get(x_50, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_5, 2);
lean_inc(x_56);
x_57 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_58 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_56, x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_box(0);
lean_ctor_set(x_50, 0, x_59);
return x_50;
}
else
{
lean_object* x_60; 
lean_free_object(x_50);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_48);
x_60 = lean_infer_type(x_48, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_63 = lean_whnf(x_61, x_3, x_4, x_5, x_6, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 7)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 3)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 2);
lean_inc(x_66);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 3)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_70 = lean_infer_type(x_35, x_3, x_4, x_5, x_6, x_67);
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
x_80 = l_Lean_Meta_decLevel(x_68, x_3, x_4, x_5, x_6, x_77);
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
x_83 = l_Lean_Meta_decLevel(x_78, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
x_87 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_81);
x_88 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_81, x_85, x_87, x_3, x_4, x_5, x_6, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
uint8_t x_91; 
lean_free_object(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_88, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_88, 0, x_93);
return x_88;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_88, 1);
lean_inc(x_97);
lean_dec(x_88);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_98 = l_Lean_Meta_decLevel(x_69, x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_102 = l_Lean_Meta_decLevel(x_79, x_3, x_4, x_5, x_6, x_101);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_104 = lean_ctor_get(x_102, 1);
x_105 = lean_box(0);
lean_ctor_set_tag(x_102, 1);
lean_ctor_set(x_102, 1, x_105);
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 1, x_102);
lean_ctor_set_tag(x_83, 1);
lean_ctor_set(x_83, 1, x_98);
lean_ctor_set(x_83, 0, x_81);
x_106 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_107 = l_Lean_Expr_const___override(x_106, x_83);
x_108 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_48);
x_109 = lean_array_push(x_108, x_48);
lean_inc(x_35);
x_110 = lean_array_push(x_109, x_35);
x_111 = l_Lean_mkAppN(x_107, x_110);
x_112 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_113 = l_Lean_Meta_trySynthInstance(x_111, x_112, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 1)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_117 = l_Lean_Meta_getDecLevel(x_49, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_121 = l_Lean_Meta_getDecLevel(x_22, x_3, x_4, x_5, x_6, x_120);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_125 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_124);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_127 = lean_ctor_get(x_125, 1);
lean_ctor_set_tag(x_125, 1);
lean_ctor_set(x_125, 1, x_105);
lean_ctor_set_tag(x_121, 1);
lean_ctor_set(x_121, 1, x_125);
lean_ctor_set_tag(x_117, 1);
lean_ctor_set(x_117, 1, x_121);
x_128 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_117);
x_129 = l_Lean_Expr_const___override(x_128, x_117);
x_130 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_48);
x_131 = lean_array_push(x_130, x_48);
lean_inc(x_35);
x_132 = lean_array_push(x_131, x_35);
lean_inc(x_116);
x_133 = lean_array_push(x_132, x_116);
lean_inc(x_49);
x_134 = lean_array_push(x_133, x_49);
lean_inc(x_1);
x_135 = lean_array_push(x_134, x_1);
x_136 = l_Lean_mkAppN(x_129, x_135);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_136);
x_137 = lean_infer_type(x_136, x_3, x_4, x_5, x_6, x_127);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_140 = l_Lean_Meta_isExprDefEq(x_16, x_138, x_3, x_4, x_5, x_6, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_136);
lean_free_object(x_38);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_144 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_144);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_144, 0);
lean_dec(x_147);
lean_ctor_set(x_144, 0, x_112);
return x_144;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_112);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_dec(x_144);
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
lean_dec(x_145);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_152 = l_Lean_Meta_getLevel(x_49, x_3, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_156 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_155);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; 
x_158 = lean_ctor_get(x_156, 1);
lean_ctor_set_tag(x_156, 1);
lean_ctor_set(x_156, 1, x_105);
lean_ctor_set_tag(x_152, 1);
lean_ctor_set(x_152, 1, x_156);
x_159 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_160 = l_Lean_Expr_const___override(x_159, x_152);
x_161 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_162 = lean_array_push(x_161, x_49);
x_163 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_164 = lean_array_push(x_162, x_163);
lean_inc(x_36);
x_165 = lean_array_push(x_164, x_36);
x_166 = l_Lean_mkAppN(x_160, x_165);
x_167 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_168 = 0;
lean_inc(x_49);
x_169 = l_Lean_Expr_forallE___override(x_167, x_49, x_166, x_168);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_170 = l_Lean_Meta_trySynthInstance(x_169, x_112, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 1)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_175 = l_Lean_Expr_const___override(x_174, x_117);
x_176 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_177 = lean_array_push(x_176, x_48);
x_178 = lean_array_push(x_177, x_35);
x_179 = lean_array_push(x_178, x_49);
x_180 = lean_array_push(x_179, x_36);
x_181 = lean_array_push(x_180, x_116);
x_182 = lean_array_push(x_181, x_173);
x_183 = lean_array_push(x_182, x_151);
x_184 = lean_array_push(x_183, x_1);
x_185 = l_Lean_mkAppN(x_175, x_184);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_186 = l_Lean_Meta_expandCoe(x_185, x_3, x_4, x_5, x_6, x_172);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_187);
x_189 = lean_infer_type(x_187, x_3, x_4, x_5, x_6, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_192 = l_Lean_Meta_isExprDefEq(x_16, x_190, x_3, x_4, x_5, x_6, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
lean_dec(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec(x_187);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_192, 0);
lean_dec(x_196);
lean_ctor_set(x_192, 0, x_112);
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_112);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
x_200 = lean_box(0);
x_201 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_187, x_200, x_3, x_4, x_5, x_6, x_199);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
return x_201;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_201);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_187);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = lean_ctor_get(x_192, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_192, 1);
lean_inc(x_207);
lean_dec(x_192);
x_8 = x_206;
x_9 = x_207;
goto block_14;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_187);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_208 = lean_ctor_get(x_189, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_189, 1);
lean_inc(x_209);
lean_dec(x_189);
x_8 = x_208;
x_9 = x_209;
goto block_14;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_210 = lean_ctor_get(x_186, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_186, 1);
lean_inc(x_211);
lean_dec(x_186);
x_8 = x_210;
x_9 = x_211;
goto block_14;
}
}
else
{
uint8_t x_212; 
lean_dec(x_171);
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_170);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_170, 0);
lean_dec(x_213);
lean_ctor_set(x_170, 0, x_112);
return x_170;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_170, 1);
lean_inc(x_214);
lean_dec(x_170);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_112);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_216 = lean_ctor_get(x_170, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_170, 1);
lean_inc(x_217);
lean_dec(x_170);
x_8 = x_216;
x_9 = x_217;
goto block_14;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
x_218 = lean_ctor_get(x_156, 0);
x_219 = lean_ctor_get(x_156, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_156);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_105);
lean_ctor_set_tag(x_152, 1);
lean_ctor_set(x_152, 1, x_220);
x_221 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_222 = l_Lean_Expr_const___override(x_221, x_152);
x_223 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_224 = lean_array_push(x_223, x_49);
x_225 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_226 = lean_array_push(x_224, x_225);
lean_inc(x_36);
x_227 = lean_array_push(x_226, x_36);
x_228 = l_Lean_mkAppN(x_222, x_227);
x_229 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_230 = 0;
lean_inc(x_49);
x_231 = l_Lean_Expr_forallE___override(x_229, x_49, x_228, x_230);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_232 = l_Lean_Meta_trySynthInstance(x_231, x_112, x_3, x_4, x_5, x_6, x_219);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 1)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_237 = l_Lean_Expr_const___override(x_236, x_117);
x_238 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_239 = lean_array_push(x_238, x_48);
x_240 = lean_array_push(x_239, x_35);
x_241 = lean_array_push(x_240, x_49);
x_242 = lean_array_push(x_241, x_36);
x_243 = lean_array_push(x_242, x_116);
x_244 = lean_array_push(x_243, x_235);
x_245 = lean_array_push(x_244, x_151);
x_246 = lean_array_push(x_245, x_1);
x_247 = l_Lean_mkAppN(x_237, x_246);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_248 = l_Lean_Meta_expandCoe(x_247, x_3, x_4, x_5, x_6, x_234);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_249);
x_251 = lean_infer_type(x_249, x_3, x_4, x_5, x_6, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_254 = l_Lean_Meta_isExprDefEq(x_16, x_252, x_3, x_4, x_5, x_6, x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_249);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_258 = x_254;
} else {
 lean_dec_ref(x_254);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_112);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_254, 1);
lean_inc(x_260);
lean_dec(x_254);
x_261 = lean_box(0);
x_262 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_249, x_261, x_3, x_4, x_5, x_6, x_260);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_249);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_267 = lean_ctor_get(x_254, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_254, 1);
lean_inc(x_268);
lean_dec(x_254);
x_8 = x_267;
x_9 = x_268;
goto block_14;
}
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_249);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_269 = lean_ctor_get(x_251, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_251, 1);
lean_inc(x_270);
lean_dec(x_251);
x_8 = x_269;
x_9 = x_270;
goto block_14;
}
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_271 = lean_ctor_get(x_248, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_248, 1);
lean_inc(x_272);
lean_dec(x_248);
x_8 = x_271;
x_9 = x_272;
goto block_14;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_233);
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_273 = lean_ctor_get(x_232, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_274 = x_232;
} else {
 lean_dec_ref(x_232);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_112);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_276 = lean_ctor_get(x_232, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_232, 1);
lean_inc(x_277);
lean_dec(x_232);
x_8 = x_276;
x_9 = x_277;
goto block_14;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_free_object(x_152);
lean_dec(x_154);
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_278 = lean_ctor_get(x_156, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_156, 1);
lean_inc(x_279);
lean_dec(x_156);
x_8 = x_278;
x_9 = x_279;
goto block_14;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_152, 0);
x_281 = lean_ctor_get(x_152, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_152);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_282 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_285 = x_282;
} else {
 lean_dec_ref(x_282);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
 lean_ctor_set_tag(x_286, 1);
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_105);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_280);
lean_ctor_set(x_287, 1, x_286);
x_288 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_289 = l_Lean_Expr_const___override(x_288, x_287);
x_290 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_291 = lean_array_push(x_290, x_49);
x_292 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_293 = lean_array_push(x_291, x_292);
lean_inc(x_36);
x_294 = lean_array_push(x_293, x_36);
x_295 = l_Lean_mkAppN(x_289, x_294);
x_296 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_297 = 0;
lean_inc(x_49);
x_298 = l_Lean_Expr_forallE___override(x_296, x_49, x_295, x_297);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_299 = l_Lean_Meta_trySynthInstance(x_298, x_112, x_3, x_4, x_5, x_6, x_284);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 1)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_304 = l_Lean_Expr_const___override(x_303, x_117);
x_305 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_306 = lean_array_push(x_305, x_48);
x_307 = lean_array_push(x_306, x_35);
x_308 = lean_array_push(x_307, x_49);
x_309 = lean_array_push(x_308, x_36);
x_310 = lean_array_push(x_309, x_116);
x_311 = lean_array_push(x_310, x_302);
x_312 = lean_array_push(x_311, x_151);
x_313 = lean_array_push(x_312, x_1);
x_314 = l_Lean_mkAppN(x_304, x_313);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_315 = l_Lean_Meta_expandCoe(x_314, x_3, x_4, x_5, x_6, x_301);
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
x_321 = l_Lean_Meta_isExprDefEq(x_16, x_319, x_3, x_4, x_5, x_6, x_320);
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
lean_ctor_set(x_326, 0, x_112);
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
goto block_14;
}
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_316);
lean_dec(x_16);
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
goto block_14;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_16);
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
goto block_14;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_300);
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_340 = lean_ctor_get(x_299, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_341 = x_299;
} else {
 lean_dec_ref(x_299);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_112);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_343 = lean_ctor_get(x_299, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_299, 1);
lean_inc(x_344);
lean_dec(x_299);
x_8 = x_343;
x_9 = x_344;
goto block_14;
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_280);
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_345 = lean_ctor_get(x_282, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_282, 1);
lean_inc(x_346);
lean_dec(x_282);
x_8 = x_345;
x_9 = x_346;
goto block_14;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_347 = lean_ctor_get(x_152, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_152, 1);
lean_inc(x_348);
lean_dec(x_152);
x_8 = x_347;
x_9 = x_348;
goto block_14;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_349 = lean_ctor_get(x_144, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_144, 1);
lean_inc(x_350);
lean_dec(x_144);
x_8 = x_349;
x_9 = x_350;
goto block_14;
}
}
else
{
uint8_t x_351; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_351 = !lean_is_exclusive(x_140);
if (x_351 == 0)
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_140, 0);
lean_dec(x_352);
lean_ctor_set(x_38, 0, x_136);
lean_ctor_set(x_140, 0, x_38);
return x_140;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_140, 1);
lean_inc(x_353);
lean_dec(x_140);
lean_ctor_set(x_38, 0, x_136);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_38);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_136);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_355 = lean_ctor_get(x_140, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_140, 1);
lean_inc(x_356);
lean_dec(x_140);
x_8 = x_355;
x_9 = x_356;
goto block_14;
}
}
else
{
lean_object* x_357; lean_object* x_358; 
lean_dec(x_136);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_357 = lean_ctor_get(x_137, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_137, 1);
lean_inc(x_358);
lean_dec(x_137);
x_8 = x_357;
x_9 = x_358;
goto block_14;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_359 = lean_ctor_get(x_125, 0);
x_360 = lean_ctor_get(x_125, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_125);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_105);
lean_ctor_set_tag(x_121, 1);
lean_ctor_set(x_121, 1, x_361);
lean_ctor_set_tag(x_117, 1);
lean_ctor_set(x_117, 1, x_121);
x_362 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_117);
x_363 = l_Lean_Expr_const___override(x_362, x_117);
x_364 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_48);
x_365 = lean_array_push(x_364, x_48);
lean_inc(x_35);
x_366 = lean_array_push(x_365, x_35);
lean_inc(x_116);
x_367 = lean_array_push(x_366, x_116);
lean_inc(x_49);
x_368 = lean_array_push(x_367, x_49);
lean_inc(x_1);
x_369 = lean_array_push(x_368, x_1);
x_370 = l_Lean_mkAppN(x_363, x_369);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_370);
x_371 = lean_infer_type(x_370, x_3, x_4, x_5, x_6, x_360);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec(x_371);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_374 = l_Lean_Meta_isExprDefEq(x_16, x_372, x_3, x_4, x_5, x_6, x_373);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; uint8_t x_376; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_unbox(x_375);
lean_dec(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_370);
lean_free_object(x_38);
x_377 = lean_ctor_get(x_374, 1);
lean_inc(x_377);
lean_dec(x_374);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_378 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_381 = x_378;
} else {
 lean_dec_ref(x_378);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_112);
lean_ctor_set(x_382, 1, x_380);
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_378, 1);
lean_inc(x_383);
lean_dec(x_378);
x_384 = lean_ctor_get(x_379, 0);
lean_inc(x_384);
lean_dec(x_379);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_385 = l_Lean_Meta_getLevel(x_49, x_3, x_4, x_5, x_6, x_383);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_389 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_387);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
 lean_ctor_set_tag(x_393, 1);
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_105);
if (lean_is_scalar(x_388)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_388;
 lean_ctor_set_tag(x_394, 1);
}
lean_ctor_set(x_394, 0, x_386);
lean_ctor_set(x_394, 1, x_393);
x_395 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_396 = l_Lean_Expr_const___override(x_395, x_394);
x_397 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_398 = lean_array_push(x_397, x_49);
x_399 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_400 = lean_array_push(x_398, x_399);
lean_inc(x_36);
x_401 = lean_array_push(x_400, x_36);
x_402 = l_Lean_mkAppN(x_396, x_401);
x_403 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_404 = 0;
lean_inc(x_49);
x_405 = l_Lean_Expr_forallE___override(x_403, x_49, x_402, x_404);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_406 = l_Lean_Meta_trySynthInstance(x_405, x_112, x_3, x_4, x_5, x_6, x_391);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
if (lean_obj_tag(x_407) == 1)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_ctor_get(x_407, 0);
lean_inc(x_409);
lean_dec(x_407);
x_410 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_411 = l_Lean_Expr_const___override(x_410, x_117);
x_412 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_413 = lean_array_push(x_412, x_48);
x_414 = lean_array_push(x_413, x_35);
x_415 = lean_array_push(x_414, x_49);
x_416 = lean_array_push(x_415, x_36);
x_417 = lean_array_push(x_416, x_116);
x_418 = lean_array_push(x_417, x_409);
x_419 = lean_array_push(x_418, x_384);
x_420 = lean_array_push(x_419, x_1);
x_421 = l_Lean_mkAppN(x_411, x_420);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_422 = l_Lean_Meta_expandCoe(x_421, x_3, x_4, x_5, x_6, x_408);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_423);
x_425 = lean_infer_type(x_423, x_3, x_4, x_5, x_6, x_424);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_428 = l_Lean_Meta_isExprDefEq(x_16, x_426, x_3, x_4, x_5, x_6, x_427);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; uint8_t x_430; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_unbox(x_429);
lean_dec(x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_423);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_432 = x_428;
} else {
 lean_dec_ref(x_428);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_112);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_434 = lean_ctor_get(x_428, 1);
lean_inc(x_434);
lean_dec(x_428);
x_435 = lean_box(0);
x_436 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_423, x_435, x_3, x_4, x_5, x_6, x_434);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_439 = x_436;
} else {
 lean_dec_ref(x_436);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_437);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; 
lean_dec(x_423);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_441 = lean_ctor_get(x_428, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_428, 1);
lean_inc(x_442);
lean_dec(x_428);
x_8 = x_441;
x_9 = x_442;
goto block_14;
}
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec(x_423);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_443 = lean_ctor_get(x_425, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_425, 1);
lean_inc(x_444);
lean_dec(x_425);
x_8 = x_443;
x_9 = x_444;
goto block_14;
}
}
else
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_445 = lean_ctor_get(x_422, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_422, 1);
lean_inc(x_446);
lean_dec(x_422);
x_8 = x_445;
x_9 = x_446;
goto block_14;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_407);
lean_dec(x_384);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_447 = lean_ctor_get(x_406, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_448 = x_406;
} else {
 lean_dec_ref(x_406);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_112);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; 
lean_dec(x_384);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_450 = lean_ctor_get(x_406, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_406, 1);
lean_inc(x_451);
lean_dec(x_406);
x_8 = x_450;
x_9 = x_451;
goto block_14;
}
}
else
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_388);
lean_dec(x_386);
lean_dec(x_384);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_452 = lean_ctor_get(x_389, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_389, 1);
lean_inc(x_453);
lean_dec(x_389);
x_8 = x_452;
x_9 = x_453;
goto block_14;
}
}
else
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_384);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_454 = lean_ctor_get(x_385, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_385, 1);
lean_inc(x_455);
lean_dec(x_385);
x_8 = x_454;
x_9 = x_455;
goto block_14;
}
}
}
else
{
lean_object* x_456; lean_object* x_457; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_456 = lean_ctor_get(x_378, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_378, 1);
lean_inc(x_457);
lean_dec(x_378);
x_8 = x_456;
x_9 = x_457;
goto block_14;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_458 = lean_ctor_get(x_374, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_459 = x_374;
} else {
 lean_dec_ref(x_374);
 x_459 = lean_box(0);
}
lean_ctor_set(x_38, 0, x_370);
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_38);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; 
lean_dec(x_370);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_461 = lean_ctor_get(x_374, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_374, 1);
lean_inc(x_462);
lean_dec(x_374);
x_8 = x_461;
x_9 = x_462;
goto block_14;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_370);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_463 = lean_ctor_get(x_371, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_371, 1);
lean_inc(x_464);
lean_dec(x_371);
x_8 = x_463;
x_9 = x_464;
goto block_14;
}
}
}
else
{
lean_object* x_465; lean_object* x_466; 
lean_free_object(x_121);
lean_dec(x_123);
lean_free_object(x_117);
lean_dec(x_119);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_465 = lean_ctor_get(x_125, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_125, 1);
lean_inc(x_466);
lean_dec(x_125);
x_8 = x_465;
x_9 = x_466;
goto block_14;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_121, 0);
x_468 = lean_ctor_get(x_121, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_121);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_469 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_468);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
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
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 2, 0);
} else {
 x_473 = x_472;
 lean_ctor_set_tag(x_473, 1);
}
lean_ctor_set(x_473, 0, x_470);
lean_ctor_set(x_473, 1, x_105);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_467);
lean_ctor_set(x_474, 1, x_473);
lean_ctor_set_tag(x_117, 1);
lean_ctor_set(x_117, 1, x_474);
x_475 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_117);
x_476 = l_Lean_Expr_const___override(x_475, x_117);
x_477 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_48);
x_478 = lean_array_push(x_477, x_48);
lean_inc(x_35);
x_479 = lean_array_push(x_478, x_35);
lean_inc(x_116);
x_480 = lean_array_push(x_479, x_116);
lean_inc(x_49);
x_481 = lean_array_push(x_480, x_49);
lean_inc(x_1);
x_482 = lean_array_push(x_481, x_1);
x_483 = l_Lean_mkAppN(x_476, x_482);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_483);
x_484 = lean_infer_type(x_483, x_3, x_4, x_5, x_6, x_471);
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
lean_inc(x_16);
x_487 = l_Lean_Meta_isExprDefEq(x_16, x_485, x_3, x_4, x_5, x_6, x_486);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; uint8_t x_489; 
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_unbox(x_488);
lean_dec(x_488);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; 
lean_dec(x_483);
lean_free_object(x_38);
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
lean_dec(x_487);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_491 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_490);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_494 = x_491;
} else {
 lean_dec_ref(x_491);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_112);
lean_ctor_set(x_495, 1, x_493);
return x_495;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_491, 1);
lean_inc(x_496);
lean_dec(x_491);
x_497 = lean_ctor_get(x_492, 0);
lean_inc(x_497);
lean_dec(x_492);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_498 = l_Lean_Meta_getLevel(x_49, x_3, x_4, x_5, x_6, x_496);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_502 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_500);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; lean_object* x_519; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_505 = x_502;
} else {
 lean_dec_ref(x_502);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_506 = x_505;
 lean_ctor_set_tag(x_506, 1);
}
lean_ctor_set(x_506, 0, x_503);
lean_ctor_set(x_506, 1, x_105);
if (lean_is_scalar(x_501)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_501;
 lean_ctor_set_tag(x_507, 1);
}
lean_ctor_set(x_507, 0, x_499);
lean_ctor_set(x_507, 1, x_506);
x_508 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_509 = l_Lean_Expr_const___override(x_508, x_507);
x_510 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_511 = lean_array_push(x_510, x_49);
x_512 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_513 = lean_array_push(x_511, x_512);
lean_inc(x_36);
x_514 = lean_array_push(x_513, x_36);
x_515 = l_Lean_mkAppN(x_509, x_514);
x_516 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_517 = 0;
lean_inc(x_49);
x_518 = l_Lean_Expr_forallE___override(x_516, x_49, x_515, x_517);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_519 = l_Lean_Meta_trySynthInstance(x_518, x_112, x_3, x_4, x_5, x_6, x_504);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
if (lean_obj_tag(x_520) == 1)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = lean_ctor_get(x_520, 0);
lean_inc(x_522);
lean_dec(x_520);
x_523 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_524 = l_Lean_Expr_const___override(x_523, x_117);
x_525 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_526 = lean_array_push(x_525, x_48);
x_527 = lean_array_push(x_526, x_35);
x_528 = lean_array_push(x_527, x_49);
x_529 = lean_array_push(x_528, x_36);
x_530 = lean_array_push(x_529, x_116);
x_531 = lean_array_push(x_530, x_522);
x_532 = lean_array_push(x_531, x_497);
x_533 = lean_array_push(x_532, x_1);
x_534 = l_Lean_mkAppN(x_524, x_533);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_535 = l_Lean_Meta_expandCoe(x_534, x_3, x_4, x_5, x_6, x_521);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_536);
x_538 = lean_infer_type(x_536, x_3, x_4, x_5, x_6, x_537);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_541 = l_Lean_Meta_isExprDefEq(x_16, x_539, x_3, x_4, x_5, x_6, x_540);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; uint8_t x_543; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_unbox(x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_536);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_545 = x_541;
} else {
 lean_dec_ref(x_541);
 x_545 = lean_box(0);
}
if (lean_is_scalar(x_545)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_545;
}
lean_ctor_set(x_546, 0, x_112);
lean_ctor_set(x_546, 1, x_544);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_547 = lean_ctor_get(x_541, 1);
lean_inc(x_547);
lean_dec(x_541);
x_548 = lean_box(0);
x_549 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_536, x_548, x_3, x_4, x_5, x_6, x_547);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_552 = x_549;
} else {
 lean_dec_ref(x_549);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_550);
lean_ctor_set(x_553, 1, x_551);
return x_553;
}
}
else
{
lean_object* x_554; lean_object* x_555; 
lean_dec(x_536);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_554 = lean_ctor_get(x_541, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_541, 1);
lean_inc(x_555);
lean_dec(x_541);
x_8 = x_554;
x_9 = x_555;
goto block_14;
}
}
else
{
lean_object* x_556; lean_object* x_557; 
lean_dec(x_536);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_556 = lean_ctor_get(x_538, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_538, 1);
lean_inc(x_557);
lean_dec(x_538);
x_8 = x_556;
x_9 = x_557;
goto block_14;
}
}
else
{
lean_object* x_558; lean_object* x_559; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_558 = lean_ctor_get(x_535, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_535, 1);
lean_inc(x_559);
lean_dec(x_535);
x_8 = x_558;
x_9 = x_559;
goto block_14;
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_520);
lean_dec(x_497);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_560 = lean_ctor_get(x_519, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_561 = x_519;
} else {
 lean_dec_ref(x_519);
 x_561 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_561;
}
lean_ctor_set(x_562, 0, x_112);
lean_ctor_set(x_562, 1, x_560);
return x_562;
}
}
else
{
lean_object* x_563; lean_object* x_564; 
lean_dec(x_497);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_563 = lean_ctor_get(x_519, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_519, 1);
lean_inc(x_564);
lean_dec(x_519);
x_8 = x_563;
x_9 = x_564;
goto block_14;
}
}
else
{
lean_object* x_565; lean_object* x_566; 
lean_dec(x_501);
lean_dec(x_499);
lean_dec(x_497);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_565 = lean_ctor_get(x_502, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_502, 1);
lean_inc(x_566);
lean_dec(x_502);
x_8 = x_565;
x_9 = x_566;
goto block_14;
}
}
else
{
lean_object* x_567; lean_object* x_568; 
lean_dec(x_497);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_567 = lean_ctor_get(x_498, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_498, 1);
lean_inc(x_568);
lean_dec(x_498);
x_8 = x_567;
x_9 = x_568;
goto block_14;
}
}
}
else
{
lean_object* x_569; lean_object* x_570; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_569 = lean_ctor_get(x_491, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_491, 1);
lean_inc(x_570);
lean_dec(x_491);
x_8 = x_569;
x_9 = x_570;
goto block_14;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_571 = lean_ctor_get(x_487, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_572 = x_487;
} else {
 lean_dec_ref(x_487);
 x_572 = lean_box(0);
}
lean_ctor_set(x_38, 0, x_483);
if (lean_is_scalar(x_572)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_572;
}
lean_ctor_set(x_573, 0, x_38);
lean_ctor_set(x_573, 1, x_571);
return x_573;
}
}
else
{
lean_object* x_574; lean_object* x_575; 
lean_dec(x_483);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_574 = lean_ctor_get(x_487, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_487, 1);
lean_inc(x_575);
lean_dec(x_487);
x_8 = x_574;
x_9 = x_575;
goto block_14;
}
}
else
{
lean_object* x_576; lean_object* x_577; 
lean_dec(x_483);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_576 = lean_ctor_get(x_484, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_484, 1);
lean_inc(x_577);
lean_dec(x_484);
x_8 = x_576;
x_9 = x_577;
goto block_14;
}
}
else
{
lean_object* x_578; lean_object* x_579; 
lean_dec(x_467);
lean_free_object(x_117);
lean_dec(x_119);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_578 = lean_ctor_get(x_469, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_469, 1);
lean_inc(x_579);
lean_dec(x_469);
x_8 = x_578;
x_9 = x_579;
goto block_14;
}
}
}
else
{
lean_object* x_580; lean_object* x_581; 
lean_free_object(x_117);
lean_dec(x_119);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_580 = lean_ctor_get(x_121, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_121, 1);
lean_inc(x_581);
lean_dec(x_121);
x_8 = x_580;
x_9 = x_581;
goto block_14;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_117, 0);
x_583 = lean_ctor_get(x_117, 1);
lean_inc(x_583);
lean_inc(x_582);
lean_dec(x_117);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_584 = l_Lean_Meta_getDecLevel(x_22, x_3, x_4, x_5, x_6, x_583);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_587 = x_584;
} else {
 lean_dec_ref(x_584);
 x_587 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_588 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_586);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_591 = x_588;
} else {
 lean_dec_ref(x_588);
 x_591 = lean_box(0);
}
if (lean_is_scalar(x_591)) {
 x_592 = lean_alloc_ctor(1, 2, 0);
} else {
 x_592 = x_591;
 lean_ctor_set_tag(x_592, 1);
}
lean_ctor_set(x_592, 0, x_589);
lean_ctor_set(x_592, 1, x_105);
if (lean_is_scalar(x_587)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_587;
 lean_ctor_set_tag(x_593, 1);
}
lean_ctor_set(x_593, 0, x_585);
lean_ctor_set(x_593, 1, x_592);
x_594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_594, 0, x_582);
lean_ctor_set(x_594, 1, x_593);
x_595 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_594);
x_596 = l_Lean_Expr_const___override(x_595, x_594);
x_597 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_48);
x_598 = lean_array_push(x_597, x_48);
lean_inc(x_35);
x_599 = lean_array_push(x_598, x_35);
lean_inc(x_116);
x_600 = lean_array_push(x_599, x_116);
lean_inc(x_49);
x_601 = lean_array_push(x_600, x_49);
lean_inc(x_1);
x_602 = lean_array_push(x_601, x_1);
x_603 = l_Lean_mkAppN(x_596, x_602);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_603);
x_604 = lean_infer_type(x_603, x_3, x_4, x_5, x_6, x_590);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec(x_604);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_607 = l_Lean_Meta_isExprDefEq(x_16, x_605, x_3, x_4, x_5, x_6, x_606);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; uint8_t x_609; 
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_unbox(x_608);
lean_dec(x_608);
if (x_609 == 0)
{
lean_object* x_610; lean_object* x_611; 
lean_dec(x_603);
lean_free_object(x_38);
x_610 = lean_ctor_get(x_607, 1);
lean_inc(x_610);
lean_dec(x_607);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_611 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_610);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_614 = x_611;
} else {
 lean_dec_ref(x_611);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_614;
}
lean_ctor_set(x_615, 0, x_112);
lean_ctor_set(x_615, 1, x_613);
return x_615;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_611, 1);
lean_inc(x_616);
lean_dec(x_611);
x_617 = lean_ctor_get(x_612, 0);
lean_inc(x_617);
lean_dec(x_612);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_618 = l_Lean_Meta_getLevel(x_49, x_3, x_4, x_5, x_6, x_616);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_618, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_621 = x_618;
} else {
 lean_dec_ref(x_618);
 x_621 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_622 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_620);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; lean_object* x_638; lean_object* x_639; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_625 = x_622;
} else {
 lean_dec_ref(x_622);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_626 = x_625;
 lean_ctor_set_tag(x_626, 1);
}
lean_ctor_set(x_626, 0, x_623);
lean_ctor_set(x_626, 1, x_105);
if (lean_is_scalar(x_621)) {
 x_627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_627 = x_621;
 lean_ctor_set_tag(x_627, 1);
}
lean_ctor_set(x_627, 0, x_619);
lean_ctor_set(x_627, 1, x_626);
x_628 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_629 = l_Lean_Expr_const___override(x_628, x_627);
x_630 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_631 = lean_array_push(x_630, x_49);
x_632 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_633 = lean_array_push(x_631, x_632);
lean_inc(x_36);
x_634 = lean_array_push(x_633, x_36);
x_635 = l_Lean_mkAppN(x_629, x_634);
x_636 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_637 = 0;
lean_inc(x_49);
x_638 = l_Lean_Expr_forallE___override(x_636, x_49, x_635, x_637);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_639 = l_Lean_Meta_trySynthInstance(x_638, x_112, x_3, x_4, x_5, x_6, x_624);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
if (lean_obj_tag(x_640) == 1)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec(x_639);
x_642 = lean_ctor_get(x_640, 0);
lean_inc(x_642);
lean_dec(x_640);
x_643 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_644 = l_Lean_Expr_const___override(x_643, x_594);
x_645 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_646 = lean_array_push(x_645, x_48);
x_647 = lean_array_push(x_646, x_35);
x_648 = lean_array_push(x_647, x_49);
x_649 = lean_array_push(x_648, x_36);
x_650 = lean_array_push(x_649, x_116);
x_651 = lean_array_push(x_650, x_642);
x_652 = lean_array_push(x_651, x_617);
x_653 = lean_array_push(x_652, x_1);
x_654 = l_Lean_mkAppN(x_644, x_653);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_655 = l_Lean_Meta_expandCoe(x_654, x_3, x_4, x_5, x_6, x_641);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_656);
x_658 = lean_infer_type(x_656, x_3, x_4, x_5, x_6, x_657);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec(x_658);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_661 = l_Lean_Meta_isExprDefEq(x_16, x_659, x_3, x_4, x_5, x_6, x_660);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; uint8_t x_663; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_unbox(x_662);
lean_dec(x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_dec(x_656);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_664 = lean_ctor_get(x_661, 1);
lean_inc(x_664);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_665 = x_661;
} else {
 lean_dec_ref(x_661);
 x_665 = lean_box(0);
}
if (lean_is_scalar(x_665)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_665;
}
lean_ctor_set(x_666, 0, x_112);
lean_ctor_set(x_666, 1, x_664);
return x_666;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_667 = lean_ctor_get(x_661, 1);
lean_inc(x_667);
lean_dec(x_661);
x_668 = lean_box(0);
x_669 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_656, x_668, x_3, x_4, x_5, x_6, x_667);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_672 = x_669;
} else {
 lean_dec_ref(x_669);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_670);
lean_ctor_set(x_673, 1, x_671);
return x_673;
}
}
else
{
lean_object* x_674; lean_object* x_675; 
lean_dec(x_656);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_674 = lean_ctor_get(x_661, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_661, 1);
lean_inc(x_675);
lean_dec(x_661);
x_8 = x_674;
x_9 = x_675;
goto block_14;
}
}
else
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_656);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_676 = lean_ctor_get(x_658, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_658, 1);
lean_inc(x_677);
lean_dec(x_658);
x_8 = x_676;
x_9 = x_677;
goto block_14;
}
}
else
{
lean_object* x_678; lean_object* x_679; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_678 = lean_ctor_get(x_655, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_655, 1);
lean_inc(x_679);
lean_dec(x_655);
x_8 = x_678;
x_9 = x_679;
goto block_14;
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_640);
lean_dec(x_617);
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_680 = lean_ctor_get(x_639, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_681 = x_639;
} else {
 lean_dec_ref(x_639);
 x_681 = lean_box(0);
}
if (lean_is_scalar(x_681)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_681;
}
lean_ctor_set(x_682, 0, x_112);
lean_ctor_set(x_682, 1, x_680);
return x_682;
}
}
else
{
lean_object* x_683; lean_object* x_684; 
lean_dec(x_617);
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_683 = lean_ctor_get(x_639, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_639, 1);
lean_inc(x_684);
lean_dec(x_639);
x_8 = x_683;
x_9 = x_684;
goto block_14;
}
}
else
{
lean_object* x_685; lean_object* x_686; 
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_617);
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_685 = lean_ctor_get(x_622, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_622, 1);
lean_inc(x_686);
lean_dec(x_622);
x_8 = x_685;
x_9 = x_686;
goto block_14;
}
}
else
{
lean_object* x_687; lean_object* x_688; 
lean_dec(x_617);
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_687 = lean_ctor_get(x_618, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_618, 1);
lean_inc(x_688);
lean_dec(x_618);
x_8 = x_687;
x_9 = x_688;
goto block_14;
}
}
}
else
{
lean_object* x_689; lean_object* x_690; 
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_689 = lean_ctor_get(x_611, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_611, 1);
lean_inc(x_690);
lean_dec(x_611);
x_8 = x_689;
x_9 = x_690;
goto block_14;
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_691 = lean_ctor_get(x_607, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_692 = x_607;
} else {
 lean_dec_ref(x_607);
 x_692 = lean_box(0);
}
lean_ctor_set(x_38, 0, x_603);
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(0, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_38);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
else
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_603);
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_694 = lean_ctor_get(x_607, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_607, 1);
lean_inc(x_695);
lean_dec(x_607);
x_8 = x_694;
x_9 = x_695;
goto block_14;
}
}
else
{
lean_object* x_696; lean_object* x_697; 
lean_dec(x_603);
lean_dec(x_594);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_696 = lean_ctor_get(x_604, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_604, 1);
lean_inc(x_697);
lean_dec(x_604);
x_8 = x_696;
x_9 = x_697;
goto block_14;
}
}
else
{
lean_object* x_698; lean_object* x_699; 
lean_dec(x_587);
lean_dec(x_585);
lean_dec(x_582);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_698 = lean_ctor_get(x_588, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_588, 1);
lean_inc(x_699);
lean_dec(x_588);
x_8 = x_698;
x_9 = x_699;
goto block_14;
}
}
else
{
lean_object* x_700; lean_object* x_701; 
lean_dec(x_582);
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_700 = lean_ctor_get(x_584, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_584, 1);
lean_inc(x_701);
lean_dec(x_584);
x_8 = x_700;
x_9 = x_701;
goto block_14;
}
}
}
else
{
lean_object* x_702; lean_object* x_703; 
lean_dec(x_116);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_702 = lean_ctor_get(x_117, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_117, 1);
lean_inc(x_703);
lean_dec(x_117);
x_8 = x_702;
x_9 = x_703;
goto block_14;
}
}
else
{
uint8_t x_704; 
lean_dec(x_114);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_704 = !lean_is_exclusive(x_113);
if (x_704 == 0)
{
lean_object* x_705; 
x_705 = lean_ctor_get(x_113, 0);
lean_dec(x_705);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
else
{
lean_object* x_706; lean_object* x_707; 
x_706 = lean_ctor_get(x_113, 1);
lean_inc(x_706);
lean_dec(x_113);
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_112);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
}
else
{
lean_object* x_708; lean_object* x_709; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_708 = lean_ctor_get(x_113, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_113, 1);
lean_inc(x_709);
lean_dec(x_113);
x_8 = x_708;
x_9 = x_709;
goto block_14;
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_710 = lean_ctor_get(x_102, 0);
x_711 = lean_ctor_get(x_102, 1);
lean_inc(x_711);
lean_inc(x_710);
lean_dec(x_102);
x_712 = lean_box(0);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_710);
lean_ctor_set(x_713, 1, x_712);
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 1, x_713);
lean_ctor_set_tag(x_83, 1);
lean_ctor_set(x_83, 1, x_98);
lean_ctor_set(x_83, 0, x_81);
x_714 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_715 = l_Lean_Expr_const___override(x_714, x_83);
x_716 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_48);
x_717 = lean_array_push(x_716, x_48);
lean_inc(x_35);
x_718 = lean_array_push(x_717, x_35);
x_719 = l_Lean_mkAppN(x_715, x_718);
x_720 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_721 = l_Lean_Meta_trySynthInstance(x_719, x_720, x_3, x_4, x_5, x_6, x_711);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
if (lean_obj_tag(x_722) == 1)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
x_724 = lean_ctor_get(x_722, 0);
lean_inc(x_724);
lean_dec(x_722);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_725 = l_Lean_Meta_getDecLevel(x_49, x_3, x_4, x_5, x_6, x_723);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_728 = x_725;
} else {
 lean_dec_ref(x_725);
 x_728 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_729 = l_Lean_Meta_getDecLevel(x_22, x_3, x_4, x_5, x_6, x_727);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_732 = x_729;
} else {
 lean_dec_ref(x_729);
 x_732 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_733 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_731);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 x_736 = x_733;
} else {
 lean_dec_ref(x_733);
 x_736 = lean_box(0);
}
if (lean_is_scalar(x_736)) {
 x_737 = lean_alloc_ctor(1, 2, 0);
} else {
 x_737 = x_736;
 lean_ctor_set_tag(x_737, 1);
}
lean_ctor_set(x_737, 0, x_734);
lean_ctor_set(x_737, 1, x_712);
if (lean_is_scalar(x_732)) {
 x_738 = lean_alloc_ctor(1, 2, 0);
} else {
 x_738 = x_732;
 lean_ctor_set_tag(x_738, 1);
}
lean_ctor_set(x_738, 0, x_730);
lean_ctor_set(x_738, 1, x_737);
if (lean_is_scalar(x_728)) {
 x_739 = lean_alloc_ctor(1, 2, 0);
} else {
 x_739 = x_728;
 lean_ctor_set_tag(x_739, 1);
}
lean_ctor_set(x_739, 0, x_726);
lean_ctor_set(x_739, 1, x_738);
x_740 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_739);
x_741 = l_Lean_Expr_const___override(x_740, x_739);
x_742 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_48);
x_743 = lean_array_push(x_742, x_48);
lean_inc(x_35);
x_744 = lean_array_push(x_743, x_35);
lean_inc(x_724);
x_745 = lean_array_push(x_744, x_724);
lean_inc(x_49);
x_746 = lean_array_push(x_745, x_49);
lean_inc(x_1);
x_747 = lean_array_push(x_746, x_1);
x_748 = l_Lean_mkAppN(x_741, x_747);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_748);
x_749 = lean_infer_type(x_748, x_3, x_4, x_5, x_6, x_735);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
lean_dec(x_749);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_752 = l_Lean_Meta_isExprDefEq(x_16, x_750, x_3, x_4, x_5, x_6, x_751);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; uint8_t x_754; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_unbox(x_753);
lean_dec(x_753);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; 
lean_dec(x_748);
lean_free_object(x_38);
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
lean_dec(x_752);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_756 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_755);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 x_759 = x_756;
} else {
 lean_dec_ref(x_756);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_720);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_761 = lean_ctor_get(x_756, 1);
lean_inc(x_761);
lean_dec(x_756);
x_762 = lean_ctor_get(x_757, 0);
lean_inc(x_762);
lean_dec(x_757);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_763 = l_Lean_Meta_getLevel(x_49, x_3, x_4, x_5, x_6, x_761);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_763, 1);
lean_inc(x_765);
if (lean_is_exclusive(x_763)) {
 lean_ctor_release(x_763, 0);
 lean_ctor_release(x_763, 1);
 x_766 = x_763;
} else {
 lean_dec_ref(x_763);
 x_766 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_767 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_765);
if (lean_obj_tag(x_767) == 0)
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; uint8_t x_782; lean_object* x_783; lean_object* x_784; 
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_767, 1);
lean_inc(x_769);
if (lean_is_exclusive(x_767)) {
 lean_ctor_release(x_767, 0);
 lean_ctor_release(x_767, 1);
 x_770 = x_767;
} else {
 lean_dec_ref(x_767);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(1, 2, 0);
} else {
 x_771 = x_770;
 lean_ctor_set_tag(x_771, 1);
}
lean_ctor_set(x_771, 0, x_768);
lean_ctor_set(x_771, 1, x_712);
if (lean_is_scalar(x_766)) {
 x_772 = lean_alloc_ctor(1, 2, 0);
} else {
 x_772 = x_766;
 lean_ctor_set_tag(x_772, 1);
}
lean_ctor_set(x_772, 0, x_764);
lean_ctor_set(x_772, 1, x_771);
x_773 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_774 = l_Lean_Expr_const___override(x_773, x_772);
x_775 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_776 = lean_array_push(x_775, x_49);
x_777 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_778 = lean_array_push(x_776, x_777);
lean_inc(x_36);
x_779 = lean_array_push(x_778, x_36);
x_780 = l_Lean_mkAppN(x_774, x_779);
x_781 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_782 = 0;
lean_inc(x_49);
x_783 = l_Lean_Expr_forallE___override(x_781, x_49, x_780, x_782);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_784 = l_Lean_Meta_trySynthInstance(x_783, x_720, x_3, x_4, x_5, x_6, x_769);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; 
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
if (lean_obj_tag(x_785) == 1)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
lean_dec(x_784);
x_787 = lean_ctor_get(x_785, 0);
lean_inc(x_787);
lean_dec(x_785);
x_788 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_789 = l_Lean_Expr_const___override(x_788, x_739);
x_790 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_791 = lean_array_push(x_790, x_48);
x_792 = lean_array_push(x_791, x_35);
x_793 = lean_array_push(x_792, x_49);
x_794 = lean_array_push(x_793, x_36);
x_795 = lean_array_push(x_794, x_724);
x_796 = lean_array_push(x_795, x_787);
x_797 = lean_array_push(x_796, x_762);
x_798 = lean_array_push(x_797, x_1);
x_799 = l_Lean_mkAppN(x_789, x_798);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_800 = l_Lean_Meta_expandCoe(x_799, x_3, x_4, x_5, x_6, x_786);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_800, 1);
lean_inc(x_802);
lean_dec(x_800);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_801);
x_803 = lean_infer_type(x_801, x_3, x_4, x_5, x_6, x_802);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
lean_dec(x_803);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_806 = l_Lean_Meta_isExprDefEq(x_16, x_804, x_3, x_4, x_5, x_6, x_805);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; uint8_t x_808; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_unbox(x_807);
lean_dec(x_807);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_801);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_809 = lean_ctor_get(x_806, 1);
lean_inc(x_809);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_810 = x_806;
} else {
 lean_dec_ref(x_806);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(0, 2, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_720);
lean_ctor_set(x_811, 1, x_809);
return x_811;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_812 = lean_ctor_get(x_806, 1);
lean_inc(x_812);
lean_dec(x_806);
x_813 = lean_box(0);
x_814 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_801, x_813, x_3, x_4, x_5, x_6, x_812);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_814, 1);
lean_inc(x_816);
if (lean_is_exclusive(x_814)) {
 lean_ctor_release(x_814, 0);
 lean_ctor_release(x_814, 1);
 x_817 = x_814;
} else {
 lean_dec_ref(x_814);
 x_817 = lean_box(0);
}
if (lean_is_scalar(x_817)) {
 x_818 = lean_alloc_ctor(0, 2, 0);
} else {
 x_818 = x_817;
}
lean_ctor_set(x_818, 0, x_815);
lean_ctor_set(x_818, 1, x_816);
return x_818;
}
}
else
{
lean_object* x_819; lean_object* x_820; 
lean_dec(x_801);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_819 = lean_ctor_get(x_806, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_806, 1);
lean_inc(x_820);
lean_dec(x_806);
x_8 = x_819;
x_9 = x_820;
goto block_14;
}
}
else
{
lean_object* x_821; lean_object* x_822; 
lean_dec(x_801);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_821 = lean_ctor_get(x_803, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_803, 1);
lean_inc(x_822);
lean_dec(x_803);
x_8 = x_821;
x_9 = x_822;
goto block_14;
}
}
else
{
lean_object* x_823; lean_object* x_824; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_823 = lean_ctor_get(x_800, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_800, 1);
lean_inc(x_824);
lean_dec(x_800);
x_8 = x_823;
x_9 = x_824;
goto block_14;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_dec(x_785);
lean_dec(x_762);
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_825 = lean_ctor_get(x_784, 1);
lean_inc(x_825);
if (lean_is_exclusive(x_784)) {
 lean_ctor_release(x_784, 0);
 lean_ctor_release(x_784, 1);
 x_826 = x_784;
} else {
 lean_dec_ref(x_784);
 x_826 = lean_box(0);
}
if (lean_is_scalar(x_826)) {
 x_827 = lean_alloc_ctor(0, 2, 0);
} else {
 x_827 = x_826;
}
lean_ctor_set(x_827, 0, x_720);
lean_ctor_set(x_827, 1, x_825);
return x_827;
}
}
else
{
lean_object* x_828; lean_object* x_829; 
lean_dec(x_762);
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_828 = lean_ctor_get(x_784, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_784, 1);
lean_inc(x_829);
lean_dec(x_784);
x_8 = x_828;
x_9 = x_829;
goto block_14;
}
}
else
{
lean_object* x_830; lean_object* x_831; 
lean_dec(x_766);
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_830 = lean_ctor_get(x_767, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_767, 1);
lean_inc(x_831);
lean_dec(x_767);
x_8 = x_830;
x_9 = x_831;
goto block_14;
}
}
else
{
lean_object* x_832; lean_object* x_833; 
lean_dec(x_762);
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_832 = lean_ctor_get(x_763, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_763, 1);
lean_inc(x_833);
lean_dec(x_763);
x_8 = x_832;
x_9 = x_833;
goto block_14;
}
}
}
else
{
lean_object* x_834; lean_object* x_835; 
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_834 = lean_ctor_get(x_756, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_756, 1);
lean_inc(x_835);
lean_dec(x_756);
x_8 = x_834;
x_9 = x_835;
goto block_14;
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_836 = lean_ctor_get(x_752, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_837 = x_752;
} else {
 lean_dec_ref(x_752);
 x_837 = lean_box(0);
}
lean_ctor_set(x_38, 0, x_748);
if (lean_is_scalar(x_837)) {
 x_838 = lean_alloc_ctor(0, 2, 0);
} else {
 x_838 = x_837;
}
lean_ctor_set(x_838, 0, x_38);
lean_ctor_set(x_838, 1, x_836);
return x_838;
}
}
else
{
lean_object* x_839; lean_object* x_840; 
lean_dec(x_748);
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_839 = lean_ctor_get(x_752, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_752, 1);
lean_inc(x_840);
lean_dec(x_752);
x_8 = x_839;
x_9 = x_840;
goto block_14;
}
}
else
{
lean_object* x_841; lean_object* x_842; 
lean_dec(x_748);
lean_dec(x_739);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_841 = lean_ctor_get(x_749, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_749, 1);
lean_inc(x_842);
lean_dec(x_749);
x_8 = x_841;
x_9 = x_842;
goto block_14;
}
}
else
{
lean_object* x_843; lean_object* x_844; 
lean_dec(x_732);
lean_dec(x_730);
lean_dec(x_728);
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_843 = lean_ctor_get(x_733, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_733, 1);
lean_inc(x_844);
lean_dec(x_733);
x_8 = x_843;
x_9 = x_844;
goto block_14;
}
}
else
{
lean_object* x_845; lean_object* x_846; 
lean_dec(x_728);
lean_dec(x_726);
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_845 = lean_ctor_get(x_729, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_729, 1);
lean_inc(x_846);
lean_dec(x_729);
x_8 = x_845;
x_9 = x_846;
goto block_14;
}
}
else
{
lean_object* x_847; lean_object* x_848; 
lean_dec(x_724);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_847 = lean_ctor_get(x_725, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_725, 1);
lean_inc(x_848);
lean_dec(x_725);
x_8 = x_847;
x_9 = x_848;
goto block_14;
}
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_722);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_849 = lean_ctor_get(x_721, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_850 = x_721;
} else {
 lean_dec_ref(x_721);
 x_850 = lean_box(0);
}
if (lean_is_scalar(x_850)) {
 x_851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_851 = x_850;
}
lean_ctor_set(x_851, 0, x_720);
lean_ctor_set(x_851, 1, x_849);
return x_851;
}
}
else
{
lean_object* x_852; lean_object* x_853; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_852 = lean_ctor_get(x_721, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_721, 1);
lean_inc(x_853);
lean_dec(x_721);
x_8 = x_852;
x_9 = x_853;
goto block_14;
}
}
}
else
{
lean_object* x_854; lean_object* x_855; 
lean_free_object(x_98);
lean_dec(x_100);
lean_free_object(x_83);
lean_dec(x_81);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_854 = lean_ctor_get(x_102, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_102, 1);
lean_inc(x_855);
lean_dec(x_102);
x_8 = x_854;
x_9 = x_855;
goto block_14;
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_856 = lean_ctor_get(x_98, 0);
x_857 = lean_ctor_get(x_98, 1);
lean_inc(x_857);
lean_inc(x_856);
lean_dec(x_98);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_858 = l_Lean_Meta_decLevel(x_79, x_3, x_4, x_5, x_6, x_857);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_861 = x_858;
} else {
 lean_dec_ref(x_858);
 x_861 = lean_box(0);
}
x_862 = lean_box(0);
if (lean_is_scalar(x_861)) {
 x_863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_863 = x_861;
 lean_ctor_set_tag(x_863, 1);
}
lean_ctor_set(x_863, 0, x_859);
lean_ctor_set(x_863, 1, x_862);
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_856);
lean_ctor_set(x_864, 1, x_863);
lean_ctor_set_tag(x_83, 1);
lean_ctor_set(x_83, 1, x_864);
lean_ctor_set(x_83, 0, x_81);
x_865 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_866 = l_Lean_Expr_const___override(x_865, x_83);
x_867 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_48);
x_868 = lean_array_push(x_867, x_48);
lean_inc(x_35);
x_869 = lean_array_push(x_868, x_35);
x_870 = l_Lean_mkAppN(x_866, x_869);
x_871 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_872 = l_Lean_Meta_trySynthInstance(x_870, x_871, x_3, x_4, x_5, x_6, x_860);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
if (lean_obj_tag(x_873) == 1)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_ctor_get(x_873, 0);
lean_inc(x_875);
lean_dec(x_873);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_876 = l_Lean_Meta_getDecLevel(x_49, x_3, x_4, x_5, x_6, x_874);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_879 = x_876;
} else {
 lean_dec_ref(x_876);
 x_879 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_880 = l_Lean_Meta_getDecLevel(x_22, x_3, x_4, x_5, x_6, x_878);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_883 = x_880;
} else {
 lean_dec_ref(x_880);
 x_883 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_884 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_882);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 x_887 = x_884;
} else {
 lean_dec_ref(x_884);
 x_887 = lean_box(0);
}
if (lean_is_scalar(x_887)) {
 x_888 = lean_alloc_ctor(1, 2, 0);
} else {
 x_888 = x_887;
 lean_ctor_set_tag(x_888, 1);
}
lean_ctor_set(x_888, 0, x_885);
lean_ctor_set(x_888, 1, x_862);
if (lean_is_scalar(x_883)) {
 x_889 = lean_alloc_ctor(1, 2, 0);
} else {
 x_889 = x_883;
 lean_ctor_set_tag(x_889, 1);
}
lean_ctor_set(x_889, 0, x_881);
lean_ctor_set(x_889, 1, x_888);
if (lean_is_scalar(x_879)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_879;
 lean_ctor_set_tag(x_890, 1);
}
lean_ctor_set(x_890, 0, x_877);
lean_ctor_set(x_890, 1, x_889);
x_891 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_890);
x_892 = l_Lean_Expr_const___override(x_891, x_890);
x_893 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_48);
x_894 = lean_array_push(x_893, x_48);
lean_inc(x_35);
x_895 = lean_array_push(x_894, x_35);
lean_inc(x_875);
x_896 = lean_array_push(x_895, x_875);
lean_inc(x_49);
x_897 = lean_array_push(x_896, x_49);
lean_inc(x_1);
x_898 = lean_array_push(x_897, x_1);
x_899 = l_Lean_mkAppN(x_892, x_898);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_899);
x_900 = lean_infer_type(x_899, x_3, x_4, x_5, x_6, x_886);
if (lean_obj_tag(x_900) == 0)
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_901 = lean_ctor_get(x_900, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_900, 1);
lean_inc(x_902);
lean_dec(x_900);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_903 = l_Lean_Meta_isExprDefEq(x_16, x_901, x_3, x_4, x_5, x_6, x_902);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; uint8_t x_905; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
x_905 = lean_unbox(x_904);
lean_dec(x_904);
if (x_905 == 0)
{
lean_object* x_906; lean_object* x_907; 
lean_dec(x_899);
lean_free_object(x_38);
x_906 = lean_ctor_get(x_903, 1);
lean_inc(x_906);
lean_dec(x_903);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_907 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_906);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; 
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_909 = lean_ctor_get(x_907, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 x_910 = x_907;
} else {
 lean_dec_ref(x_907);
 x_910 = lean_box(0);
}
if (lean_is_scalar(x_910)) {
 x_911 = lean_alloc_ctor(0, 2, 0);
} else {
 x_911 = x_910;
}
lean_ctor_set(x_911, 0, x_871);
lean_ctor_set(x_911, 1, x_909);
return x_911;
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_912 = lean_ctor_get(x_907, 1);
lean_inc(x_912);
lean_dec(x_907);
x_913 = lean_ctor_get(x_908, 0);
lean_inc(x_913);
lean_dec(x_908);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_914 = l_Lean_Meta_getLevel(x_49, x_3, x_4, x_5, x_6, x_912);
if (lean_obj_tag(x_914) == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_917 = x_914;
} else {
 lean_dec_ref(x_914);
 x_917 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_918 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_916);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; uint8_t x_933; lean_object* x_934; lean_object* x_935; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 lean_ctor_release(x_918, 1);
 x_921 = x_918;
} else {
 lean_dec_ref(x_918);
 x_921 = lean_box(0);
}
if (lean_is_scalar(x_921)) {
 x_922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_922 = x_921;
 lean_ctor_set_tag(x_922, 1);
}
lean_ctor_set(x_922, 0, x_919);
lean_ctor_set(x_922, 1, x_862);
if (lean_is_scalar(x_917)) {
 x_923 = lean_alloc_ctor(1, 2, 0);
} else {
 x_923 = x_917;
 lean_ctor_set_tag(x_923, 1);
}
lean_ctor_set(x_923, 0, x_915);
lean_ctor_set(x_923, 1, x_922);
x_924 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_925 = l_Lean_Expr_const___override(x_924, x_923);
x_926 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_927 = lean_array_push(x_926, x_49);
x_928 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_929 = lean_array_push(x_927, x_928);
lean_inc(x_36);
x_930 = lean_array_push(x_929, x_36);
x_931 = l_Lean_mkAppN(x_925, x_930);
x_932 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_933 = 0;
lean_inc(x_49);
x_934 = l_Lean_Expr_forallE___override(x_932, x_49, x_931, x_933);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_935 = l_Lean_Meta_trySynthInstance(x_934, x_871, x_3, x_4, x_5, x_6, x_920);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
if (lean_obj_tag(x_936) == 1)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
lean_dec(x_935);
x_938 = lean_ctor_get(x_936, 0);
lean_inc(x_938);
lean_dec(x_936);
x_939 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_940 = l_Lean_Expr_const___override(x_939, x_890);
x_941 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_942 = lean_array_push(x_941, x_48);
x_943 = lean_array_push(x_942, x_35);
x_944 = lean_array_push(x_943, x_49);
x_945 = lean_array_push(x_944, x_36);
x_946 = lean_array_push(x_945, x_875);
x_947 = lean_array_push(x_946, x_938);
x_948 = lean_array_push(x_947, x_913);
x_949 = lean_array_push(x_948, x_1);
x_950 = l_Lean_mkAppN(x_940, x_949);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_951 = l_Lean_Meta_expandCoe(x_950, x_3, x_4, x_5, x_6, x_937);
if (lean_obj_tag(x_951) == 0)
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_952 = lean_ctor_get(x_951, 0);
lean_inc(x_952);
x_953 = lean_ctor_get(x_951, 1);
lean_inc(x_953);
lean_dec(x_951);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_952);
x_954 = lean_infer_type(x_952, x_3, x_4, x_5, x_6, x_953);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec(x_954);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_957 = l_Lean_Meta_isExprDefEq(x_16, x_955, x_3, x_4, x_5, x_6, x_956);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; uint8_t x_959; 
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
x_959 = lean_unbox(x_958);
lean_dec(x_958);
if (x_959 == 0)
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_952);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_960 = lean_ctor_get(x_957, 1);
lean_inc(x_960);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_961 = x_957;
} else {
 lean_dec_ref(x_957);
 x_961 = lean_box(0);
}
if (lean_is_scalar(x_961)) {
 x_962 = lean_alloc_ctor(0, 2, 0);
} else {
 x_962 = x_961;
}
lean_ctor_set(x_962, 0, x_871);
lean_ctor_set(x_962, 1, x_960);
return x_962;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_963 = lean_ctor_get(x_957, 1);
lean_inc(x_963);
lean_dec(x_957);
x_964 = lean_box(0);
x_965 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_952, x_964, x_3, x_4, x_5, x_6, x_963);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_968)) {
 x_969 = lean_alloc_ctor(0, 2, 0);
} else {
 x_969 = x_968;
}
lean_ctor_set(x_969, 0, x_966);
lean_ctor_set(x_969, 1, x_967);
return x_969;
}
}
else
{
lean_object* x_970; lean_object* x_971; 
lean_dec(x_952);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_970 = lean_ctor_get(x_957, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_957, 1);
lean_inc(x_971);
lean_dec(x_957);
x_8 = x_970;
x_9 = x_971;
goto block_14;
}
}
else
{
lean_object* x_972; lean_object* x_973; 
lean_dec(x_952);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_972 = lean_ctor_get(x_954, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_954, 1);
lean_inc(x_973);
lean_dec(x_954);
x_8 = x_972;
x_9 = x_973;
goto block_14;
}
}
else
{
lean_object* x_974; lean_object* x_975; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_974 = lean_ctor_get(x_951, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_951, 1);
lean_inc(x_975);
lean_dec(x_951);
x_8 = x_974;
x_9 = x_975;
goto block_14;
}
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; 
lean_dec(x_936);
lean_dec(x_913);
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_976 = lean_ctor_get(x_935, 1);
lean_inc(x_976);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_977 = x_935;
} else {
 lean_dec_ref(x_935);
 x_977 = lean_box(0);
}
if (lean_is_scalar(x_977)) {
 x_978 = lean_alloc_ctor(0, 2, 0);
} else {
 x_978 = x_977;
}
lean_ctor_set(x_978, 0, x_871);
lean_ctor_set(x_978, 1, x_976);
return x_978;
}
}
else
{
lean_object* x_979; lean_object* x_980; 
lean_dec(x_913);
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_979 = lean_ctor_get(x_935, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_935, 1);
lean_inc(x_980);
lean_dec(x_935);
x_8 = x_979;
x_9 = x_980;
goto block_14;
}
}
else
{
lean_object* x_981; lean_object* x_982; 
lean_dec(x_917);
lean_dec(x_915);
lean_dec(x_913);
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_981 = lean_ctor_get(x_918, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_918, 1);
lean_inc(x_982);
lean_dec(x_918);
x_8 = x_981;
x_9 = x_982;
goto block_14;
}
}
else
{
lean_object* x_983; lean_object* x_984; 
lean_dec(x_913);
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_983 = lean_ctor_get(x_914, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_914, 1);
lean_inc(x_984);
lean_dec(x_914);
x_8 = x_983;
x_9 = x_984;
goto block_14;
}
}
}
else
{
lean_object* x_985; lean_object* x_986; 
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_985 = lean_ctor_get(x_907, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_907, 1);
lean_inc(x_986);
lean_dec(x_907);
x_8 = x_985;
x_9 = x_986;
goto block_14;
}
}
else
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_987 = lean_ctor_get(x_903, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 lean_ctor_release(x_903, 1);
 x_988 = x_903;
} else {
 lean_dec_ref(x_903);
 x_988 = lean_box(0);
}
lean_ctor_set(x_38, 0, x_899);
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_38);
lean_ctor_set(x_989, 1, x_987);
return x_989;
}
}
else
{
lean_object* x_990; lean_object* x_991; 
lean_dec(x_899);
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_990 = lean_ctor_get(x_903, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_903, 1);
lean_inc(x_991);
lean_dec(x_903);
x_8 = x_990;
x_9 = x_991;
goto block_14;
}
}
else
{
lean_object* x_992; lean_object* x_993; 
lean_dec(x_899);
lean_dec(x_890);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_992 = lean_ctor_get(x_900, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_900, 1);
lean_inc(x_993);
lean_dec(x_900);
x_8 = x_992;
x_9 = x_993;
goto block_14;
}
}
else
{
lean_object* x_994; lean_object* x_995; 
lean_dec(x_883);
lean_dec(x_881);
lean_dec(x_879);
lean_dec(x_877);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_994 = lean_ctor_get(x_884, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_884, 1);
lean_inc(x_995);
lean_dec(x_884);
x_8 = x_994;
x_9 = x_995;
goto block_14;
}
}
else
{
lean_object* x_996; lean_object* x_997; 
lean_dec(x_879);
lean_dec(x_877);
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_996 = lean_ctor_get(x_880, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_880, 1);
lean_inc(x_997);
lean_dec(x_880);
x_8 = x_996;
x_9 = x_997;
goto block_14;
}
}
else
{
lean_object* x_998; lean_object* x_999; 
lean_dec(x_875);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_998 = lean_ctor_get(x_876, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_876, 1);
lean_inc(x_999);
lean_dec(x_876);
x_8 = x_998;
x_9 = x_999;
goto block_14;
}
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_873);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1000 = lean_ctor_get(x_872, 1);
lean_inc(x_1000);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_1001 = x_872;
} else {
 lean_dec_ref(x_872);
 x_1001 = lean_box(0);
}
if (lean_is_scalar(x_1001)) {
 x_1002 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1002 = x_1001;
}
lean_ctor_set(x_1002, 0, x_871);
lean_ctor_set(x_1002, 1, x_1000);
return x_1002;
}
}
else
{
lean_object* x_1003; lean_object* x_1004; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1003 = lean_ctor_get(x_872, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_872, 1);
lean_inc(x_1004);
lean_dec(x_872);
x_8 = x_1003;
x_9 = x_1004;
goto block_14;
}
}
else
{
lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_856);
lean_free_object(x_83);
lean_dec(x_81);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1005 = lean_ctor_get(x_858, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_858, 1);
lean_inc(x_1006);
lean_dec(x_858);
x_8 = x_1005;
x_9 = x_1006;
goto block_14;
}
}
}
else
{
lean_object* x_1007; lean_object* x_1008; 
lean_free_object(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1007 = lean_ctor_get(x_98, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_98, 1);
lean_inc(x_1008);
lean_dec(x_98);
x_8 = x_1007;
x_9 = x_1008;
goto block_14;
}
}
}
else
{
lean_object* x_1009; lean_object* x_1010; 
lean_free_object(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1009 = lean_ctor_get(x_88, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_88, 1);
lean_inc(x_1010);
lean_dec(x_88);
x_8 = x_1009;
x_9 = x_1010;
goto block_14;
}
}
else
{
lean_object* x_1011; lean_object* x_1012; uint8_t x_1013; lean_object* x_1014; 
x_1011 = lean_ctor_get(x_83, 0);
x_1012 = lean_ctor_get(x_83, 1);
lean_inc(x_1012);
lean_inc(x_1011);
lean_dec(x_83);
x_1013 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_81);
x_1014 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_81, x_1011, x_1013, x_3, x_4, x_5, x_6, x_1012);
if (lean_obj_tag(x_1014) == 0)
{
lean_object* x_1015; uint8_t x_1016; 
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
x_1016 = lean_unbox(x_1015);
lean_dec(x_1015);
if (x_1016 == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1017 = lean_ctor_get(x_1014, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1018 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1018 = lean_box(0);
}
x_1019 = lean_box(0);
if (lean_is_scalar(x_1018)) {
 x_1020 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1020 = x_1018;
}
lean_ctor_set(x_1020, 0, x_1019);
lean_ctor_set(x_1020, 1, x_1017);
return x_1020;
}
else
{
lean_object* x_1021; lean_object* x_1022; 
x_1021 = lean_ctor_get(x_1014, 1);
lean_inc(x_1021);
lean_dec(x_1014);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1022 = l_Lean_Meta_decLevel(x_69, x_3, x_4, x_5, x_6, x_1021);
if (lean_obj_tag(x_1022) == 0)
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1025 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1025 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1026 = l_Lean_Meta_decLevel(x_79, x_3, x_4, x_5, x_6, x_1024);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1027 = lean_ctor_get(x_1026, 0);
lean_inc(x_1027);
x_1028 = lean_ctor_get(x_1026, 1);
lean_inc(x_1028);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1029 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1029 = lean_box(0);
}
x_1030 = lean_box(0);
if (lean_is_scalar(x_1029)) {
 x_1031 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1031 = x_1029;
 lean_ctor_set_tag(x_1031, 1);
}
lean_ctor_set(x_1031, 0, x_1027);
lean_ctor_set(x_1031, 1, x_1030);
if (lean_is_scalar(x_1025)) {
 x_1032 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1032 = x_1025;
 lean_ctor_set_tag(x_1032, 1);
}
lean_ctor_set(x_1032, 0, x_1023);
lean_ctor_set(x_1032, 1, x_1031);
x_1033 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1033, 0, x_81);
lean_ctor_set(x_1033, 1, x_1032);
x_1034 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1035 = l_Lean_Expr_const___override(x_1034, x_1033);
x_1036 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_48);
x_1037 = lean_array_push(x_1036, x_48);
lean_inc(x_35);
x_1038 = lean_array_push(x_1037, x_35);
x_1039 = l_Lean_mkAppN(x_1035, x_1038);
x_1040 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1041 = l_Lean_Meta_trySynthInstance(x_1039, x_1040, x_3, x_4, x_5, x_6, x_1028);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; 
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
if (lean_obj_tag(x_1042) == 1)
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
lean_dec(x_1041);
x_1044 = lean_ctor_get(x_1042, 0);
lean_inc(x_1044);
lean_dec(x_1042);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_1045 = l_Lean_Meta_getDecLevel(x_49, x_3, x_4, x_5, x_6, x_1043);
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1045, 1);
lean_inc(x_1047);
if (lean_is_exclusive(x_1045)) {
 lean_ctor_release(x_1045, 0);
 lean_ctor_release(x_1045, 1);
 x_1048 = x_1045;
} else {
 lean_dec_ref(x_1045);
 x_1048 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1049 = l_Lean_Meta_getDecLevel(x_22, x_3, x_4, x_5, x_6, x_1047);
if (lean_obj_tag(x_1049) == 0)
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
if (lean_is_exclusive(x_1049)) {
 lean_ctor_release(x_1049, 0);
 lean_ctor_release(x_1049, 1);
 x_1052 = x_1049;
} else {
 lean_dec_ref(x_1049);
 x_1052 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_1053 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_1051);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1053, 1);
lean_inc(x_1055);
if (lean_is_exclusive(x_1053)) {
 lean_ctor_release(x_1053, 0);
 lean_ctor_release(x_1053, 1);
 x_1056 = x_1053;
} else {
 lean_dec_ref(x_1053);
 x_1056 = lean_box(0);
}
if (lean_is_scalar(x_1056)) {
 x_1057 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1057 = x_1056;
 lean_ctor_set_tag(x_1057, 1);
}
lean_ctor_set(x_1057, 0, x_1054);
lean_ctor_set(x_1057, 1, x_1030);
if (lean_is_scalar(x_1052)) {
 x_1058 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1058 = x_1052;
 lean_ctor_set_tag(x_1058, 1);
}
lean_ctor_set(x_1058, 0, x_1050);
lean_ctor_set(x_1058, 1, x_1057);
if (lean_is_scalar(x_1048)) {
 x_1059 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1059 = x_1048;
 lean_ctor_set_tag(x_1059, 1);
}
lean_ctor_set(x_1059, 0, x_1046);
lean_ctor_set(x_1059, 1, x_1058);
x_1060 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_1059);
x_1061 = l_Lean_Expr_const___override(x_1060, x_1059);
x_1062 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_48);
x_1063 = lean_array_push(x_1062, x_48);
lean_inc(x_35);
x_1064 = lean_array_push(x_1063, x_35);
lean_inc(x_1044);
x_1065 = lean_array_push(x_1064, x_1044);
lean_inc(x_49);
x_1066 = lean_array_push(x_1065, x_49);
lean_inc(x_1);
x_1067 = lean_array_push(x_1066, x_1);
x_1068 = l_Lean_mkAppN(x_1061, x_1067);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1068);
x_1069 = lean_infer_type(x_1068, x_3, x_4, x_5, x_6, x_1055);
if (lean_obj_tag(x_1069) == 0)
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1070 = lean_ctor_get(x_1069, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1069, 1);
lean_inc(x_1071);
lean_dec(x_1069);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_1072 = l_Lean_Meta_isExprDefEq(x_16, x_1070, x_3, x_4, x_5, x_6, x_1071);
if (lean_obj_tag(x_1072) == 0)
{
lean_object* x_1073; uint8_t x_1074; 
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_unbox(x_1073);
lean_dec(x_1073);
if (x_1074 == 0)
{
lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_1068);
lean_free_object(x_38);
x_1075 = lean_ctor_get(x_1072, 1);
lean_inc(x_1075);
lean_dec(x_1072);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_1076 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_1075);
if (lean_obj_tag(x_1076) == 0)
{
lean_object* x_1077; 
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1078 = lean_ctor_get(x_1076, 1);
lean_inc(x_1078);
if (lean_is_exclusive(x_1076)) {
 lean_ctor_release(x_1076, 0);
 lean_ctor_release(x_1076, 1);
 x_1079 = x_1076;
} else {
 lean_dec_ref(x_1076);
 x_1079 = lean_box(0);
}
if (lean_is_scalar(x_1079)) {
 x_1080 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1080 = x_1079;
}
lean_ctor_set(x_1080, 0, x_1040);
lean_ctor_set(x_1080, 1, x_1078);
return x_1080;
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1076, 1);
lean_inc(x_1081);
lean_dec(x_1076);
x_1082 = lean_ctor_get(x_1077, 0);
lean_inc(x_1082);
lean_dec(x_1077);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_1083 = l_Lean_Meta_getLevel(x_49, x_3, x_4, x_5, x_6, x_1081);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
if (lean_is_exclusive(x_1083)) {
 lean_ctor_release(x_1083, 0);
 lean_ctor_release(x_1083, 1);
 x_1086 = x_1083;
} else {
 lean_dec_ref(x_1083);
 x_1086 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_1087 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_1085);
if (lean_obj_tag(x_1087) == 0)
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; uint8_t x_1102; lean_object* x_1103; lean_object* x_1104; 
x_1088 = lean_ctor_get(x_1087, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1087, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_1087)) {
 lean_ctor_release(x_1087, 0);
 lean_ctor_release(x_1087, 1);
 x_1090 = x_1087;
} else {
 lean_dec_ref(x_1087);
 x_1090 = lean_box(0);
}
if (lean_is_scalar(x_1090)) {
 x_1091 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1091 = x_1090;
 lean_ctor_set_tag(x_1091, 1);
}
lean_ctor_set(x_1091, 0, x_1088);
lean_ctor_set(x_1091, 1, x_1030);
if (lean_is_scalar(x_1086)) {
 x_1092 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1092 = x_1086;
 lean_ctor_set_tag(x_1092, 1);
}
lean_ctor_set(x_1092, 0, x_1084);
lean_ctor_set(x_1092, 1, x_1091);
x_1093 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1094 = l_Lean_Expr_const___override(x_1093, x_1092);
x_1095 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_1096 = lean_array_push(x_1095, x_49);
x_1097 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_1098 = lean_array_push(x_1096, x_1097);
lean_inc(x_36);
x_1099 = lean_array_push(x_1098, x_36);
x_1100 = l_Lean_mkAppN(x_1094, x_1099);
x_1101 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_1102 = 0;
lean_inc(x_49);
x_1103 = l_Lean_Expr_forallE___override(x_1101, x_49, x_1100, x_1102);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1104 = l_Lean_Meta_trySynthInstance(x_1103, x_1040, x_3, x_4, x_5, x_6, x_1089);
if (lean_obj_tag(x_1104) == 0)
{
lean_object* x_1105; 
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
if (lean_obj_tag(x_1105) == 1)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
x_1106 = lean_ctor_get(x_1104, 1);
lean_inc(x_1106);
lean_dec(x_1104);
x_1107 = lean_ctor_get(x_1105, 0);
lean_inc(x_1107);
lean_dec(x_1105);
x_1108 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_1109 = l_Lean_Expr_const___override(x_1108, x_1059);
x_1110 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_1111 = lean_array_push(x_1110, x_48);
x_1112 = lean_array_push(x_1111, x_35);
x_1113 = lean_array_push(x_1112, x_49);
x_1114 = lean_array_push(x_1113, x_36);
x_1115 = lean_array_push(x_1114, x_1044);
x_1116 = lean_array_push(x_1115, x_1107);
x_1117 = lean_array_push(x_1116, x_1082);
x_1118 = lean_array_push(x_1117, x_1);
x_1119 = l_Lean_mkAppN(x_1109, x_1118);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1120 = l_Lean_Meta_expandCoe(x_1119, x_3, x_4, x_5, x_6, x_1106);
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1120, 0);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_1120, 1);
lean_inc(x_1122);
lean_dec(x_1120);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1121);
x_1123 = lean_infer_type(x_1121, x_3, x_4, x_5, x_6, x_1122);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1123, 1);
lean_inc(x_1125);
lean_dec(x_1123);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1126 = l_Lean_Meta_isExprDefEq(x_16, x_1124, x_3, x_4, x_5, x_6, x_1125);
if (lean_obj_tag(x_1126) == 0)
{
lean_object* x_1127; uint8_t x_1128; 
x_1127 = lean_ctor_get(x_1126, 0);
lean_inc(x_1127);
x_1128 = lean_unbox(x_1127);
lean_dec(x_1127);
if (x_1128 == 0)
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
lean_dec(x_1121);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1129 = lean_ctor_get(x_1126, 1);
lean_inc(x_1129);
if (lean_is_exclusive(x_1126)) {
 lean_ctor_release(x_1126, 0);
 lean_ctor_release(x_1126, 1);
 x_1130 = x_1126;
} else {
 lean_dec_ref(x_1126);
 x_1130 = lean_box(0);
}
if (lean_is_scalar(x_1130)) {
 x_1131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1131 = x_1130;
}
lean_ctor_set(x_1131, 0, x_1040);
lean_ctor_set(x_1131, 1, x_1129);
return x_1131;
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
x_1132 = lean_ctor_get(x_1126, 1);
lean_inc(x_1132);
lean_dec(x_1126);
x_1133 = lean_box(0);
x_1134 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1121, x_1133, x_3, x_4, x_5, x_6, x_1132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1135 = lean_ctor_get(x_1134, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1134, 1);
lean_inc(x_1136);
if (lean_is_exclusive(x_1134)) {
 lean_ctor_release(x_1134, 0);
 lean_ctor_release(x_1134, 1);
 x_1137 = x_1134;
} else {
 lean_dec_ref(x_1134);
 x_1137 = lean_box(0);
}
if (lean_is_scalar(x_1137)) {
 x_1138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1138 = x_1137;
}
lean_ctor_set(x_1138, 0, x_1135);
lean_ctor_set(x_1138, 1, x_1136);
return x_1138;
}
}
else
{
lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1121);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1139 = lean_ctor_get(x_1126, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1126, 1);
lean_inc(x_1140);
lean_dec(x_1126);
x_8 = x_1139;
x_9 = x_1140;
goto block_14;
}
}
else
{
lean_object* x_1141; lean_object* x_1142; 
lean_dec(x_1121);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1141 = lean_ctor_get(x_1123, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1123, 1);
lean_inc(x_1142);
lean_dec(x_1123);
x_8 = x_1141;
x_9 = x_1142;
goto block_14;
}
}
else
{
lean_object* x_1143; lean_object* x_1144; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1143 = lean_ctor_get(x_1120, 0);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1120, 1);
lean_inc(x_1144);
lean_dec(x_1120);
x_8 = x_1143;
x_9 = x_1144;
goto block_14;
}
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
lean_dec(x_1105);
lean_dec(x_1082);
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1145 = lean_ctor_get(x_1104, 1);
lean_inc(x_1145);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1146 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1146 = lean_box(0);
}
if (lean_is_scalar(x_1146)) {
 x_1147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1147 = x_1146;
}
lean_ctor_set(x_1147, 0, x_1040);
lean_ctor_set(x_1147, 1, x_1145);
return x_1147;
}
}
else
{
lean_object* x_1148; lean_object* x_1149; 
lean_dec(x_1082);
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1148 = lean_ctor_get(x_1104, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1104, 1);
lean_inc(x_1149);
lean_dec(x_1104);
x_8 = x_1148;
x_9 = x_1149;
goto block_14;
}
}
else
{
lean_object* x_1150; lean_object* x_1151; 
lean_dec(x_1086);
lean_dec(x_1084);
lean_dec(x_1082);
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1150 = lean_ctor_get(x_1087, 0);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1087, 1);
lean_inc(x_1151);
lean_dec(x_1087);
x_8 = x_1150;
x_9 = x_1151;
goto block_14;
}
}
else
{
lean_object* x_1152; lean_object* x_1153; 
lean_dec(x_1082);
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1152 = lean_ctor_get(x_1083, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1083, 1);
lean_inc(x_1153);
lean_dec(x_1083);
x_8 = x_1152;
x_9 = x_1153;
goto block_14;
}
}
}
else
{
lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1154 = lean_ctor_get(x_1076, 0);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1076, 1);
lean_inc(x_1155);
lean_dec(x_1076);
x_8 = x_1154;
x_9 = x_1155;
goto block_14;
}
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1156 = lean_ctor_get(x_1072, 1);
lean_inc(x_1156);
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 lean_ctor_release(x_1072, 1);
 x_1157 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1157 = lean_box(0);
}
lean_ctor_set(x_38, 0, x_1068);
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_38);
lean_ctor_set(x_1158, 1, x_1156);
return x_1158;
}
}
else
{
lean_object* x_1159; lean_object* x_1160; 
lean_dec(x_1068);
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1159 = lean_ctor_get(x_1072, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1072, 1);
lean_inc(x_1160);
lean_dec(x_1072);
x_8 = x_1159;
x_9 = x_1160;
goto block_14;
}
}
else
{
lean_object* x_1161; lean_object* x_1162; 
lean_dec(x_1068);
lean_dec(x_1059);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1161 = lean_ctor_get(x_1069, 0);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1069, 1);
lean_inc(x_1162);
lean_dec(x_1069);
x_8 = x_1161;
x_9 = x_1162;
goto block_14;
}
}
else
{
lean_object* x_1163; lean_object* x_1164; 
lean_dec(x_1052);
lean_dec(x_1050);
lean_dec(x_1048);
lean_dec(x_1046);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1163 = lean_ctor_get(x_1053, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1053, 1);
lean_inc(x_1164);
lean_dec(x_1053);
x_8 = x_1163;
x_9 = x_1164;
goto block_14;
}
}
else
{
lean_object* x_1165; lean_object* x_1166; 
lean_dec(x_1048);
lean_dec(x_1046);
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1165 = lean_ctor_get(x_1049, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1049, 1);
lean_inc(x_1166);
lean_dec(x_1049);
x_8 = x_1165;
x_9 = x_1166;
goto block_14;
}
}
else
{
lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1044);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1167 = lean_ctor_get(x_1045, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1045, 1);
lean_inc(x_1168);
lean_dec(x_1045);
x_8 = x_1167;
x_9 = x_1168;
goto block_14;
}
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
lean_dec(x_1042);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1169 = lean_ctor_get(x_1041, 1);
lean_inc(x_1169);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1170 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1170 = lean_box(0);
}
if (lean_is_scalar(x_1170)) {
 x_1171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1171 = x_1170;
}
lean_ctor_set(x_1171, 0, x_1040);
lean_ctor_set(x_1171, 1, x_1169);
return x_1171;
}
}
else
{
lean_object* x_1172; lean_object* x_1173; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1172 = lean_ctor_get(x_1041, 0);
lean_inc(x_1172);
x_1173 = lean_ctor_get(x_1041, 1);
lean_inc(x_1173);
lean_dec(x_1041);
x_8 = x_1172;
x_9 = x_1173;
goto block_14;
}
}
else
{
lean_object* x_1174; lean_object* x_1175; 
lean_dec(x_1025);
lean_dec(x_1023);
lean_dec(x_81);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1174 = lean_ctor_get(x_1026, 0);
lean_inc(x_1174);
x_1175 = lean_ctor_get(x_1026, 1);
lean_inc(x_1175);
lean_dec(x_1026);
x_8 = x_1174;
x_9 = x_1175;
goto block_14;
}
}
else
{
lean_object* x_1176; lean_object* x_1177; 
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1176 = lean_ctor_get(x_1022, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1022, 1);
lean_inc(x_1177);
lean_dec(x_1022);
x_8 = x_1176;
x_9 = x_1177;
goto block_14;
}
}
}
else
{
lean_object* x_1178; lean_object* x_1179; 
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1178 = lean_ctor_get(x_1014, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1014, 1);
lean_inc(x_1179);
lean_dec(x_1014);
x_8 = x_1178;
x_9 = x_1179;
goto block_14;
}
}
}
else
{
lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1180 = lean_ctor_get(x_83, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_83, 1);
lean_inc(x_1181);
lean_dec(x_83);
x_8 = x_1180;
x_9 = x_1181;
goto block_14;
}
}
else
{
lean_object* x_1182; lean_object* x_1183; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1182 = lean_ctor_get(x_80, 0);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_80, 1);
lean_inc(x_1183);
lean_dec(x_80);
x_8 = x_1182;
x_9 = x_1183;
goto block_14;
}
}
else
{
uint8_t x_1184; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1184 = !lean_is_exclusive(x_73);
if (x_1184 == 0)
{
lean_object* x_1185; lean_object* x_1186; 
x_1185 = lean_ctor_get(x_73, 0);
lean_dec(x_1185);
x_1186 = lean_box(0);
lean_ctor_set(x_73, 0, x_1186);
return x_73;
}
else
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
x_1187 = lean_ctor_get(x_73, 1);
lean_inc(x_1187);
lean_dec(x_73);
x_1188 = lean_box(0);
x_1189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1189, 0, x_1188);
lean_ctor_set(x_1189, 1, x_1187);
return x_1189;
}
}
}
else
{
uint8_t x_1190; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1190 = !lean_is_exclusive(x_73);
if (x_1190 == 0)
{
lean_object* x_1191; lean_object* x_1192; 
x_1191 = lean_ctor_get(x_73, 0);
lean_dec(x_1191);
x_1192 = lean_box(0);
lean_ctor_set(x_73, 0, x_1192);
return x_73;
}
else
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1193 = lean_ctor_get(x_73, 1);
lean_inc(x_1193);
lean_dec(x_73);
x_1194 = lean_box(0);
x_1195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1195, 0, x_1194);
lean_ctor_set(x_1195, 1, x_1193);
return x_1195;
}
}
}
else
{
uint8_t x_1196; 
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1196 = !lean_is_exclusive(x_73);
if (x_1196 == 0)
{
lean_object* x_1197; lean_object* x_1198; 
x_1197 = lean_ctor_get(x_73, 0);
lean_dec(x_1197);
x_1198 = lean_box(0);
lean_ctor_set(x_73, 0, x_1198);
return x_73;
}
else
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
x_1199 = lean_ctor_get(x_73, 1);
lean_inc(x_1199);
lean_dec(x_73);
x_1200 = lean_box(0);
x_1201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1201, 0, x_1200);
lean_ctor_set(x_1201, 1, x_1199);
return x_1201;
}
}
}
else
{
uint8_t x_1202; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1202 = !lean_is_exclusive(x_73);
if (x_1202 == 0)
{
lean_object* x_1203; uint8_t x_1204; 
x_1203 = lean_ctor_get(x_73, 0);
x_1204 = l_Lean_Exception_isRuntime(x_1203);
if (x_1204 == 0)
{
lean_object* x_1205; 
lean_dec(x_1203);
x_1205 = lean_box(0);
lean_ctor_set_tag(x_73, 0);
lean_ctor_set(x_73, 0, x_1205);
return x_73;
}
else
{
return x_73;
}
}
else
{
lean_object* x_1206; lean_object* x_1207; uint8_t x_1208; 
x_1206 = lean_ctor_get(x_73, 0);
x_1207 = lean_ctor_get(x_73, 1);
lean_inc(x_1207);
lean_inc(x_1206);
lean_dec(x_73);
x_1208 = l_Lean_Exception_isRuntime(x_1206);
if (x_1208 == 0)
{
lean_object* x_1209; lean_object* x_1210; 
lean_dec(x_1206);
x_1209 = lean_box(0);
x_1210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1210, 0, x_1209);
lean_ctor_set(x_1210, 1, x_1207);
return x_1210;
}
else
{
lean_object* x_1211; 
x_1211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1211, 0, x_1206);
lean_ctor_set(x_1211, 1, x_1207);
return x_1211;
}
}
}
}
else
{
uint8_t x_1212; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1212 = !lean_is_exclusive(x_70);
if (x_1212 == 0)
{
lean_object* x_1213; uint8_t x_1214; 
x_1213 = lean_ctor_get(x_70, 0);
x_1214 = l_Lean_Exception_isRuntime(x_1213);
if (x_1214 == 0)
{
lean_object* x_1215; 
lean_dec(x_1213);
x_1215 = lean_box(0);
lean_ctor_set_tag(x_70, 0);
lean_ctor_set(x_70, 0, x_1215);
return x_70;
}
else
{
return x_70;
}
}
else
{
lean_object* x_1216; lean_object* x_1217; uint8_t x_1218; 
x_1216 = lean_ctor_get(x_70, 0);
x_1217 = lean_ctor_get(x_70, 1);
lean_inc(x_1217);
lean_inc(x_1216);
lean_dec(x_70);
x_1218 = l_Lean_Exception_isRuntime(x_1216);
if (x_1218 == 0)
{
lean_object* x_1219; lean_object* x_1220; 
lean_dec(x_1216);
x_1219 = lean_box(0);
x_1220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1220, 0, x_1219);
lean_ctor_set(x_1220, 1, x_1217);
return x_1220;
}
else
{
lean_object* x_1221; 
x_1221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1221, 0, x_1216);
lean_ctor_set(x_1221, 1, x_1217);
return x_1221;
}
}
}
}
else
{
uint8_t x_1222; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1222 = !lean_is_exclusive(x_63);
if (x_1222 == 0)
{
lean_object* x_1223; lean_object* x_1224; 
x_1223 = lean_ctor_get(x_63, 0);
lean_dec(x_1223);
x_1224 = lean_box(0);
lean_ctor_set(x_63, 0, x_1224);
return x_63;
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1225 = lean_ctor_get(x_63, 1);
lean_inc(x_1225);
lean_dec(x_63);
x_1226 = lean_box(0);
x_1227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1227, 0, x_1226);
lean_ctor_set(x_1227, 1, x_1225);
return x_1227;
}
}
}
else
{
uint8_t x_1228; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1228 = !lean_is_exclusive(x_63);
if (x_1228 == 0)
{
lean_object* x_1229; lean_object* x_1230; 
x_1229 = lean_ctor_get(x_63, 0);
lean_dec(x_1229);
x_1230 = lean_box(0);
lean_ctor_set(x_63, 0, x_1230);
return x_63;
}
else
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
x_1231 = lean_ctor_get(x_63, 1);
lean_inc(x_1231);
lean_dec(x_63);
x_1232 = lean_box(0);
x_1233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1233, 0, x_1232);
lean_ctor_set(x_1233, 1, x_1231);
return x_1233;
}
}
}
else
{
uint8_t x_1234; 
lean_dec(x_64);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1234 = !lean_is_exclusive(x_63);
if (x_1234 == 0)
{
lean_object* x_1235; lean_object* x_1236; 
x_1235 = lean_ctor_get(x_63, 0);
lean_dec(x_1235);
x_1236 = lean_box(0);
lean_ctor_set(x_63, 0, x_1236);
return x_63;
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1237 = lean_ctor_get(x_63, 1);
lean_inc(x_1237);
lean_dec(x_63);
x_1238 = lean_box(0);
x_1239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1239, 0, x_1238);
lean_ctor_set(x_1239, 1, x_1237);
return x_1239;
}
}
}
else
{
uint8_t x_1240; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1240 = !lean_is_exclusive(x_63);
if (x_1240 == 0)
{
lean_object* x_1241; uint8_t x_1242; 
x_1241 = lean_ctor_get(x_63, 0);
x_1242 = l_Lean_Exception_isRuntime(x_1241);
if (x_1242 == 0)
{
lean_object* x_1243; 
lean_dec(x_1241);
x_1243 = lean_box(0);
lean_ctor_set_tag(x_63, 0);
lean_ctor_set(x_63, 0, x_1243);
return x_63;
}
else
{
return x_63;
}
}
else
{
lean_object* x_1244; lean_object* x_1245; uint8_t x_1246; 
x_1244 = lean_ctor_get(x_63, 0);
x_1245 = lean_ctor_get(x_63, 1);
lean_inc(x_1245);
lean_inc(x_1244);
lean_dec(x_63);
x_1246 = l_Lean_Exception_isRuntime(x_1244);
if (x_1246 == 0)
{
lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_1244);
x_1247 = lean_box(0);
x_1248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1248, 0, x_1247);
lean_ctor_set(x_1248, 1, x_1245);
return x_1248;
}
else
{
lean_object* x_1249; 
x_1249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1249, 0, x_1244);
lean_ctor_set(x_1249, 1, x_1245);
return x_1249;
}
}
}
}
else
{
uint8_t x_1250; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1250 = !lean_is_exclusive(x_60);
if (x_1250 == 0)
{
lean_object* x_1251; uint8_t x_1252; 
x_1251 = lean_ctor_get(x_60, 0);
x_1252 = l_Lean_Exception_isRuntime(x_1251);
if (x_1252 == 0)
{
lean_object* x_1253; 
lean_dec(x_1251);
x_1253 = lean_box(0);
lean_ctor_set_tag(x_60, 0);
lean_ctor_set(x_60, 0, x_1253);
return x_60;
}
else
{
return x_60;
}
}
else
{
lean_object* x_1254; lean_object* x_1255; uint8_t x_1256; 
x_1254 = lean_ctor_get(x_60, 0);
x_1255 = lean_ctor_get(x_60, 1);
lean_inc(x_1255);
lean_inc(x_1254);
lean_dec(x_60);
x_1256 = l_Lean_Exception_isRuntime(x_1254);
if (x_1256 == 0)
{
lean_object* x_1257; lean_object* x_1258; 
lean_dec(x_1254);
x_1257 = lean_box(0);
x_1258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1258, 0, x_1257);
lean_ctor_set(x_1258, 1, x_1255);
return x_1258;
}
else
{
lean_object* x_1259; 
x_1259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1259, 0, x_1254);
lean_ctor_set(x_1259, 1, x_1255);
return x_1259;
}
}
}
}
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; uint8_t x_1263; 
x_1260 = lean_ctor_get(x_50, 1);
lean_inc(x_1260);
lean_dec(x_50);
x_1261 = lean_ctor_get(x_5, 2);
lean_inc(x_1261);
x_1262 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1263 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1261, x_1262);
lean_dec(x_1261);
if (x_1263 == 0)
{
lean_object* x_1264; lean_object* x_1265; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1264 = lean_box(0);
x_1265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1265, 0, x_1264);
lean_ctor_set(x_1265, 1, x_1260);
return x_1265;
}
else
{
lean_object* x_1266; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_48);
x_1266 = lean_infer_type(x_48, x_3, x_4, x_5, x_6, x_1260);
if (lean_obj_tag(x_1266) == 0)
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1266, 0);
lean_inc(x_1267);
x_1268 = lean_ctor_get(x_1266, 1);
lean_inc(x_1268);
lean_dec(x_1266);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1269 = lean_whnf(x_1267, x_3, x_4, x_5, x_6, x_1268);
if (lean_obj_tag(x_1269) == 0)
{
lean_object* x_1270; 
x_1270 = lean_ctor_get(x_1269, 0);
lean_inc(x_1270);
if (lean_obj_tag(x_1270) == 7)
{
lean_object* x_1271; 
x_1271 = lean_ctor_get(x_1270, 1);
lean_inc(x_1271);
if (lean_obj_tag(x_1271) == 3)
{
lean_object* x_1272; 
x_1272 = lean_ctor_get(x_1270, 2);
lean_inc(x_1272);
lean_dec(x_1270);
if (lean_obj_tag(x_1272) == 3)
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; 
x_1273 = lean_ctor_get(x_1269, 1);
lean_inc(x_1273);
lean_dec(x_1269);
x_1274 = lean_ctor_get(x_1271, 0);
lean_inc(x_1274);
lean_dec(x_1271);
x_1275 = lean_ctor_get(x_1272, 0);
lean_inc(x_1275);
lean_dec(x_1272);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_1276 = lean_infer_type(x_35, x_3, x_4, x_5, x_6, x_1273);
if (lean_obj_tag(x_1276) == 0)
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
x_1277 = lean_ctor_get(x_1276, 0);
lean_inc(x_1277);
x_1278 = lean_ctor_get(x_1276, 1);
lean_inc(x_1278);
lean_dec(x_1276);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1279 = lean_whnf(x_1277, x_3, x_4, x_5, x_6, x_1278);
if (lean_obj_tag(x_1279) == 0)
{
lean_object* x_1280; 
x_1280 = lean_ctor_get(x_1279, 0);
lean_inc(x_1280);
if (lean_obj_tag(x_1280) == 7)
{
lean_object* x_1281; 
x_1281 = lean_ctor_get(x_1280, 1);
lean_inc(x_1281);
if (lean_obj_tag(x_1281) == 3)
{
lean_object* x_1282; 
x_1282 = lean_ctor_get(x_1280, 2);
lean_inc(x_1282);
lean_dec(x_1280);
if (lean_obj_tag(x_1282) == 3)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
x_1283 = lean_ctor_get(x_1279, 1);
lean_inc(x_1283);
lean_dec(x_1279);
x_1284 = lean_ctor_get(x_1281, 0);
lean_inc(x_1284);
lean_dec(x_1281);
x_1285 = lean_ctor_get(x_1282, 0);
lean_inc(x_1285);
lean_dec(x_1282);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1286 = l_Lean_Meta_decLevel(x_1274, x_3, x_4, x_5, x_6, x_1283);
if (lean_obj_tag(x_1286) == 0)
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
x_1287 = lean_ctor_get(x_1286, 0);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1286, 1);
lean_inc(x_1288);
lean_dec(x_1286);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1289 = l_Lean_Meta_decLevel(x_1284, x_3, x_4, x_5, x_6, x_1288);
if (lean_obj_tag(x_1289) == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; uint8_t x_1293; lean_object* x_1294; 
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 1);
lean_inc(x_1291);
if (lean_is_exclusive(x_1289)) {
 lean_ctor_release(x_1289, 0);
 lean_ctor_release(x_1289, 1);
 x_1292 = x_1289;
} else {
 lean_dec_ref(x_1289);
 x_1292 = lean_box(0);
}
x_1293 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1287);
x_1294 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1287, x_1290, x_1293, x_3, x_4, x_5, x_6, x_1291);
if (lean_obj_tag(x_1294) == 0)
{
lean_object* x_1295; uint8_t x_1296; 
x_1295 = lean_ctor_get(x_1294, 0);
lean_inc(x_1295);
x_1296 = lean_unbox(x_1295);
lean_dec(x_1295);
if (x_1296 == 0)
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
lean_dec(x_1292);
lean_dec(x_1287);
lean_dec(x_1285);
lean_dec(x_1275);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1297 = lean_ctor_get(x_1294, 1);
lean_inc(x_1297);
if (lean_is_exclusive(x_1294)) {
 lean_ctor_release(x_1294, 0);
 lean_ctor_release(x_1294, 1);
 x_1298 = x_1294;
} else {
 lean_dec_ref(x_1294);
 x_1298 = lean_box(0);
}
x_1299 = lean_box(0);
if (lean_is_scalar(x_1298)) {
 x_1300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1300 = x_1298;
}
lean_ctor_set(x_1300, 0, x_1299);
lean_ctor_set(x_1300, 1, x_1297);
return x_1300;
}
else
{
lean_object* x_1301; lean_object* x_1302; 
x_1301 = lean_ctor_get(x_1294, 1);
lean_inc(x_1301);
lean_dec(x_1294);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1302 = l_Lean_Meta_decLevel(x_1275, x_3, x_4, x_5, x_6, x_1301);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1302, 1);
lean_inc(x_1304);
if (lean_is_exclusive(x_1302)) {
 lean_ctor_release(x_1302, 0);
 lean_ctor_release(x_1302, 1);
 x_1305 = x_1302;
} else {
 lean_dec_ref(x_1302);
 x_1305 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1306 = l_Lean_Meta_decLevel(x_1285, x_3, x_4, x_5, x_6, x_1304);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_1306, 1);
lean_inc(x_1308);
if (lean_is_exclusive(x_1306)) {
 lean_ctor_release(x_1306, 0);
 lean_ctor_release(x_1306, 1);
 x_1309 = x_1306;
} else {
 lean_dec_ref(x_1306);
 x_1309 = lean_box(0);
}
x_1310 = lean_box(0);
if (lean_is_scalar(x_1309)) {
 x_1311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1311 = x_1309;
 lean_ctor_set_tag(x_1311, 1);
}
lean_ctor_set(x_1311, 0, x_1307);
lean_ctor_set(x_1311, 1, x_1310);
if (lean_is_scalar(x_1305)) {
 x_1312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1312 = x_1305;
 lean_ctor_set_tag(x_1312, 1);
}
lean_ctor_set(x_1312, 0, x_1303);
lean_ctor_set(x_1312, 1, x_1311);
if (lean_is_scalar(x_1292)) {
 x_1313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1313 = x_1292;
 lean_ctor_set_tag(x_1313, 1);
}
lean_ctor_set(x_1313, 0, x_1287);
lean_ctor_set(x_1313, 1, x_1312);
x_1314 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1315 = l_Lean_Expr_const___override(x_1314, x_1313);
x_1316 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_48);
x_1317 = lean_array_push(x_1316, x_48);
lean_inc(x_35);
x_1318 = lean_array_push(x_1317, x_35);
x_1319 = l_Lean_mkAppN(x_1315, x_1318);
x_1320 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1321 = l_Lean_Meta_trySynthInstance(x_1319, x_1320, x_3, x_4, x_5, x_6, x_1308);
if (lean_obj_tag(x_1321) == 0)
{
lean_object* x_1322; 
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
if (lean_obj_tag(x_1322) == 1)
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; 
x_1323 = lean_ctor_get(x_1321, 1);
lean_inc(x_1323);
lean_dec(x_1321);
x_1324 = lean_ctor_get(x_1322, 0);
lean_inc(x_1324);
lean_dec(x_1322);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_1325 = l_Lean_Meta_getDecLevel(x_49, x_3, x_4, x_5, x_6, x_1323);
if (lean_obj_tag(x_1325) == 0)
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
x_1326 = lean_ctor_get(x_1325, 0);
lean_inc(x_1326);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1329 = l_Lean_Meta_getDecLevel(x_22, x_3, x_4, x_5, x_6, x_1327);
if (lean_obj_tag(x_1329) == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; 
x_1330 = lean_ctor_get(x_1329, 0);
lean_inc(x_1330);
x_1331 = lean_ctor_get(x_1329, 1);
lean_inc(x_1331);
if (lean_is_exclusive(x_1329)) {
 lean_ctor_release(x_1329, 0);
 lean_ctor_release(x_1329, 1);
 x_1332 = x_1329;
} else {
 lean_dec_ref(x_1329);
 x_1332 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_1333 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_1331);
if (lean_obj_tag(x_1333) == 0)
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; 
x_1334 = lean_ctor_get(x_1333, 0);
lean_inc(x_1334);
x_1335 = lean_ctor_get(x_1333, 1);
lean_inc(x_1335);
if (lean_is_exclusive(x_1333)) {
 lean_ctor_release(x_1333, 0);
 lean_ctor_release(x_1333, 1);
 x_1336 = x_1333;
} else {
 lean_dec_ref(x_1333);
 x_1336 = lean_box(0);
}
if (lean_is_scalar(x_1336)) {
 x_1337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1337 = x_1336;
 lean_ctor_set_tag(x_1337, 1);
}
lean_ctor_set(x_1337, 0, x_1334);
lean_ctor_set(x_1337, 1, x_1310);
if (lean_is_scalar(x_1332)) {
 x_1338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1338 = x_1332;
 lean_ctor_set_tag(x_1338, 1);
}
lean_ctor_set(x_1338, 0, x_1330);
lean_ctor_set(x_1338, 1, x_1337);
if (lean_is_scalar(x_1328)) {
 x_1339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1339 = x_1328;
 lean_ctor_set_tag(x_1339, 1);
}
lean_ctor_set(x_1339, 0, x_1326);
lean_ctor_set(x_1339, 1, x_1338);
x_1340 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_1339);
x_1341 = l_Lean_Expr_const___override(x_1340, x_1339);
x_1342 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_48);
x_1343 = lean_array_push(x_1342, x_48);
lean_inc(x_35);
x_1344 = lean_array_push(x_1343, x_35);
lean_inc(x_1324);
x_1345 = lean_array_push(x_1344, x_1324);
lean_inc(x_49);
x_1346 = lean_array_push(x_1345, x_49);
lean_inc(x_1);
x_1347 = lean_array_push(x_1346, x_1);
x_1348 = l_Lean_mkAppN(x_1341, x_1347);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1348);
x_1349 = lean_infer_type(x_1348, x_3, x_4, x_5, x_6, x_1335);
if (lean_obj_tag(x_1349) == 0)
{
lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
x_1350 = lean_ctor_get(x_1349, 0);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1349, 1);
lean_inc(x_1351);
lean_dec(x_1349);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_1352 = l_Lean_Meta_isExprDefEq(x_16, x_1350, x_3, x_4, x_5, x_6, x_1351);
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1353; uint8_t x_1354; 
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
x_1354 = lean_unbox(x_1353);
lean_dec(x_1353);
if (x_1354 == 0)
{
lean_object* x_1355; lean_object* x_1356; 
lean_dec(x_1348);
lean_free_object(x_38);
x_1355 = lean_ctor_get(x_1352, 1);
lean_inc(x_1355);
lean_dec(x_1352);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_1356 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_1355);
if (lean_obj_tag(x_1356) == 0)
{
lean_object* x_1357; 
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
if (lean_obj_tag(x_1357) == 0)
{
lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1358 = lean_ctor_get(x_1356, 1);
lean_inc(x_1358);
if (lean_is_exclusive(x_1356)) {
 lean_ctor_release(x_1356, 0);
 lean_ctor_release(x_1356, 1);
 x_1359 = x_1356;
} else {
 lean_dec_ref(x_1356);
 x_1359 = lean_box(0);
}
if (lean_is_scalar(x_1359)) {
 x_1360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1360 = x_1359;
}
lean_ctor_set(x_1360, 0, x_1320);
lean_ctor_set(x_1360, 1, x_1358);
return x_1360;
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1361 = lean_ctor_get(x_1356, 1);
lean_inc(x_1361);
lean_dec(x_1356);
x_1362 = lean_ctor_get(x_1357, 0);
lean_inc(x_1362);
lean_dec(x_1357);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_1363 = l_Lean_Meta_getLevel(x_49, x_3, x_4, x_5, x_6, x_1361);
if (lean_obj_tag(x_1363) == 0)
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
x_1364 = lean_ctor_get(x_1363, 0);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1363, 1);
lean_inc(x_1365);
if (lean_is_exclusive(x_1363)) {
 lean_ctor_release(x_1363, 0);
 lean_ctor_release(x_1363, 1);
 x_1366 = x_1363;
} else {
 lean_dec_ref(x_1363);
 x_1366 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_1367 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_1365);
if (lean_obj_tag(x_1367) == 0)
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; uint8_t x_1382; lean_object* x_1383; lean_object* x_1384; 
x_1368 = lean_ctor_get(x_1367, 0);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1367, 1);
lean_inc(x_1369);
if (lean_is_exclusive(x_1367)) {
 lean_ctor_release(x_1367, 0);
 lean_ctor_release(x_1367, 1);
 x_1370 = x_1367;
} else {
 lean_dec_ref(x_1367);
 x_1370 = lean_box(0);
}
if (lean_is_scalar(x_1370)) {
 x_1371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1371 = x_1370;
 lean_ctor_set_tag(x_1371, 1);
}
lean_ctor_set(x_1371, 0, x_1368);
lean_ctor_set(x_1371, 1, x_1310);
if (lean_is_scalar(x_1366)) {
 x_1372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1372 = x_1366;
 lean_ctor_set_tag(x_1372, 1);
}
lean_ctor_set(x_1372, 0, x_1364);
lean_ctor_set(x_1372, 1, x_1371);
x_1373 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1374 = l_Lean_Expr_const___override(x_1373, x_1372);
x_1375 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_49);
x_1376 = lean_array_push(x_1375, x_49);
x_1377 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_1378 = lean_array_push(x_1376, x_1377);
lean_inc(x_36);
x_1379 = lean_array_push(x_1378, x_36);
x_1380 = l_Lean_mkAppN(x_1374, x_1379);
x_1381 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_1382 = 0;
lean_inc(x_49);
x_1383 = l_Lean_Expr_forallE___override(x_1381, x_49, x_1380, x_1382);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1384 = l_Lean_Meta_trySynthInstance(x_1383, x_1320, x_3, x_4, x_5, x_6, x_1369);
if (lean_obj_tag(x_1384) == 0)
{
lean_object* x_1385; 
x_1385 = lean_ctor_get(x_1384, 0);
lean_inc(x_1385);
if (lean_obj_tag(x_1385) == 1)
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
x_1386 = lean_ctor_get(x_1384, 1);
lean_inc(x_1386);
lean_dec(x_1384);
x_1387 = lean_ctor_get(x_1385, 0);
lean_inc(x_1387);
lean_dec(x_1385);
x_1388 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_1389 = l_Lean_Expr_const___override(x_1388, x_1339);
x_1390 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_1391 = lean_array_push(x_1390, x_48);
x_1392 = lean_array_push(x_1391, x_35);
x_1393 = lean_array_push(x_1392, x_49);
x_1394 = lean_array_push(x_1393, x_36);
x_1395 = lean_array_push(x_1394, x_1324);
x_1396 = lean_array_push(x_1395, x_1387);
x_1397 = lean_array_push(x_1396, x_1362);
x_1398 = lean_array_push(x_1397, x_1);
x_1399 = l_Lean_mkAppN(x_1389, x_1398);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1400 = l_Lean_Meta_expandCoe(x_1399, x_3, x_4, x_5, x_6, x_1386);
if (lean_obj_tag(x_1400) == 0)
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1401 = lean_ctor_get(x_1400, 0);
lean_inc(x_1401);
x_1402 = lean_ctor_get(x_1400, 1);
lean_inc(x_1402);
lean_dec(x_1400);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1401);
x_1403 = lean_infer_type(x_1401, x_3, x_4, x_5, x_6, x_1402);
if (lean_obj_tag(x_1403) == 0)
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1404 = lean_ctor_get(x_1403, 0);
lean_inc(x_1404);
x_1405 = lean_ctor_get(x_1403, 1);
lean_inc(x_1405);
lean_dec(x_1403);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1406 = l_Lean_Meta_isExprDefEq(x_16, x_1404, x_3, x_4, x_5, x_6, x_1405);
if (lean_obj_tag(x_1406) == 0)
{
lean_object* x_1407; uint8_t x_1408; 
x_1407 = lean_ctor_get(x_1406, 0);
lean_inc(x_1407);
x_1408 = lean_unbox(x_1407);
lean_dec(x_1407);
if (x_1408 == 0)
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
lean_dec(x_1401);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1409 = lean_ctor_get(x_1406, 1);
lean_inc(x_1409);
if (lean_is_exclusive(x_1406)) {
 lean_ctor_release(x_1406, 0);
 lean_ctor_release(x_1406, 1);
 x_1410 = x_1406;
} else {
 lean_dec_ref(x_1406);
 x_1410 = lean_box(0);
}
if (lean_is_scalar(x_1410)) {
 x_1411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1411 = x_1410;
}
lean_ctor_set(x_1411, 0, x_1320);
lean_ctor_set(x_1411, 1, x_1409);
return x_1411;
}
else
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
x_1412 = lean_ctor_get(x_1406, 1);
lean_inc(x_1412);
lean_dec(x_1406);
x_1413 = lean_box(0);
x_1414 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1401, x_1413, x_3, x_4, x_5, x_6, x_1412);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1414, 1);
lean_inc(x_1416);
if (lean_is_exclusive(x_1414)) {
 lean_ctor_release(x_1414, 0);
 lean_ctor_release(x_1414, 1);
 x_1417 = x_1414;
} else {
 lean_dec_ref(x_1414);
 x_1417 = lean_box(0);
}
if (lean_is_scalar(x_1417)) {
 x_1418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1418 = x_1417;
}
lean_ctor_set(x_1418, 0, x_1415);
lean_ctor_set(x_1418, 1, x_1416);
return x_1418;
}
}
else
{
lean_object* x_1419; lean_object* x_1420; 
lean_dec(x_1401);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1419 = lean_ctor_get(x_1406, 0);
lean_inc(x_1419);
x_1420 = lean_ctor_get(x_1406, 1);
lean_inc(x_1420);
lean_dec(x_1406);
x_8 = x_1419;
x_9 = x_1420;
goto block_14;
}
}
else
{
lean_object* x_1421; lean_object* x_1422; 
lean_dec(x_1401);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1421 = lean_ctor_get(x_1403, 0);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_1403, 1);
lean_inc(x_1422);
lean_dec(x_1403);
x_8 = x_1421;
x_9 = x_1422;
goto block_14;
}
}
else
{
lean_object* x_1423; lean_object* x_1424; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1423 = lean_ctor_get(x_1400, 0);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1400, 1);
lean_inc(x_1424);
lean_dec(x_1400);
x_8 = x_1423;
x_9 = x_1424;
goto block_14;
}
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; 
lean_dec(x_1385);
lean_dec(x_1362);
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1425 = lean_ctor_get(x_1384, 1);
lean_inc(x_1425);
if (lean_is_exclusive(x_1384)) {
 lean_ctor_release(x_1384, 0);
 lean_ctor_release(x_1384, 1);
 x_1426 = x_1384;
} else {
 lean_dec_ref(x_1384);
 x_1426 = lean_box(0);
}
if (lean_is_scalar(x_1426)) {
 x_1427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1427 = x_1426;
}
lean_ctor_set(x_1427, 0, x_1320);
lean_ctor_set(x_1427, 1, x_1425);
return x_1427;
}
}
else
{
lean_object* x_1428; lean_object* x_1429; 
lean_dec(x_1362);
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1428 = lean_ctor_get(x_1384, 0);
lean_inc(x_1428);
x_1429 = lean_ctor_get(x_1384, 1);
lean_inc(x_1429);
lean_dec(x_1384);
x_8 = x_1428;
x_9 = x_1429;
goto block_14;
}
}
else
{
lean_object* x_1430; lean_object* x_1431; 
lean_dec(x_1366);
lean_dec(x_1364);
lean_dec(x_1362);
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1430 = lean_ctor_get(x_1367, 0);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_1367, 1);
lean_inc(x_1431);
lean_dec(x_1367);
x_8 = x_1430;
x_9 = x_1431;
goto block_14;
}
}
else
{
lean_object* x_1432; lean_object* x_1433; 
lean_dec(x_1362);
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1432 = lean_ctor_get(x_1363, 0);
lean_inc(x_1432);
x_1433 = lean_ctor_get(x_1363, 1);
lean_inc(x_1433);
lean_dec(x_1363);
x_8 = x_1432;
x_9 = x_1433;
goto block_14;
}
}
}
else
{
lean_object* x_1434; lean_object* x_1435; 
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1434 = lean_ctor_get(x_1356, 0);
lean_inc(x_1434);
x_1435 = lean_ctor_get(x_1356, 1);
lean_inc(x_1435);
lean_dec(x_1356);
x_8 = x_1434;
x_9 = x_1435;
goto block_14;
}
}
else
{
lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1436 = lean_ctor_get(x_1352, 1);
lean_inc(x_1436);
if (lean_is_exclusive(x_1352)) {
 lean_ctor_release(x_1352, 0);
 lean_ctor_release(x_1352, 1);
 x_1437 = x_1352;
} else {
 lean_dec_ref(x_1352);
 x_1437 = lean_box(0);
}
lean_ctor_set(x_38, 0, x_1348);
if (lean_is_scalar(x_1437)) {
 x_1438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1438 = x_1437;
}
lean_ctor_set(x_1438, 0, x_38);
lean_ctor_set(x_1438, 1, x_1436);
return x_1438;
}
}
else
{
lean_object* x_1439; lean_object* x_1440; 
lean_dec(x_1348);
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1439 = lean_ctor_get(x_1352, 0);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1352, 1);
lean_inc(x_1440);
lean_dec(x_1352);
x_8 = x_1439;
x_9 = x_1440;
goto block_14;
}
}
else
{
lean_object* x_1441; lean_object* x_1442; 
lean_dec(x_1348);
lean_dec(x_1339);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1441 = lean_ctor_get(x_1349, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1349, 1);
lean_inc(x_1442);
lean_dec(x_1349);
x_8 = x_1441;
x_9 = x_1442;
goto block_14;
}
}
else
{
lean_object* x_1443; lean_object* x_1444; 
lean_dec(x_1332);
lean_dec(x_1330);
lean_dec(x_1328);
lean_dec(x_1326);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1443 = lean_ctor_get(x_1333, 0);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1333, 1);
lean_inc(x_1444);
lean_dec(x_1333);
x_8 = x_1443;
x_9 = x_1444;
goto block_14;
}
}
else
{
lean_object* x_1445; lean_object* x_1446; 
lean_dec(x_1328);
lean_dec(x_1326);
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1445 = lean_ctor_get(x_1329, 0);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_1329, 1);
lean_inc(x_1446);
lean_dec(x_1329);
x_8 = x_1445;
x_9 = x_1446;
goto block_14;
}
}
else
{
lean_object* x_1447; lean_object* x_1448; 
lean_dec(x_1324);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1447 = lean_ctor_get(x_1325, 0);
lean_inc(x_1447);
x_1448 = lean_ctor_get(x_1325, 1);
lean_inc(x_1448);
lean_dec(x_1325);
x_8 = x_1447;
x_9 = x_1448;
goto block_14;
}
}
else
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
lean_dec(x_1322);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1449 = lean_ctor_get(x_1321, 1);
lean_inc(x_1449);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 lean_ctor_release(x_1321, 1);
 x_1450 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1450 = lean_box(0);
}
if (lean_is_scalar(x_1450)) {
 x_1451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1451 = x_1450;
}
lean_ctor_set(x_1451, 0, x_1320);
lean_ctor_set(x_1451, 1, x_1449);
return x_1451;
}
}
else
{
lean_object* x_1452; lean_object* x_1453; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1452 = lean_ctor_get(x_1321, 0);
lean_inc(x_1452);
x_1453 = lean_ctor_get(x_1321, 1);
lean_inc(x_1453);
lean_dec(x_1321);
x_8 = x_1452;
x_9 = x_1453;
goto block_14;
}
}
else
{
lean_object* x_1454; lean_object* x_1455; 
lean_dec(x_1305);
lean_dec(x_1303);
lean_dec(x_1292);
lean_dec(x_1287);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1454 = lean_ctor_get(x_1306, 0);
lean_inc(x_1454);
x_1455 = lean_ctor_get(x_1306, 1);
lean_inc(x_1455);
lean_dec(x_1306);
x_8 = x_1454;
x_9 = x_1455;
goto block_14;
}
}
else
{
lean_object* x_1456; lean_object* x_1457; 
lean_dec(x_1292);
lean_dec(x_1287);
lean_dec(x_1285);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1456 = lean_ctor_get(x_1302, 0);
lean_inc(x_1456);
x_1457 = lean_ctor_get(x_1302, 1);
lean_inc(x_1457);
lean_dec(x_1302);
x_8 = x_1456;
x_9 = x_1457;
goto block_14;
}
}
}
else
{
lean_object* x_1458; lean_object* x_1459; 
lean_dec(x_1292);
lean_dec(x_1287);
lean_dec(x_1285);
lean_dec(x_1275);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1458 = lean_ctor_get(x_1294, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1294, 1);
lean_inc(x_1459);
lean_dec(x_1294);
x_8 = x_1458;
x_9 = x_1459;
goto block_14;
}
}
else
{
lean_object* x_1460; lean_object* x_1461; 
lean_dec(x_1287);
lean_dec(x_1285);
lean_dec(x_1275);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1460 = lean_ctor_get(x_1289, 0);
lean_inc(x_1460);
x_1461 = lean_ctor_get(x_1289, 1);
lean_inc(x_1461);
lean_dec(x_1289);
x_8 = x_1460;
x_9 = x_1461;
goto block_14;
}
}
else
{
lean_object* x_1462; lean_object* x_1463; 
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1275);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1462 = lean_ctor_get(x_1286, 0);
lean_inc(x_1462);
x_1463 = lean_ctor_get(x_1286, 1);
lean_inc(x_1463);
lean_dec(x_1286);
x_8 = x_1462;
x_9 = x_1463;
goto block_14;
}
}
else
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
lean_dec(x_1282);
lean_dec(x_1281);
lean_dec(x_1275);
lean_dec(x_1274);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1464 = lean_ctor_get(x_1279, 1);
lean_inc(x_1464);
if (lean_is_exclusive(x_1279)) {
 lean_ctor_release(x_1279, 0);
 lean_ctor_release(x_1279, 1);
 x_1465 = x_1279;
} else {
 lean_dec_ref(x_1279);
 x_1465 = lean_box(0);
}
x_1466 = lean_box(0);
if (lean_is_scalar(x_1465)) {
 x_1467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1467 = x_1465;
}
lean_ctor_set(x_1467, 0, x_1466);
lean_ctor_set(x_1467, 1, x_1464);
return x_1467;
}
}
else
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
lean_dec(x_1281);
lean_dec(x_1280);
lean_dec(x_1275);
lean_dec(x_1274);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1468 = lean_ctor_get(x_1279, 1);
lean_inc(x_1468);
if (lean_is_exclusive(x_1279)) {
 lean_ctor_release(x_1279, 0);
 lean_ctor_release(x_1279, 1);
 x_1469 = x_1279;
} else {
 lean_dec_ref(x_1279);
 x_1469 = lean_box(0);
}
x_1470 = lean_box(0);
if (lean_is_scalar(x_1469)) {
 x_1471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1471 = x_1469;
}
lean_ctor_set(x_1471, 0, x_1470);
lean_ctor_set(x_1471, 1, x_1468);
return x_1471;
}
}
else
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
lean_dec(x_1280);
lean_dec(x_1275);
lean_dec(x_1274);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1472 = lean_ctor_get(x_1279, 1);
lean_inc(x_1472);
if (lean_is_exclusive(x_1279)) {
 lean_ctor_release(x_1279, 0);
 lean_ctor_release(x_1279, 1);
 x_1473 = x_1279;
} else {
 lean_dec_ref(x_1279);
 x_1473 = lean_box(0);
}
x_1474 = lean_box(0);
if (lean_is_scalar(x_1473)) {
 x_1475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1475 = x_1473;
}
lean_ctor_set(x_1475, 0, x_1474);
lean_ctor_set(x_1475, 1, x_1472);
return x_1475;
}
}
else
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; uint8_t x_1479; 
lean_dec(x_1275);
lean_dec(x_1274);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1476 = lean_ctor_get(x_1279, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1279, 1);
lean_inc(x_1477);
if (lean_is_exclusive(x_1279)) {
 lean_ctor_release(x_1279, 0);
 lean_ctor_release(x_1279, 1);
 x_1478 = x_1279;
} else {
 lean_dec_ref(x_1279);
 x_1478 = lean_box(0);
}
x_1479 = l_Lean_Exception_isRuntime(x_1476);
if (x_1479 == 0)
{
lean_object* x_1480; lean_object* x_1481; 
lean_dec(x_1476);
x_1480 = lean_box(0);
if (lean_is_scalar(x_1478)) {
 x_1481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1481 = x_1478;
 lean_ctor_set_tag(x_1481, 0);
}
lean_ctor_set(x_1481, 0, x_1480);
lean_ctor_set(x_1481, 1, x_1477);
return x_1481;
}
else
{
lean_object* x_1482; 
if (lean_is_scalar(x_1478)) {
 x_1482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1482 = x_1478;
}
lean_ctor_set(x_1482, 0, x_1476);
lean_ctor_set(x_1482, 1, x_1477);
return x_1482;
}
}
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; uint8_t x_1486; 
lean_dec(x_1275);
lean_dec(x_1274);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1483 = lean_ctor_get(x_1276, 0);
lean_inc(x_1483);
x_1484 = lean_ctor_get(x_1276, 1);
lean_inc(x_1484);
if (lean_is_exclusive(x_1276)) {
 lean_ctor_release(x_1276, 0);
 lean_ctor_release(x_1276, 1);
 x_1485 = x_1276;
} else {
 lean_dec_ref(x_1276);
 x_1485 = lean_box(0);
}
x_1486 = l_Lean_Exception_isRuntime(x_1483);
if (x_1486 == 0)
{
lean_object* x_1487; lean_object* x_1488; 
lean_dec(x_1483);
x_1487 = lean_box(0);
if (lean_is_scalar(x_1485)) {
 x_1488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1488 = x_1485;
 lean_ctor_set_tag(x_1488, 0);
}
lean_ctor_set(x_1488, 0, x_1487);
lean_ctor_set(x_1488, 1, x_1484);
return x_1488;
}
else
{
lean_object* x_1489; 
if (lean_is_scalar(x_1485)) {
 x_1489 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1489 = x_1485;
}
lean_ctor_set(x_1489, 0, x_1483);
lean_ctor_set(x_1489, 1, x_1484);
return x_1489;
}
}
}
else
{
lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
lean_dec(x_1272);
lean_dec(x_1271);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1490 = lean_ctor_get(x_1269, 1);
lean_inc(x_1490);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1491 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1491 = lean_box(0);
}
x_1492 = lean_box(0);
if (lean_is_scalar(x_1491)) {
 x_1493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1493 = x_1491;
}
lean_ctor_set(x_1493, 0, x_1492);
lean_ctor_set(x_1493, 1, x_1490);
return x_1493;
}
}
else
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
lean_dec(x_1271);
lean_dec(x_1270);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1494 = lean_ctor_get(x_1269, 1);
lean_inc(x_1494);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1495 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1495 = lean_box(0);
}
x_1496 = lean_box(0);
if (lean_is_scalar(x_1495)) {
 x_1497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1497 = x_1495;
}
lean_ctor_set(x_1497, 0, x_1496);
lean_ctor_set(x_1497, 1, x_1494);
return x_1497;
}
}
else
{
lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; 
lean_dec(x_1270);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1498 = lean_ctor_get(x_1269, 1);
lean_inc(x_1498);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1499 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1499 = lean_box(0);
}
x_1500 = lean_box(0);
if (lean_is_scalar(x_1499)) {
 x_1501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1501 = x_1499;
}
lean_ctor_set(x_1501, 0, x_1500);
lean_ctor_set(x_1501, 1, x_1498);
return x_1501;
}
}
else
{
lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; uint8_t x_1505; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1502 = lean_ctor_get(x_1269, 0);
lean_inc(x_1502);
x_1503 = lean_ctor_get(x_1269, 1);
lean_inc(x_1503);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1504 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1504 = lean_box(0);
}
x_1505 = l_Lean_Exception_isRuntime(x_1502);
if (x_1505 == 0)
{
lean_object* x_1506; lean_object* x_1507; 
lean_dec(x_1502);
x_1506 = lean_box(0);
if (lean_is_scalar(x_1504)) {
 x_1507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1507 = x_1504;
 lean_ctor_set_tag(x_1507, 0);
}
lean_ctor_set(x_1507, 0, x_1506);
lean_ctor_set(x_1507, 1, x_1503);
return x_1507;
}
else
{
lean_object* x_1508; 
if (lean_is_scalar(x_1504)) {
 x_1508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1508 = x_1504;
}
lean_ctor_set(x_1508, 0, x_1502);
lean_ctor_set(x_1508, 1, x_1503);
return x_1508;
}
}
}
else
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; uint8_t x_1512; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1509 = lean_ctor_get(x_1266, 0);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1266, 1);
lean_inc(x_1510);
if (lean_is_exclusive(x_1266)) {
 lean_ctor_release(x_1266, 0);
 lean_ctor_release(x_1266, 1);
 x_1511 = x_1266;
} else {
 lean_dec_ref(x_1266);
 x_1511 = lean_box(0);
}
x_1512 = l_Lean_Exception_isRuntime(x_1509);
if (x_1512 == 0)
{
lean_object* x_1513; lean_object* x_1514; 
lean_dec(x_1509);
x_1513 = lean_box(0);
if (lean_is_scalar(x_1511)) {
 x_1514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1514 = x_1511;
 lean_ctor_set_tag(x_1514, 0);
}
lean_ctor_set(x_1514, 0, x_1513);
lean_ctor_set(x_1514, 1, x_1510);
return x_1514;
}
else
{
lean_object* x_1515; 
if (lean_is_scalar(x_1511)) {
 x_1515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1515 = x_1511;
}
lean_ctor_set(x_1515, 0, x_1509);
lean_ctor_set(x_1515, 1, x_1510);
return x_1515;
}
}
}
}
}
else
{
lean_object* x_1516; lean_object* x_1517; 
lean_dec(x_22);
lean_dec(x_16);
x_1516 = lean_ctor_get(x_50, 1);
lean_inc(x_1516);
lean_dec(x_50);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1517 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_1516);
if (lean_obj_tag(x_1517) == 0)
{
lean_object* x_1518; 
x_1518 = lean_ctor_get(x_1517, 0);
lean_inc(x_1518);
if (lean_obj_tag(x_1518) == 0)
{
uint8_t x_1519; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1519 = !lean_is_exclusive(x_1517);
if (x_1519 == 0)
{
lean_object* x_1520; lean_object* x_1521; 
x_1520 = lean_ctor_get(x_1517, 0);
lean_dec(x_1520);
x_1521 = lean_box(0);
lean_ctor_set(x_1517, 0, x_1521);
return x_1517;
}
else
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
x_1522 = lean_ctor_get(x_1517, 1);
lean_inc(x_1522);
lean_dec(x_1517);
x_1523 = lean_box(0);
x_1524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1524, 0, x_1523);
lean_ctor_set(x_1524, 1, x_1522);
return x_1524;
}
}
else
{
lean_object* x_1525; uint8_t x_1526; 
x_1525 = lean_ctor_get(x_1517, 1);
lean_inc(x_1525);
lean_dec(x_1517);
x_1526 = !lean_is_exclusive(x_1518);
if (x_1526 == 0)
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; 
x_1527 = lean_ctor_get(x_1518, 0);
lean_ctor_set(x_1518, 0, x_48);
lean_ctor_set(x_38, 0, x_49);
lean_ctor_set(x_25, 0, x_36);
x_1528 = lean_box(0);
x_1529 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1529, 0, x_1527);
x_1530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1530, 0, x_1);
x_1531 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_1532 = lean_array_push(x_1531, x_1518);
x_1533 = lean_array_push(x_1532, x_38);
x_1534 = lean_array_push(x_1533, x_25);
x_1535 = lean_array_push(x_1534, x_1528);
x_1536 = lean_array_push(x_1535, x_1529);
x_1537 = lean_array_push(x_1536, x_1530);
x_1538 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1539 = l_Lean_Meta_mkAppOptM(x_1538, x_1537, x_3, x_4, x_5, x_6, x_1525);
if (lean_obj_tag(x_1539) == 0)
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; 
x_1540 = lean_ctor_get(x_1539, 0);
lean_inc(x_1540);
x_1541 = lean_ctor_get(x_1539, 1);
lean_inc(x_1541);
lean_dec(x_1539);
x_1542 = l_Lean_Meta_expandCoe(x_1540, x_3, x_4, x_5, x_6, x_1541);
if (lean_obj_tag(x_1542) == 0)
{
uint8_t x_1543; 
x_1543 = !lean_is_exclusive(x_1542);
if (x_1543 == 0)
{
lean_object* x_1544; lean_object* x_1545; 
x_1544 = lean_ctor_get(x_1542, 0);
x_1545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1545, 0, x_1544);
lean_ctor_set(x_1542, 0, x_1545);
return x_1542;
}
else
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; 
x_1546 = lean_ctor_get(x_1542, 0);
x_1547 = lean_ctor_get(x_1542, 1);
lean_inc(x_1547);
lean_inc(x_1546);
lean_dec(x_1542);
x_1548 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1548, 0, x_1546);
x_1549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1549, 0, x_1548);
lean_ctor_set(x_1549, 1, x_1547);
return x_1549;
}
}
else
{
uint8_t x_1550; 
x_1550 = !lean_is_exclusive(x_1542);
if (x_1550 == 0)
{
lean_object* x_1551; uint8_t x_1552; 
x_1551 = lean_ctor_get(x_1542, 0);
x_1552 = l_Lean_Exception_isRuntime(x_1551);
if (x_1552 == 0)
{
lean_dec(x_1551);
lean_ctor_set_tag(x_1542, 0);
lean_ctor_set(x_1542, 0, x_1528);
return x_1542;
}
else
{
return x_1542;
}
}
else
{
lean_object* x_1553; lean_object* x_1554; uint8_t x_1555; 
x_1553 = lean_ctor_get(x_1542, 0);
x_1554 = lean_ctor_get(x_1542, 1);
lean_inc(x_1554);
lean_inc(x_1553);
lean_dec(x_1542);
x_1555 = l_Lean_Exception_isRuntime(x_1553);
if (x_1555 == 0)
{
lean_object* x_1556; 
lean_dec(x_1553);
x_1556 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1556, 0, x_1528);
lean_ctor_set(x_1556, 1, x_1554);
return x_1556;
}
else
{
lean_object* x_1557; 
x_1557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1557, 0, x_1553);
lean_ctor_set(x_1557, 1, x_1554);
return x_1557;
}
}
}
}
else
{
uint8_t x_1558; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1558 = !lean_is_exclusive(x_1539);
if (x_1558 == 0)
{
lean_object* x_1559; uint8_t x_1560; 
x_1559 = lean_ctor_get(x_1539, 0);
x_1560 = l_Lean_Exception_isRuntime(x_1559);
if (x_1560 == 0)
{
lean_dec(x_1559);
lean_ctor_set_tag(x_1539, 0);
lean_ctor_set(x_1539, 0, x_1528);
return x_1539;
}
else
{
return x_1539;
}
}
else
{
lean_object* x_1561; lean_object* x_1562; uint8_t x_1563; 
x_1561 = lean_ctor_get(x_1539, 0);
x_1562 = lean_ctor_get(x_1539, 1);
lean_inc(x_1562);
lean_inc(x_1561);
lean_dec(x_1539);
x_1563 = l_Lean_Exception_isRuntime(x_1561);
if (x_1563 == 0)
{
lean_object* x_1564; 
lean_dec(x_1561);
x_1564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1564, 0, x_1528);
lean_ctor_set(x_1564, 1, x_1562);
return x_1564;
}
else
{
lean_object* x_1565; 
x_1565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1565, 0, x_1561);
lean_ctor_set(x_1565, 1, x_1562);
return x_1565;
}
}
}
}
else
{
lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; 
x_1566 = lean_ctor_get(x_1518, 0);
lean_inc(x_1566);
lean_dec(x_1518);
x_1567 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1567, 0, x_48);
lean_ctor_set(x_38, 0, x_49);
lean_ctor_set(x_25, 0, x_36);
x_1568 = lean_box(0);
x_1569 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1569, 0, x_1566);
x_1570 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1570, 0, x_1);
x_1571 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_1572 = lean_array_push(x_1571, x_1567);
x_1573 = lean_array_push(x_1572, x_38);
x_1574 = lean_array_push(x_1573, x_25);
x_1575 = lean_array_push(x_1574, x_1568);
x_1576 = lean_array_push(x_1575, x_1569);
x_1577 = lean_array_push(x_1576, x_1570);
x_1578 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1579 = l_Lean_Meta_mkAppOptM(x_1578, x_1577, x_3, x_4, x_5, x_6, x_1525);
if (lean_obj_tag(x_1579) == 0)
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; 
x_1580 = lean_ctor_get(x_1579, 0);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_1579, 1);
lean_inc(x_1581);
lean_dec(x_1579);
x_1582 = l_Lean_Meta_expandCoe(x_1580, x_3, x_4, x_5, x_6, x_1581);
if (lean_obj_tag(x_1582) == 0)
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1583 = lean_ctor_get(x_1582, 0);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_1582, 1);
lean_inc(x_1584);
if (lean_is_exclusive(x_1582)) {
 lean_ctor_release(x_1582, 0);
 lean_ctor_release(x_1582, 1);
 x_1585 = x_1582;
} else {
 lean_dec_ref(x_1582);
 x_1585 = lean_box(0);
}
x_1586 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1586, 0, x_1583);
if (lean_is_scalar(x_1585)) {
 x_1587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1587 = x_1585;
}
lean_ctor_set(x_1587, 0, x_1586);
lean_ctor_set(x_1587, 1, x_1584);
return x_1587;
}
else
{
lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; uint8_t x_1591; 
x_1588 = lean_ctor_get(x_1582, 0);
lean_inc(x_1588);
x_1589 = lean_ctor_get(x_1582, 1);
lean_inc(x_1589);
if (lean_is_exclusive(x_1582)) {
 lean_ctor_release(x_1582, 0);
 lean_ctor_release(x_1582, 1);
 x_1590 = x_1582;
} else {
 lean_dec_ref(x_1582);
 x_1590 = lean_box(0);
}
x_1591 = l_Lean_Exception_isRuntime(x_1588);
if (x_1591 == 0)
{
lean_object* x_1592; 
lean_dec(x_1588);
if (lean_is_scalar(x_1590)) {
 x_1592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1592 = x_1590;
 lean_ctor_set_tag(x_1592, 0);
}
lean_ctor_set(x_1592, 0, x_1568);
lean_ctor_set(x_1592, 1, x_1589);
return x_1592;
}
else
{
lean_object* x_1593; 
if (lean_is_scalar(x_1590)) {
 x_1593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1593 = x_1590;
}
lean_ctor_set(x_1593, 0, x_1588);
lean_ctor_set(x_1593, 1, x_1589);
return x_1593;
}
}
}
else
{
lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; uint8_t x_1597; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1594 = lean_ctor_get(x_1579, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1579, 1);
lean_inc(x_1595);
if (lean_is_exclusive(x_1579)) {
 lean_ctor_release(x_1579, 0);
 lean_ctor_release(x_1579, 1);
 x_1596 = x_1579;
} else {
 lean_dec_ref(x_1579);
 x_1596 = lean_box(0);
}
x_1597 = l_Lean_Exception_isRuntime(x_1594);
if (x_1597 == 0)
{
lean_object* x_1598; 
lean_dec(x_1594);
if (lean_is_scalar(x_1596)) {
 x_1598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1598 = x_1596;
 lean_ctor_set_tag(x_1598, 0);
}
lean_ctor_set(x_1598, 0, x_1568);
lean_ctor_set(x_1598, 1, x_1595);
return x_1598;
}
else
{
lean_object* x_1599; 
if (lean_is_scalar(x_1596)) {
 x_1599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1599 = x_1596;
}
lean_ctor_set(x_1599, 0, x_1594);
lean_ctor_set(x_1599, 1, x_1595);
return x_1599;
}
}
}
}
}
else
{
uint8_t x_1600; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1600 = !lean_is_exclusive(x_1517);
if (x_1600 == 0)
{
return x_1517;
}
else
{
lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; 
x_1601 = lean_ctor_get(x_1517, 0);
x_1602 = lean_ctor_get(x_1517, 1);
lean_inc(x_1602);
lean_inc(x_1601);
lean_dec(x_1517);
x_1603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1603, 0, x_1601);
lean_ctor_set(x_1603, 1, x_1602);
return x_1603;
}
}
}
}
else
{
uint8_t x_1604; 
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1604 = !lean_is_exclusive(x_50);
if (x_1604 == 0)
{
return x_50;
}
else
{
lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; 
x_1605 = lean_ctor_get(x_50, 0);
x_1606 = lean_ctor_get(x_50, 1);
lean_inc(x_1606);
lean_inc(x_1605);
lean_dec(x_50);
x_1607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1607, 0, x_1605);
lean_ctor_set(x_1607, 1, x_1606);
return x_1607;
}
}
}
else
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; 
x_1608 = lean_ctor_get(x_38, 0);
lean_inc(x_1608);
lean_dec(x_38);
x_1609 = lean_ctor_get(x_37, 1);
lean_inc(x_1609);
lean_dec(x_37);
x_1610 = lean_ctor_get(x_1608, 0);
lean_inc(x_1610);
x_1611 = lean_ctor_get(x_1608, 1);
lean_inc(x_1611);
lean_dec(x_1608);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
lean_inc(x_1610);
x_1612 = l_Lean_Meta_isExprDefEq(x_1610, x_35, x_3, x_4, x_5, x_6, x_1609);
if (lean_obj_tag(x_1612) == 0)
{
lean_object* x_1613; uint8_t x_1614; 
x_1613 = lean_ctor_get(x_1612, 0);
lean_inc(x_1613);
x_1614 = lean_unbox(x_1613);
lean_dec(x_1613);
if (x_1614 == 0)
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; uint8_t x_1619; 
lean_free_object(x_25);
x_1615 = lean_ctor_get(x_1612, 1);
lean_inc(x_1615);
if (lean_is_exclusive(x_1612)) {
 lean_ctor_release(x_1612, 0);
 lean_ctor_release(x_1612, 1);
 x_1616 = x_1612;
} else {
 lean_dec_ref(x_1612);
 x_1616 = lean_box(0);
}
x_1617 = lean_ctor_get(x_5, 2);
lean_inc(x_1617);
x_1618 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1619 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1617, x_1618);
lean_dec(x_1617);
if (x_1619 == 0)
{
lean_object* x_1620; lean_object* x_1621; 
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1620 = lean_box(0);
if (lean_is_scalar(x_1616)) {
 x_1621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1621 = x_1616;
}
lean_ctor_set(x_1621, 0, x_1620);
lean_ctor_set(x_1621, 1, x_1615);
return x_1621;
}
else
{
lean_object* x_1622; 
lean_dec(x_1616);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1610);
x_1622 = lean_infer_type(x_1610, x_3, x_4, x_5, x_6, x_1615);
if (lean_obj_tag(x_1622) == 0)
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; 
x_1623 = lean_ctor_get(x_1622, 0);
lean_inc(x_1623);
x_1624 = lean_ctor_get(x_1622, 1);
lean_inc(x_1624);
lean_dec(x_1622);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1625 = lean_whnf(x_1623, x_3, x_4, x_5, x_6, x_1624);
if (lean_obj_tag(x_1625) == 0)
{
lean_object* x_1626; 
x_1626 = lean_ctor_get(x_1625, 0);
lean_inc(x_1626);
if (lean_obj_tag(x_1626) == 7)
{
lean_object* x_1627; 
x_1627 = lean_ctor_get(x_1626, 1);
lean_inc(x_1627);
if (lean_obj_tag(x_1627) == 3)
{
lean_object* x_1628; 
x_1628 = lean_ctor_get(x_1626, 2);
lean_inc(x_1628);
lean_dec(x_1626);
if (lean_obj_tag(x_1628) == 3)
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; 
x_1629 = lean_ctor_get(x_1625, 1);
lean_inc(x_1629);
lean_dec(x_1625);
x_1630 = lean_ctor_get(x_1627, 0);
lean_inc(x_1630);
lean_dec(x_1627);
x_1631 = lean_ctor_get(x_1628, 0);
lean_inc(x_1631);
lean_dec(x_1628);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_1632 = lean_infer_type(x_35, x_3, x_4, x_5, x_6, x_1629);
if (lean_obj_tag(x_1632) == 0)
{
lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
x_1633 = lean_ctor_get(x_1632, 0);
lean_inc(x_1633);
x_1634 = lean_ctor_get(x_1632, 1);
lean_inc(x_1634);
lean_dec(x_1632);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1635 = lean_whnf(x_1633, x_3, x_4, x_5, x_6, x_1634);
if (lean_obj_tag(x_1635) == 0)
{
lean_object* x_1636; 
x_1636 = lean_ctor_get(x_1635, 0);
lean_inc(x_1636);
if (lean_obj_tag(x_1636) == 7)
{
lean_object* x_1637; 
x_1637 = lean_ctor_get(x_1636, 1);
lean_inc(x_1637);
if (lean_obj_tag(x_1637) == 3)
{
lean_object* x_1638; 
x_1638 = lean_ctor_get(x_1636, 2);
lean_inc(x_1638);
lean_dec(x_1636);
if (lean_obj_tag(x_1638) == 3)
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
x_1639 = lean_ctor_get(x_1635, 1);
lean_inc(x_1639);
lean_dec(x_1635);
x_1640 = lean_ctor_get(x_1637, 0);
lean_inc(x_1640);
lean_dec(x_1637);
x_1641 = lean_ctor_get(x_1638, 0);
lean_inc(x_1641);
lean_dec(x_1638);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1642 = l_Lean_Meta_decLevel(x_1630, x_3, x_4, x_5, x_6, x_1639);
if (lean_obj_tag(x_1642) == 0)
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
x_1643 = lean_ctor_get(x_1642, 0);
lean_inc(x_1643);
x_1644 = lean_ctor_get(x_1642, 1);
lean_inc(x_1644);
lean_dec(x_1642);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1645 = l_Lean_Meta_decLevel(x_1640, x_3, x_4, x_5, x_6, x_1644);
if (lean_obj_tag(x_1645) == 0)
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; uint8_t x_1649; lean_object* x_1650; 
x_1646 = lean_ctor_get(x_1645, 0);
lean_inc(x_1646);
x_1647 = lean_ctor_get(x_1645, 1);
lean_inc(x_1647);
if (lean_is_exclusive(x_1645)) {
 lean_ctor_release(x_1645, 0);
 lean_ctor_release(x_1645, 1);
 x_1648 = x_1645;
} else {
 lean_dec_ref(x_1645);
 x_1648 = lean_box(0);
}
x_1649 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1643);
x_1650 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1643, x_1646, x_1649, x_3, x_4, x_5, x_6, x_1647);
if (lean_obj_tag(x_1650) == 0)
{
lean_object* x_1651; uint8_t x_1652; 
x_1651 = lean_ctor_get(x_1650, 0);
lean_inc(x_1651);
x_1652 = lean_unbox(x_1651);
lean_dec(x_1651);
if (x_1652 == 0)
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; 
lean_dec(x_1648);
lean_dec(x_1643);
lean_dec(x_1641);
lean_dec(x_1631);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1653 = lean_ctor_get(x_1650, 1);
lean_inc(x_1653);
if (lean_is_exclusive(x_1650)) {
 lean_ctor_release(x_1650, 0);
 lean_ctor_release(x_1650, 1);
 x_1654 = x_1650;
} else {
 lean_dec_ref(x_1650);
 x_1654 = lean_box(0);
}
x_1655 = lean_box(0);
if (lean_is_scalar(x_1654)) {
 x_1656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1656 = x_1654;
}
lean_ctor_set(x_1656, 0, x_1655);
lean_ctor_set(x_1656, 1, x_1653);
return x_1656;
}
else
{
lean_object* x_1657; lean_object* x_1658; 
x_1657 = lean_ctor_get(x_1650, 1);
lean_inc(x_1657);
lean_dec(x_1650);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1658 = l_Lean_Meta_decLevel(x_1631, x_3, x_4, x_5, x_6, x_1657);
if (lean_obj_tag(x_1658) == 0)
{
lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; 
x_1659 = lean_ctor_get(x_1658, 0);
lean_inc(x_1659);
x_1660 = lean_ctor_get(x_1658, 1);
lean_inc(x_1660);
if (lean_is_exclusive(x_1658)) {
 lean_ctor_release(x_1658, 0);
 lean_ctor_release(x_1658, 1);
 x_1661 = x_1658;
} else {
 lean_dec_ref(x_1658);
 x_1661 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1662 = l_Lean_Meta_decLevel(x_1641, x_3, x_4, x_5, x_6, x_1660);
if (lean_obj_tag(x_1662) == 0)
{
lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; 
x_1663 = lean_ctor_get(x_1662, 0);
lean_inc(x_1663);
x_1664 = lean_ctor_get(x_1662, 1);
lean_inc(x_1664);
if (lean_is_exclusive(x_1662)) {
 lean_ctor_release(x_1662, 0);
 lean_ctor_release(x_1662, 1);
 x_1665 = x_1662;
} else {
 lean_dec_ref(x_1662);
 x_1665 = lean_box(0);
}
x_1666 = lean_box(0);
if (lean_is_scalar(x_1665)) {
 x_1667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1667 = x_1665;
 lean_ctor_set_tag(x_1667, 1);
}
lean_ctor_set(x_1667, 0, x_1663);
lean_ctor_set(x_1667, 1, x_1666);
if (lean_is_scalar(x_1661)) {
 x_1668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1668 = x_1661;
 lean_ctor_set_tag(x_1668, 1);
}
lean_ctor_set(x_1668, 0, x_1659);
lean_ctor_set(x_1668, 1, x_1667);
if (lean_is_scalar(x_1648)) {
 x_1669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1669 = x_1648;
 lean_ctor_set_tag(x_1669, 1);
}
lean_ctor_set(x_1669, 0, x_1643);
lean_ctor_set(x_1669, 1, x_1668);
x_1670 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_1671 = l_Lean_Expr_const___override(x_1670, x_1669);
x_1672 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_1610);
x_1673 = lean_array_push(x_1672, x_1610);
lean_inc(x_35);
x_1674 = lean_array_push(x_1673, x_35);
x_1675 = l_Lean_mkAppN(x_1671, x_1674);
x_1676 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1677 = l_Lean_Meta_trySynthInstance(x_1675, x_1676, x_3, x_4, x_5, x_6, x_1664);
if (lean_obj_tag(x_1677) == 0)
{
lean_object* x_1678; 
x_1678 = lean_ctor_get(x_1677, 0);
lean_inc(x_1678);
if (lean_obj_tag(x_1678) == 1)
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
x_1679 = lean_ctor_get(x_1677, 1);
lean_inc(x_1679);
lean_dec(x_1677);
x_1680 = lean_ctor_get(x_1678, 0);
lean_inc(x_1680);
lean_dec(x_1678);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1611);
x_1681 = l_Lean_Meta_getDecLevel(x_1611, x_3, x_4, x_5, x_6, x_1679);
if (lean_obj_tag(x_1681) == 0)
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
x_1682 = lean_ctor_get(x_1681, 0);
lean_inc(x_1682);
x_1683 = lean_ctor_get(x_1681, 1);
lean_inc(x_1683);
if (lean_is_exclusive(x_1681)) {
 lean_ctor_release(x_1681, 0);
 lean_ctor_release(x_1681, 1);
 x_1684 = x_1681;
} else {
 lean_dec_ref(x_1681);
 x_1684 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1685 = l_Lean_Meta_getDecLevel(x_22, x_3, x_4, x_5, x_6, x_1683);
if (lean_obj_tag(x_1685) == 0)
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
x_1686 = lean_ctor_get(x_1685, 0);
lean_inc(x_1686);
x_1687 = lean_ctor_get(x_1685, 1);
lean_inc(x_1687);
if (lean_is_exclusive(x_1685)) {
 lean_ctor_release(x_1685, 0);
 lean_ctor_release(x_1685, 1);
 x_1688 = x_1685;
} else {
 lean_dec_ref(x_1685);
 x_1688 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_1689 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_1687);
if (lean_obj_tag(x_1689) == 0)
{
lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; 
x_1690 = lean_ctor_get(x_1689, 0);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1689, 1);
lean_inc(x_1691);
if (lean_is_exclusive(x_1689)) {
 lean_ctor_release(x_1689, 0);
 lean_ctor_release(x_1689, 1);
 x_1692 = x_1689;
} else {
 lean_dec_ref(x_1689);
 x_1692 = lean_box(0);
}
if (lean_is_scalar(x_1692)) {
 x_1693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1693 = x_1692;
 lean_ctor_set_tag(x_1693, 1);
}
lean_ctor_set(x_1693, 0, x_1690);
lean_ctor_set(x_1693, 1, x_1666);
if (lean_is_scalar(x_1688)) {
 x_1694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1694 = x_1688;
 lean_ctor_set_tag(x_1694, 1);
}
lean_ctor_set(x_1694, 0, x_1686);
lean_ctor_set(x_1694, 1, x_1693);
if (lean_is_scalar(x_1684)) {
 x_1695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1695 = x_1684;
 lean_ctor_set_tag(x_1695, 1);
}
lean_ctor_set(x_1695, 0, x_1682);
lean_ctor_set(x_1695, 1, x_1694);
x_1696 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_1695);
x_1697 = l_Lean_Expr_const___override(x_1696, x_1695);
x_1698 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_1610);
x_1699 = lean_array_push(x_1698, x_1610);
lean_inc(x_35);
x_1700 = lean_array_push(x_1699, x_35);
lean_inc(x_1680);
x_1701 = lean_array_push(x_1700, x_1680);
lean_inc(x_1611);
x_1702 = lean_array_push(x_1701, x_1611);
lean_inc(x_1);
x_1703 = lean_array_push(x_1702, x_1);
x_1704 = l_Lean_mkAppN(x_1697, x_1703);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1704);
x_1705 = lean_infer_type(x_1704, x_3, x_4, x_5, x_6, x_1691);
if (lean_obj_tag(x_1705) == 0)
{
lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; 
x_1706 = lean_ctor_get(x_1705, 0);
lean_inc(x_1706);
x_1707 = lean_ctor_get(x_1705, 1);
lean_inc(x_1707);
lean_dec(x_1705);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_1708 = l_Lean_Meta_isExprDefEq(x_16, x_1706, x_3, x_4, x_5, x_6, x_1707);
if (lean_obj_tag(x_1708) == 0)
{
lean_object* x_1709; uint8_t x_1710; 
x_1709 = lean_ctor_get(x_1708, 0);
lean_inc(x_1709);
x_1710 = lean_unbox(x_1709);
lean_dec(x_1709);
if (x_1710 == 0)
{
lean_object* x_1711; lean_object* x_1712; 
lean_dec(x_1704);
x_1711 = lean_ctor_get(x_1708, 1);
lean_inc(x_1711);
lean_dec(x_1708);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_1712 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_1711);
if (lean_obj_tag(x_1712) == 0)
{
lean_object* x_1713; 
x_1713 = lean_ctor_get(x_1712, 0);
lean_inc(x_1713);
if (lean_obj_tag(x_1713) == 0)
{
lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; 
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1714 = lean_ctor_get(x_1712, 1);
lean_inc(x_1714);
if (lean_is_exclusive(x_1712)) {
 lean_ctor_release(x_1712, 0);
 lean_ctor_release(x_1712, 1);
 x_1715 = x_1712;
} else {
 lean_dec_ref(x_1712);
 x_1715 = lean_box(0);
}
if (lean_is_scalar(x_1715)) {
 x_1716 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1716 = x_1715;
}
lean_ctor_set(x_1716, 0, x_1676);
lean_ctor_set(x_1716, 1, x_1714);
return x_1716;
}
else
{
lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; 
x_1717 = lean_ctor_get(x_1712, 1);
lean_inc(x_1717);
lean_dec(x_1712);
x_1718 = lean_ctor_get(x_1713, 0);
lean_inc(x_1718);
lean_dec(x_1713);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1611);
x_1719 = l_Lean_Meta_getLevel(x_1611, x_3, x_4, x_5, x_6, x_1717);
if (lean_obj_tag(x_1719) == 0)
{
lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; 
x_1720 = lean_ctor_get(x_1719, 0);
lean_inc(x_1720);
x_1721 = lean_ctor_get(x_1719, 1);
lean_inc(x_1721);
if (lean_is_exclusive(x_1719)) {
 lean_ctor_release(x_1719, 0);
 lean_ctor_release(x_1719, 1);
 x_1722 = x_1719;
} else {
 lean_dec_ref(x_1719);
 x_1722 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_1723 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_1721);
if (lean_obj_tag(x_1723) == 0)
{
lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; uint8_t x_1738; lean_object* x_1739; lean_object* x_1740; 
x_1724 = lean_ctor_get(x_1723, 0);
lean_inc(x_1724);
x_1725 = lean_ctor_get(x_1723, 1);
lean_inc(x_1725);
if (lean_is_exclusive(x_1723)) {
 lean_ctor_release(x_1723, 0);
 lean_ctor_release(x_1723, 1);
 x_1726 = x_1723;
} else {
 lean_dec_ref(x_1723);
 x_1726 = lean_box(0);
}
if (lean_is_scalar(x_1726)) {
 x_1727 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1727 = x_1726;
 lean_ctor_set_tag(x_1727, 1);
}
lean_ctor_set(x_1727, 0, x_1724);
lean_ctor_set(x_1727, 1, x_1666);
if (lean_is_scalar(x_1722)) {
 x_1728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1728 = x_1722;
 lean_ctor_set_tag(x_1728, 1);
}
lean_ctor_set(x_1728, 0, x_1720);
lean_ctor_set(x_1728, 1, x_1727);
x_1729 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_1730 = l_Lean_Expr_const___override(x_1729, x_1728);
x_1731 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_1611);
x_1732 = lean_array_push(x_1731, x_1611);
x_1733 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_1734 = lean_array_push(x_1732, x_1733);
lean_inc(x_36);
x_1735 = lean_array_push(x_1734, x_36);
x_1736 = l_Lean_mkAppN(x_1730, x_1735);
x_1737 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_1738 = 0;
lean_inc(x_1611);
x_1739 = l_Lean_Expr_forallE___override(x_1737, x_1611, x_1736, x_1738);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1740 = l_Lean_Meta_trySynthInstance(x_1739, x_1676, x_3, x_4, x_5, x_6, x_1725);
if (lean_obj_tag(x_1740) == 0)
{
lean_object* x_1741; 
x_1741 = lean_ctor_get(x_1740, 0);
lean_inc(x_1741);
if (lean_obj_tag(x_1741) == 1)
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; 
x_1742 = lean_ctor_get(x_1740, 1);
lean_inc(x_1742);
lean_dec(x_1740);
x_1743 = lean_ctor_get(x_1741, 0);
lean_inc(x_1743);
lean_dec(x_1741);
x_1744 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_1745 = l_Lean_Expr_const___override(x_1744, x_1695);
x_1746 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_1747 = lean_array_push(x_1746, x_1610);
x_1748 = lean_array_push(x_1747, x_35);
x_1749 = lean_array_push(x_1748, x_1611);
x_1750 = lean_array_push(x_1749, x_36);
x_1751 = lean_array_push(x_1750, x_1680);
x_1752 = lean_array_push(x_1751, x_1743);
x_1753 = lean_array_push(x_1752, x_1718);
x_1754 = lean_array_push(x_1753, x_1);
x_1755 = l_Lean_mkAppN(x_1745, x_1754);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1756 = l_Lean_Meta_expandCoe(x_1755, x_3, x_4, x_5, x_6, x_1742);
if (lean_obj_tag(x_1756) == 0)
{
lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; 
x_1757 = lean_ctor_get(x_1756, 0);
lean_inc(x_1757);
x_1758 = lean_ctor_get(x_1756, 1);
lean_inc(x_1758);
lean_dec(x_1756);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1757);
x_1759 = lean_infer_type(x_1757, x_3, x_4, x_5, x_6, x_1758);
if (lean_obj_tag(x_1759) == 0)
{
lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; 
x_1760 = lean_ctor_get(x_1759, 0);
lean_inc(x_1760);
x_1761 = lean_ctor_get(x_1759, 1);
lean_inc(x_1761);
lean_dec(x_1759);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1762 = l_Lean_Meta_isExprDefEq(x_16, x_1760, x_3, x_4, x_5, x_6, x_1761);
if (lean_obj_tag(x_1762) == 0)
{
lean_object* x_1763; uint8_t x_1764; 
x_1763 = lean_ctor_get(x_1762, 0);
lean_inc(x_1763);
x_1764 = lean_unbox(x_1763);
lean_dec(x_1763);
if (x_1764 == 0)
{
lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; 
lean_dec(x_1757);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1765 = lean_ctor_get(x_1762, 1);
lean_inc(x_1765);
if (lean_is_exclusive(x_1762)) {
 lean_ctor_release(x_1762, 0);
 lean_ctor_release(x_1762, 1);
 x_1766 = x_1762;
} else {
 lean_dec_ref(x_1762);
 x_1766 = lean_box(0);
}
if (lean_is_scalar(x_1766)) {
 x_1767 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1767 = x_1766;
}
lean_ctor_set(x_1767, 0, x_1676);
lean_ctor_set(x_1767, 1, x_1765);
return x_1767;
}
else
{
lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; 
x_1768 = lean_ctor_get(x_1762, 1);
lean_inc(x_1768);
lean_dec(x_1762);
x_1769 = lean_box(0);
x_1770 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_1757, x_1769, x_3, x_4, x_5, x_6, x_1768);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1771 = lean_ctor_get(x_1770, 0);
lean_inc(x_1771);
x_1772 = lean_ctor_get(x_1770, 1);
lean_inc(x_1772);
if (lean_is_exclusive(x_1770)) {
 lean_ctor_release(x_1770, 0);
 lean_ctor_release(x_1770, 1);
 x_1773 = x_1770;
} else {
 lean_dec_ref(x_1770);
 x_1773 = lean_box(0);
}
if (lean_is_scalar(x_1773)) {
 x_1774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1774 = x_1773;
}
lean_ctor_set(x_1774, 0, x_1771);
lean_ctor_set(x_1774, 1, x_1772);
return x_1774;
}
}
else
{
lean_object* x_1775; lean_object* x_1776; 
lean_dec(x_1757);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1775 = lean_ctor_get(x_1762, 0);
lean_inc(x_1775);
x_1776 = lean_ctor_get(x_1762, 1);
lean_inc(x_1776);
lean_dec(x_1762);
x_8 = x_1775;
x_9 = x_1776;
goto block_14;
}
}
else
{
lean_object* x_1777; lean_object* x_1778; 
lean_dec(x_1757);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1777 = lean_ctor_get(x_1759, 0);
lean_inc(x_1777);
x_1778 = lean_ctor_get(x_1759, 1);
lean_inc(x_1778);
lean_dec(x_1759);
x_8 = x_1777;
x_9 = x_1778;
goto block_14;
}
}
else
{
lean_object* x_1779; lean_object* x_1780; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1779 = lean_ctor_get(x_1756, 0);
lean_inc(x_1779);
x_1780 = lean_ctor_get(x_1756, 1);
lean_inc(x_1780);
lean_dec(x_1756);
x_8 = x_1779;
x_9 = x_1780;
goto block_14;
}
}
else
{
lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; 
lean_dec(x_1741);
lean_dec(x_1718);
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1781 = lean_ctor_get(x_1740, 1);
lean_inc(x_1781);
if (lean_is_exclusive(x_1740)) {
 lean_ctor_release(x_1740, 0);
 lean_ctor_release(x_1740, 1);
 x_1782 = x_1740;
} else {
 lean_dec_ref(x_1740);
 x_1782 = lean_box(0);
}
if (lean_is_scalar(x_1782)) {
 x_1783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1783 = x_1782;
}
lean_ctor_set(x_1783, 0, x_1676);
lean_ctor_set(x_1783, 1, x_1781);
return x_1783;
}
}
else
{
lean_object* x_1784; lean_object* x_1785; 
lean_dec(x_1718);
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1784 = lean_ctor_get(x_1740, 0);
lean_inc(x_1784);
x_1785 = lean_ctor_get(x_1740, 1);
lean_inc(x_1785);
lean_dec(x_1740);
x_8 = x_1784;
x_9 = x_1785;
goto block_14;
}
}
else
{
lean_object* x_1786; lean_object* x_1787; 
lean_dec(x_1722);
lean_dec(x_1720);
lean_dec(x_1718);
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1786 = lean_ctor_get(x_1723, 0);
lean_inc(x_1786);
x_1787 = lean_ctor_get(x_1723, 1);
lean_inc(x_1787);
lean_dec(x_1723);
x_8 = x_1786;
x_9 = x_1787;
goto block_14;
}
}
else
{
lean_object* x_1788; lean_object* x_1789; 
lean_dec(x_1718);
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1788 = lean_ctor_get(x_1719, 0);
lean_inc(x_1788);
x_1789 = lean_ctor_get(x_1719, 1);
lean_inc(x_1789);
lean_dec(x_1719);
x_8 = x_1788;
x_9 = x_1789;
goto block_14;
}
}
}
else
{
lean_object* x_1790; lean_object* x_1791; 
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1790 = lean_ctor_get(x_1712, 0);
lean_inc(x_1790);
x_1791 = lean_ctor_get(x_1712, 1);
lean_inc(x_1791);
lean_dec(x_1712);
x_8 = x_1790;
x_9 = x_1791;
goto block_14;
}
}
else
{
lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; 
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1792 = lean_ctor_get(x_1708, 1);
lean_inc(x_1792);
if (lean_is_exclusive(x_1708)) {
 lean_ctor_release(x_1708, 0);
 lean_ctor_release(x_1708, 1);
 x_1793 = x_1708;
} else {
 lean_dec_ref(x_1708);
 x_1793 = lean_box(0);
}
x_1794 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1794, 0, x_1704);
if (lean_is_scalar(x_1793)) {
 x_1795 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1795 = x_1793;
}
lean_ctor_set(x_1795, 0, x_1794);
lean_ctor_set(x_1795, 1, x_1792);
return x_1795;
}
}
else
{
lean_object* x_1796; lean_object* x_1797; 
lean_dec(x_1704);
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1796 = lean_ctor_get(x_1708, 0);
lean_inc(x_1796);
x_1797 = lean_ctor_get(x_1708, 1);
lean_inc(x_1797);
lean_dec(x_1708);
x_8 = x_1796;
x_9 = x_1797;
goto block_14;
}
}
else
{
lean_object* x_1798; lean_object* x_1799; 
lean_dec(x_1704);
lean_dec(x_1695);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1798 = lean_ctor_get(x_1705, 0);
lean_inc(x_1798);
x_1799 = lean_ctor_get(x_1705, 1);
lean_inc(x_1799);
lean_dec(x_1705);
x_8 = x_1798;
x_9 = x_1799;
goto block_14;
}
}
else
{
lean_object* x_1800; lean_object* x_1801; 
lean_dec(x_1688);
lean_dec(x_1686);
lean_dec(x_1684);
lean_dec(x_1682);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1800 = lean_ctor_get(x_1689, 0);
lean_inc(x_1800);
x_1801 = lean_ctor_get(x_1689, 1);
lean_inc(x_1801);
lean_dec(x_1689);
x_8 = x_1800;
x_9 = x_1801;
goto block_14;
}
}
else
{
lean_object* x_1802; lean_object* x_1803; 
lean_dec(x_1684);
lean_dec(x_1682);
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1802 = lean_ctor_get(x_1685, 0);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1685, 1);
lean_inc(x_1803);
lean_dec(x_1685);
x_8 = x_1802;
x_9 = x_1803;
goto block_14;
}
}
else
{
lean_object* x_1804; lean_object* x_1805; 
lean_dec(x_1680);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1804 = lean_ctor_get(x_1681, 0);
lean_inc(x_1804);
x_1805 = lean_ctor_get(x_1681, 1);
lean_inc(x_1805);
lean_dec(x_1681);
x_8 = x_1804;
x_9 = x_1805;
goto block_14;
}
}
else
{
lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; 
lean_dec(x_1678);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1806 = lean_ctor_get(x_1677, 1);
lean_inc(x_1806);
if (lean_is_exclusive(x_1677)) {
 lean_ctor_release(x_1677, 0);
 lean_ctor_release(x_1677, 1);
 x_1807 = x_1677;
} else {
 lean_dec_ref(x_1677);
 x_1807 = lean_box(0);
}
if (lean_is_scalar(x_1807)) {
 x_1808 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1808 = x_1807;
}
lean_ctor_set(x_1808, 0, x_1676);
lean_ctor_set(x_1808, 1, x_1806);
return x_1808;
}
}
else
{
lean_object* x_1809; lean_object* x_1810; 
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1809 = lean_ctor_get(x_1677, 0);
lean_inc(x_1809);
x_1810 = lean_ctor_get(x_1677, 1);
lean_inc(x_1810);
lean_dec(x_1677);
x_8 = x_1809;
x_9 = x_1810;
goto block_14;
}
}
else
{
lean_object* x_1811; lean_object* x_1812; 
lean_dec(x_1661);
lean_dec(x_1659);
lean_dec(x_1648);
lean_dec(x_1643);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1811 = lean_ctor_get(x_1662, 0);
lean_inc(x_1811);
x_1812 = lean_ctor_get(x_1662, 1);
lean_inc(x_1812);
lean_dec(x_1662);
x_8 = x_1811;
x_9 = x_1812;
goto block_14;
}
}
else
{
lean_object* x_1813; lean_object* x_1814; 
lean_dec(x_1648);
lean_dec(x_1643);
lean_dec(x_1641);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1813 = lean_ctor_get(x_1658, 0);
lean_inc(x_1813);
x_1814 = lean_ctor_get(x_1658, 1);
lean_inc(x_1814);
lean_dec(x_1658);
x_8 = x_1813;
x_9 = x_1814;
goto block_14;
}
}
}
else
{
lean_object* x_1815; lean_object* x_1816; 
lean_dec(x_1648);
lean_dec(x_1643);
lean_dec(x_1641);
lean_dec(x_1631);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1815 = lean_ctor_get(x_1650, 0);
lean_inc(x_1815);
x_1816 = lean_ctor_get(x_1650, 1);
lean_inc(x_1816);
lean_dec(x_1650);
x_8 = x_1815;
x_9 = x_1816;
goto block_14;
}
}
else
{
lean_object* x_1817; lean_object* x_1818; 
lean_dec(x_1643);
lean_dec(x_1641);
lean_dec(x_1631);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1817 = lean_ctor_get(x_1645, 0);
lean_inc(x_1817);
x_1818 = lean_ctor_get(x_1645, 1);
lean_inc(x_1818);
lean_dec(x_1645);
x_8 = x_1817;
x_9 = x_1818;
goto block_14;
}
}
else
{
lean_object* x_1819; lean_object* x_1820; 
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1631);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1819 = lean_ctor_get(x_1642, 0);
lean_inc(x_1819);
x_1820 = lean_ctor_get(x_1642, 1);
lean_inc(x_1820);
lean_dec(x_1642);
x_8 = x_1819;
x_9 = x_1820;
goto block_14;
}
}
else
{
lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; 
lean_dec(x_1638);
lean_dec(x_1637);
lean_dec(x_1631);
lean_dec(x_1630);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1821 = lean_ctor_get(x_1635, 1);
lean_inc(x_1821);
if (lean_is_exclusive(x_1635)) {
 lean_ctor_release(x_1635, 0);
 lean_ctor_release(x_1635, 1);
 x_1822 = x_1635;
} else {
 lean_dec_ref(x_1635);
 x_1822 = lean_box(0);
}
x_1823 = lean_box(0);
if (lean_is_scalar(x_1822)) {
 x_1824 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1824 = x_1822;
}
lean_ctor_set(x_1824, 0, x_1823);
lean_ctor_set(x_1824, 1, x_1821);
return x_1824;
}
}
else
{
lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; 
lean_dec(x_1637);
lean_dec(x_1636);
lean_dec(x_1631);
lean_dec(x_1630);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1825 = lean_ctor_get(x_1635, 1);
lean_inc(x_1825);
if (lean_is_exclusive(x_1635)) {
 lean_ctor_release(x_1635, 0);
 lean_ctor_release(x_1635, 1);
 x_1826 = x_1635;
} else {
 lean_dec_ref(x_1635);
 x_1826 = lean_box(0);
}
x_1827 = lean_box(0);
if (lean_is_scalar(x_1826)) {
 x_1828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1828 = x_1826;
}
lean_ctor_set(x_1828, 0, x_1827);
lean_ctor_set(x_1828, 1, x_1825);
return x_1828;
}
}
else
{
lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; 
lean_dec(x_1636);
lean_dec(x_1631);
lean_dec(x_1630);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1829 = lean_ctor_get(x_1635, 1);
lean_inc(x_1829);
if (lean_is_exclusive(x_1635)) {
 lean_ctor_release(x_1635, 0);
 lean_ctor_release(x_1635, 1);
 x_1830 = x_1635;
} else {
 lean_dec_ref(x_1635);
 x_1830 = lean_box(0);
}
x_1831 = lean_box(0);
if (lean_is_scalar(x_1830)) {
 x_1832 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1832 = x_1830;
}
lean_ctor_set(x_1832, 0, x_1831);
lean_ctor_set(x_1832, 1, x_1829);
return x_1832;
}
}
else
{
lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; uint8_t x_1836; 
lean_dec(x_1631);
lean_dec(x_1630);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1833 = lean_ctor_get(x_1635, 0);
lean_inc(x_1833);
x_1834 = lean_ctor_get(x_1635, 1);
lean_inc(x_1834);
if (lean_is_exclusive(x_1635)) {
 lean_ctor_release(x_1635, 0);
 lean_ctor_release(x_1635, 1);
 x_1835 = x_1635;
} else {
 lean_dec_ref(x_1635);
 x_1835 = lean_box(0);
}
x_1836 = l_Lean_Exception_isRuntime(x_1833);
if (x_1836 == 0)
{
lean_object* x_1837; lean_object* x_1838; 
lean_dec(x_1833);
x_1837 = lean_box(0);
if (lean_is_scalar(x_1835)) {
 x_1838 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1838 = x_1835;
 lean_ctor_set_tag(x_1838, 0);
}
lean_ctor_set(x_1838, 0, x_1837);
lean_ctor_set(x_1838, 1, x_1834);
return x_1838;
}
else
{
lean_object* x_1839; 
if (lean_is_scalar(x_1835)) {
 x_1839 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1839 = x_1835;
}
lean_ctor_set(x_1839, 0, x_1833);
lean_ctor_set(x_1839, 1, x_1834);
return x_1839;
}
}
}
else
{
lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; uint8_t x_1843; 
lean_dec(x_1631);
lean_dec(x_1630);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1840 = lean_ctor_get(x_1632, 0);
lean_inc(x_1840);
x_1841 = lean_ctor_get(x_1632, 1);
lean_inc(x_1841);
if (lean_is_exclusive(x_1632)) {
 lean_ctor_release(x_1632, 0);
 lean_ctor_release(x_1632, 1);
 x_1842 = x_1632;
} else {
 lean_dec_ref(x_1632);
 x_1842 = lean_box(0);
}
x_1843 = l_Lean_Exception_isRuntime(x_1840);
if (x_1843 == 0)
{
lean_object* x_1844; lean_object* x_1845; 
lean_dec(x_1840);
x_1844 = lean_box(0);
if (lean_is_scalar(x_1842)) {
 x_1845 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1845 = x_1842;
 lean_ctor_set_tag(x_1845, 0);
}
lean_ctor_set(x_1845, 0, x_1844);
lean_ctor_set(x_1845, 1, x_1841);
return x_1845;
}
else
{
lean_object* x_1846; 
if (lean_is_scalar(x_1842)) {
 x_1846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1846 = x_1842;
}
lean_ctor_set(x_1846, 0, x_1840);
lean_ctor_set(x_1846, 1, x_1841);
return x_1846;
}
}
}
else
{
lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; 
lean_dec(x_1628);
lean_dec(x_1627);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1847 = lean_ctor_get(x_1625, 1);
lean_inc(x_1847);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1848 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1848 = lean_box(0);
}
x_1849 = lean_box(0);
if (lean_is_scalar(x_1848)) {
 x_1850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1850 = x_1848;
}
lean_ctor_set(x_1850, 0, x_1849);
lean_ctor_set(x_1850, 1, x_1847);
return x_1850;
}
}
else
{
lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; 
lean_dec(x_1627);
lean_dec(x_1626);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1851 = lean_ctor_get(x_1625, 1);
lean_inc(x_1851);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1852 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1852 = lean_box(0);
}
x_1853 = lean_box(0);
if (lean_is_scalar(x_1852)) {
 x_1854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1854 = x_1852;
}
lean_ctor_set(x_1854, 0, x_1853);
lean_ctor_set(x_1854, 1, x_1851);
return x_1854;
}
}
else
{
lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; 
lean_dec(x_1626);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1855 = lean_ctor_get(x_1625, 1);
lean_inc(x_1855);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1856 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1856 = lean_box(0);
}
x_1857 = lean_box(0);
if (lean_is_scalar(x_1856)) {
 x_1858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1858 = x_1856;
}
lean_ctor_set(x_1858, 0, x_1857);
lean_ctor_set(x_1858, 1, x_1855);
return x_1858;
}
}
else
{
lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; uint8_t x_1862; 
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1859 = lean_ctor_get(x_1625, 0);
lean_inc(x_1859);
x_1860 = lean_ctor_get(x_1625, 1);
lean_inc(x_1860);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1861 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1861 = lean_box(0);
}
x_1862 = l_Lean_Exception_isRuntime(x_1859);
if (x_1862 == 0)
{
lean_object* x_1863; lean_object* x_1864; 
lean_dec(x_1859);
x_1863 = lean_box(0);
if (lean_is_scalar(x_1861)) {
 x_1864 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1864 = x_1861;
 lean_ctor_set_tag(x_1864, 0);
}
lean_ctor_set(x_1864, 0, x_1863);
lean_ctor_set(x_1864, 1, x_1860);
return x_1864;
}
else
{
lean_object* x_1865; 
if (lean_is_scalar(x_1861)) {
 x_1865 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1865 = x_1861;
}
lean_ctor_set(x_1865, 0, x_1859);
lean_ctor_set(x_1865, 1, x_1860);
return x_1865;
}
}
}
else
{
lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; uint8_t x_1869; 
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1866 = lean_ctor_get(x_1622, 0);
lean_inc(x_1866);
x_1867 = lean_ctor_get(x_1622, 1);
lean_inc(x_1867);
if (lean_is_exclusive(x_1622)) {
 lean_ctor_release(x_1622, 0);
 lean_ctor_release(x_1622, 1);
 x_1868 = x_1622;
} else {
 lean_dec_ref(x_1622);
 x_1868 = lean_box(0);
}
x_1869 = l_Lean_Exception_isRuntime(x_1866);
if (x_1869 == 0)
{
lean_object* x_1870; lean_object* x_1871; 
lean_dec(x_1866);
x_1870 = lean_box(0);
if (lean_is_scalar(x_1868)) {
 x_1871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1871 = x_1868;
 lean_ctor_set_tag(x_1871, 0);
}
lean_ctor_set(x_1871, 0, x_1870);
lean_ctor_set(x_1871, 1, x_1867);
return x_1871;
}
else
{
lean_object* x_1872; 
if (lean_is_scalar(x_1868)) {
 x_1872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1872 = x_1868;
}
lean_ctor_set(x_1872, 0, x_1866);
lean_ctor_set(x_1872, 1, x_1867);
return x_1872;
}
}
}
}
else
{
lean_object* x_1873; lean_object* x_1874; 
lean_dec(x_22);
lean_dec(x_16);
x_1873 = lean_ctor_get(x_1612, 1);
lean_inc(x_1873);
lean_dec(x_1612);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1874 = l_Lean_Meta_isMonad_x3f(x_35, x_3, x_4, x_5, x_6, x_1873);
if (lean_obj_tag(x_1874) == 0)
{
lean_object* x_1875; 
x_1875 = lean_ctor_get(x_1874, 0);
lean_inc(x_1875);
if (lean_obj_tag(x_1875) == 0)
{
lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; 
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1876 = lean_ctor_get(x_1874, 1);
lean_inc(x_1876);
if (lean_is_exclusive(x_1874)) {
 lean_ctor_release(x_1874, 0);
 lean_ctor_release(x_1874, 1);
 x_1877 = x_1874;
} else {
 lean_dec_ref(x_1874);
 x_1877 = lean_box(0);
}
x_1878 = lean_box(0);
if (lean_is_scalar(x_1877)) {
 x_1879 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1879 = x_1877;
}
lean_ctor_set(x_1879, 0, x_1878);
lean_ctor_set(x_1879, 1, x_1876);
return x_1879;
}
else
{
lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; 
x_1880 = lean_ctor_get(x_1874, 1);
lean_inc(x_1880);
lean_dec(x_1874);
x_1881 = lean_ctor_get(x_1875, 0);
lean_inc(x_1881);
if (lean_is_exclusive(x_1875)) {
 lean_ctor_release(x_1875, 0);
 x_1882 = x_1875;
} else {
 lean_dec_ref(x_1875);
 x_1882 = lean_box(0);
}
if (lean_is_scalar(x_1882)) {
 x_1883 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1883 = x_1882;
}
lean_ctor_set(x_1883, 0, x_1610);
x_1884 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1884, 0, x_1611);
lean_ctor_set(x_25, 0, x_36);
x_1885 = lean_box(0);
x_1886 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1886, 0, x_1881);
x_1887 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1887, 0, x_1);
x_1888 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_1889 = lean_array_push(x_1888, x_1883);
x_1890 = lean_array_push(x_1889, x_1884);
x_1891 = lean_array_push(x_1890, x_25);
x_1892 = lean_array_push(x_1891, x_1885);
x_1893 = lean_array_push(x_1892, x_1886);
x_1894 = lean_array_push(x_1893, x_1887);
x_1895 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1896 = l_Lean_Meta_mkAppOptM(x_1895, x_1894, x_3, x_4, x_5, x_6, x_1880);
if (lean_obj_tag(x_1896) == 0)
{
lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; 
x_1897 = lean_ctor_get(x_1896, 0);
lean_inc(x_1897);
x_1898 = lean_ctor_get(x_1896, 1);
lean_inc(x_1898);
lean_dec(x_1896);
x_1899 = l_Lean_Meta_expandCoe(x_1897, x_3, x_4, x_5, x_6, x_1898);
if (lean_obj_tag(x_1899) == 0)
{
lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; 
x_1900 = lean_ctor_get(x_1899, 0);
lean_inc(x_1900);
x_1901 = lean_ctor_get(x_1899, 1);
lean_inc(x_1901);
if (lean_is_exclusive(x_1899)) {
 lean_ctor_release(x_1899, 0);
 lean_ctor_release(x_1899, 1);
 x_1902 = x_1899;
} else {
 lean_dec_ref(x_1899);
 x_1902 = lean_box(0);
}
x_1903 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1903, 0, x_1900);
if (lean_is_scalar(x_1902)) {
 x_1904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1904 = x_1902;
}
lean_ctor_set(x_1904, 0, x_1903);
lean_ctor_set(x_1904, 1, x_1901);
return x_1904;
}
else
{
lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; uint8_t x_1908; 
x_1905 = lean_ctor_get(x_1899, 0);
lean_inc(x_1905);
x_1906 = lean_ctor_get(x_1899, 1);
lean_inc(x_1906);
if (lean_is_exclusive(x_1899)) {
 lean_ctor_release(x_1899, 0);
 lean_ctor_release(x_1899, 1);
 x_1907 = x_1899;
} else {
 lean_dec_ref(x_1899);
 x_1907 = lean_box(0);
}
x_1908 = l_Lean_Exception_isRuntime(x_1905);
if (x_1908 == 0)
{
lean_object* x_1909; 
lean_dec(x_1905);
if (lean_is_scalar(x_1907)) {
 x_1909 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1909 = x_1907;
 lean_ctor_set_tag(x_1909, 0);
}
lean_ctor_set(x_1909, 0, x_1885);
lean_ctor_set(x_1909, 1, x_1906);
return x_1909;
}
else
{
lean_object* x_1910; 
if (lean_is_scalar(x_1907)) {
 x_1910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1910 = x_1907;
}
lean_ctor_set(x_1910, 0, x_1905);
lean_ctor_set(x_1910, 1, x_1906);
return x_1910;
}
}
}
else
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; uint8_t x_1914; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1911 = lean_ctor_get(x_1896, 0);
lean_inc(x_1911);
x_1912 = lean_ctor_get(x_1896, 1);
lean_inc(x_1912);
if (lean_is_exclusive(x_1896)) {
 lean_ctor_release(x_1896, 0);
 lean_ctor_release(x_1896, 1);
 x_1913 = x_1896;
} else {
 lean_dec_ref(x_1896);
 x_1913 = lean_box(0);
}
x_1914 = l_Lean_Exception_isRuntime(x_1911);
if (x_1914 == 0)
{
lean_object* x_1915; 
lean_dec(x_1911);
if (lean_is_scalar(x_1913)) {
 x_1915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1915 = x_1913;
 lean_ctor_set_tag(x_1915, 0);
}
lean_ctor_set(x_1915, 0, x_1885);
lean_ctor_set(x_1915, 1, x_1912);
return x_1915;
}
else
{
lean_object* x_1916; 
if (lean_is_scalar(x_1913)) {
 x_1916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1916 = x_1913;
}
lean_ctor_set(x_1916, 0, x_1911);
lean_ctor_set(x_1916, 1, x_1912);
return x_1916;
}
}
}
}
else
{
lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; 
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1917 = lean_ctor_get(x_1874, 0);
lean_inc(x_1917);
x_1918 = lean_ctor_get(x_1874, 1);
lean_inc(x_1918);
if (lean_is_exclusive(x_1874)) {
 lean_ctor_release(x_1874, 0);
 lean_ctor_release(x_1874, 1);
 x_1919 = x_1874;
} else {
 lean_dec_ref(x_1874);
 x_1919 = lean_box(0);
}
if (lean_is_scalar(x_1919)) {
 x_1920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1920 = x_1919;
}
lean_ctor_set(x_1920, 0, x_1917);
lean_ctor_set(x_1920, 1, x_1918);
return x_1920;
}
}
}
else
{
lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; 
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1921 = lean_ctor_get(x_1612, 0);
lean_inc(x_1921);
x_1922 = lean_ctor_get(x_1612, 1);
lean_inc(x_1922);
if (lean_is_exclusive(x_1612)) {
 lean_ctor_release(x_1612, 0);
 lean_ctor_release(x_1612, 1);
 x_1923 = x_1612;
} else {
 lean_dec_ref(x_1612);
 x_1923 = lean_box(0);
}
if (lean_is_scalar(x_1923)) {
 x_1924 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1924 = x_1923;
}
lean_ctor_set(x_1924, 0, x_1921);
lean_ctor_set(x_1924, 1, x_1922);
return x_1924;
}
}
}
}
else
{
uint8_t x_1925; 
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1925 = !lean_is_exclusive(x_37);
if (x_1925 == 0)
{
return x_37;
}
else
{
lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; 
x_1926 = lean_ctor_get(x_37, 0);
x_1927 = lean_ctor_get(x_37, 1);
lean_inc(x_1927);
lean_inc(x_1926);
lean_dec(x_37);
x_1928 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1928, 0, x_1926);
lean_ctor_set(x_1928, 1, x_1927);
return x_1928;
}
}
}
else
{
lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; 
x_1929 = lean_ctor_get(x_25, 0);
lean_inc(x_1929);
lean_dec(x_25);
x_1930 = lean_ctor_get(x_24, 1);
lean_inc(x_1930);
lean_dec(x_24);
x_1931 = lean_ctor_get(x_1929, 0);
lean_inc(x_1931);
x_1932 = lean_ctor_get(x_1929, 1);
lean_inc(x_1932);
lean_dec(x_1929);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
x_1933 = l_Lean_Meta_isTypeApp_x3f(x_22, x_3, x_4, x_5, x_6, x_1930);
if (lean_obj_tag(x_1933) == 0)
{
lean_object* x_1934; 
x_1934 = lean_ctor_get(x_1933, 0);
lean_inc(x_1934);
if (lean_obj_tag(x_1934) == 0)
{
lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; 
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1935 = lean_ctor_get(x_1933, 1);
lean_inc(x_1935);
if (lean_is_exclusive(x_1933)) {
 lean_ctor_release(x_1933, 0);
 lean_ctor_release(x_1933, 1);
 x_1936 = x_1933;
} else {
 lean_dec_ref(x_1933);
 x_1936 = lean_box(0);
}
x_1937 = lean_box(0);
if (lean_is_scalar(x_1936)) {
 x_1938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1938 = x_1936;
}
lean_ctor_set(x_1938, 0, x_1937);
lean_ctor_set(x_1938, 1, x_1935);
return x_1938;
}
else
{
lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; 
x_1939 = lean_ctor_get(x_1934, 0);
lean_inc(x_1939);
if (lean_is_exclusive(x_1934)) {
 lean_ctor_release(x_1934, 0);
 x_1940 = x_1934;
} else {
 lean_dec_ref(x_1934);
 x_1940 = lean_box(0);
}
x_1941 = lean_ctor_get(x_1933, 1);
lean_inc(x_1941);
lean_dec(x_1933);
x_1942 = lean_ctor_get(x_1939, 0);
lean_inc(x_1942);
x_1943 = lean_ctor_get(x_1939, 1);
lean_inc(x_1943);
lean_dec(x_1939);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1931);
lean_inc(x_1942);
x_1944 = l_Lean_Meta_isExprDefEq(x_1942, x_1931, x_3, x_4, x_5, x_6, x_1941);
if (lean_obj_tag(x_1944) == 0)
{
lean_object* x_1945; uint8_t x_1946; 
x_1945 = lean_ctor_get(x_1944, 0);
lean_inc(x_1945);
x_1946 = lean_unbox(x_1945);
lean_dec(x_1945);
if (x_1946 == 0)
{
lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; uint8_t x_1951; 
x_1947 = lean_ctor_get(x_1944, 1);
lean_inc(x_1947);
if (lean_is_exclusive(x_1944)) {
 lean_ctor_release(x_1944, 0);
 lean_ctor_release(x_1944, 1);
 x_1948 = x_1944;
} else {
 lean_dec_ref(x_1944);
 x_1948 = lean_box(0);
}
x_1949 = lean_ctor_get(x_5, 2);
lean_inc(x_1949);
x_1950 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_1951 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1949, x_1950);
lean_dec(x_1949);
if (x_1951 == 0)
{
lean_object* x_1952; lean_object* x_1953; 
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1952 = lean_box(0);
if (lean_is_scalar(x_1948)) {
 x_1953 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1953 = x_1948;
}
lean_ctor_set(x_1953, 0, x_1952);
lean_ctor_set(x_1953, 1, x_1947);
return x_1953;
}
else
{
lean_object* x_1954; 
lean_dec(x_1948);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1942);
x_1954 = lean_infer_type(x_1942, x_3, x_4, x_5, x_6, x_1947);
if (lean_obj_tag(x_1954) == 0)
{
lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; 
x_1955 = lean_ctor_get(x_1954, 0);
lean_inc(x_1955);
x_1956 = lean_ctor_get(x_1954, 1);
lean_inc(x_1956);
lean_dec(x_1954);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1957 = lean_whnf(x_1955, x_3, x_4, x_5, x_6, x_1956);
if (lean_obj_tag(x_1957) == 0)
{
lean_object* x_1958; 
x_1958 = lean_ctor_get(x_1957, 0);
lean_inc(x_1958);
if (lean_obj_tag(x_1958) == 7)
{
lean_object* x_1959; 
x_1959 = lean_ctor_get(x_1958, 1);
lean_inc(x_1959);
if (lean_obj_tag(x_1959) == 3)
{
lean_object* x_1960; 
x_1960 = lean_ctor_get(x_1958, 2);
lean_inc(x_1960);
lean_dec(x_1958);
if (lean_obj_tag(x_1960) == 3)
{
lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; 
x_1961 = lean_ctor_get(x_1957, 1);
lean_inc(x_1961);
lean_dec(x_1957);
x_1962 = lean_ctor_get(x_1959, 0);
lean_inc(x_1962);
lean_dec(x_1959);
x_1963 = lean_ctor_get(x_1960, 0);
lean_inc(x_1963);
lean_dec(x_1960);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1931);
x_1964 = lean_infer_type(x_1931, x_3, x_4, x_5, x_6, x_1961);
if (lean_obj_tag(x_1964) == 0)
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; 
x_1965 = lean_ctor_get(x_1964, 0);
lean_inc(x_1965);
x_1966 = lean_ctor_get(x_1964, 1);
lean_inc(x_1966);
lean_dec(x_1964);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1967 = lean_whnf(x_1965, x_3, x_4, x_5, x_6, x_1966);
if (lean_obj_tag(x_1967) == 0)
{
lean_object* x_1968; 
x_1968 = lean_ctor_get(x_1967, 0);
lean_inc(x_1968);
if (lean_obj_tag(x_1968) == 7)
{
lean_object* x_1969; 
x_1969 = lean_ctor_get(x_1968, 1);
lean_inc(x_1969);
if (lean_obj_tag(x_1969) == 3)
{
lean_object* x_1970; 
x_1970 = lean_ctor_get(x_1968, 2);
lean_inc(x_1970);
lean_dec(x_1968);
if (lean_obj_tag(x_1970) == 3)
{
lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; 
x_1971 = lean_ctor_get(x_1967, 1);
lean_inc(x_1971);
lean_dec(x_1967);
x_1972 = lean_ctor_get(x_1969, 0);
lean_inc(x_1972);
lean_dec(x_1969);
x_1973 = lean_ctor_get(x_1970, 0);
lean_inc(x_1973);
lean_dec(x_1970);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1974 = l_Lean_Meta_decLevel(x_1962, x_3, x_4, x_5, x_6, x_1971);
if (lean_obj_tag(x_1974) == 0)
{
lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; 
x_1975 = lean_ctor_get(x_1974, 0);
lean_inc(x_1975);
x_1976 = lean_ctor_get(x_1974, 1);
lean_inc(x_1976);
lean_dec(x_1974);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1977 = l_Lean_Meta_decLevel(x_1972, x_3, x_4, x_5, x_6, x_1976);
if (lean_obj_tag(x_1977) == 0)
{
lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; uint8_t x_1981; lean_object* x_1982; 
x_1978 = lean_ctor_get(x_1977, 0);
lean_inc(x_1978);
x_1979 = lean_ctor_get(x_1977, 1);
lean_inc(x_1979);
if (lean_is_exclusive(x_1977)) {
 lean_ctor_release(x_1977, 0);
 lean_ctor_release(x_1977, 1);
 x_1980 = x_1977;
} else {
 lean_dec_ref(x_1977);
 x_1980 = lean_box(0);
}
x_1981 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1975);
x_1982 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_1975, x_1978, x_1981, x_3, x_4, x_5, x_6, x_1979);
if (lean_obj_tag(x_1982) == 0)
{
lean_object* x_1983; uint8_t x_1984; 
x_1983 = lean_ctor_get(x_1982, 0);
lean_inc(x_1983);
x_1984 = lean_unbox(x_1983);
lean_dec(x_1983);
if (x_1984 == 0)
{
lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; 
lean_dec(x_1980);
lean_dec(x_1975);
lean_dec(x_1973);
lean_dec(x_1963);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_1987 = lean_box(0);
if (lean_is_scalar(x_1986)) {
 x_1988 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1988 = x_1986;
}
lean_ctor_set(x_1988, 0, x_1987);
lean_ctor_set(x_1988, 1, x_1985);
return x_1988;
}
else
{
lean_object* x_1989; lean_object* x_1990; 
x_1989 = lean_ctor_get(x_1982, 1);
lean_inc(x_1989);
lean_dec(x_1982);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1990 = l_Lean_Meta_decLevel(x_1963, x_3, x_4, x_5, x_6, x_1989);
if (lean_obj_tag(x_1990) == 0)
{
lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; 
x_1991 = lean_ctor_get(x_1990, 0);
lean_inc(x_1991);
x_1992 = lean_ctor_get(x_1990, 1);
lean_inc(x_1992);
if (lean_is_exclusive(x_1990)) {
 lean_ctor_release(x_1990, 0);
 lean_ctor_release(x_1990, 1);
 x_1993 = x_1990;
} else {
 lean_dec_ref(x_1990);
 x_1993 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1994 = l_Lean_Meta_decLevel(x_1973, x_3, x_4, x_5, x_6, x_1992);
if (lean_obj_tag(x_1994) == 0)
{
lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; 
x_1995 = lean_ctor_get(x_1994, 0);
lean_inc(x_1995);
x_1996 = lean_ctor_get(x_1994, 1);
lean_inc(x_1996);
if (lean_is_exclusive(x_1994)) {
 lean_ctor_release(x_1994, 0);
 lean_ctor_release(x_1994, 1);
 x_1997 = x_1994;
} else {
 lean_dec_ref(x_1994);
 x_1997 = lean_box(0);
}
x_1998 = lean_box(0);
if (lean_is_scalar(x_1997)) {
 x_1999 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1999 = x_1997;
 lean_ctor_set_tag(x_1999, 1);
}
lean_ctor_set(x_1999, 0, x_1995);
lean_ctor_set(x_1999, 1, x_1998);
if (lean_is_scalar(x_1993)) {
 x_2000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2000 = x_1993;
 lean_ctor_set_tag(x_2000, 1);
}
lean_ctor_set(x_2000, 0, x_1991);
lean_ctor_set(x_2000, 1, x_1999);
if (lean_is_scalar(x_1980)) {
 x_2001 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2001 = x_1980;
 lean_ctor_set_tag(x_2001, 1);
}
lean_ctor_set(x_2001, 0, x_1975);
lean_ctor_set(x_2001, 1, x_2000);
x_2002 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_2003 = l_Lean_Expr_const___override(x_2002, x_2001);
x_2004 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_1942);
x_2005 = lean_array_push(x_2004, x_1942);
lean_inc(x_1931);
x_2006 = lean_array_push(x_2005, x_1931);
x_2007 = l_Lean_mkAppN(x_2003, x_2006);
x_2008 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2009 = l_Lean_Meta_trySynthInstance(x_2007, x_2008, x_3, x_4, x_5, x_6, x_1996);
if (lean_obj_tag(x_2009) == 0)
{
lean_object* x_2010; 
x_2010 = lean_ctor_get(x_2009, 0);
lean_inc(x_2010);
if (lean_obj_tag(x_2010) == 1)
{
lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; 
x_2011 = lean_ctor_get(x_2009, 1);
lean_inc(x_2011);
lean_dec(x_2009);
x_2012 = lean_ctor_get(x_2010, 0);
lean_inc(x_2012);
lean_dec(x_2010);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1943);
x_2013 = l_Lean_Meta_getDecLevel(x_1943, x_3, x_4, x_5, x_6, x_2011);
if (lean_obj_tag(x_2013) == 0)
{
lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; 
x_2014 = lean_ctor_get(x_2013, 0);
lean_inc(x_2014);
x_2015 = lean_ctor_get(x_2013, 1);
lean_inc(x_2015);
if (lean_is_exclusive(x_2013)) {
 lean_ctor_release(x_2013, 0);
 lean_ctor_release(x_2013, 1);
 x_2016 = x_2013;
} else {
 lean_dec_ref(x_2013);
 x_2016 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2017 = l_Lean_Meta_getDecLevel(x_22, x_3, x_4, x_5, x_6, x_2015);
if (lean_obj_tag(x_2017) == 0)
{
lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; 
x_2018 = lean_ctor_get(x_2017, 0);
lean_inc(x_2018);
x_2019 = lean_ctor_get(x_2017, 1);
lean_inc(x_2019);
if (lean_is_exclusive(x_2017)) {
 lean_ctor_release(x_2017, 0);
 lean_ctor_release(x_2017, 1);
 x_2020 = x_2017;
} else {
 lean_dec_ref(x_2017);
 x_2020 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_2021 = l_Lean_Meta_getDecLevel(x_16, x_3, x_4, x_5, x_6, x_2019);
if (lean_obj_tag(x_2021) == 0)
{
lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; 
x_2022 = lean_ctor_get(x_2021, 0);
lean_inc(x_2022);
x_2023 = lean_ctor_get(x_2021, 1);
lean_inc(x_2023);
if (lean_is_exclusive(x_2021)) {
 lean_ctor_release(x_2021, 0);
 lean_ctor_release(x_2021, 1);
 x_2024 = x_2021;
} else {
 lean_dec_ref(x_2021);
 x_2024 = lean_box(0);
}
if (lean_is_scalar(x_2024)) {
 x_2025 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2025 = x_2024;
 lean_ctor_set_tag(x_2025, 1);
}
lean_ctor_set(x_2025, 0, x_2022);
lean_ctor_set(x_2025, 1, x_1998);
if (lean_is_scalar(x_2020)) {
 x_2026 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2026 = x_2020;
 lean_ctor_set_tag(x_2026, 1);
}
lean_ctor_set(x_2026, 0, x_2018);
lean_ctor_set(x_2026, 1, x_2025);
if (lean_is_scalar(x_2016)) {
 x_2027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2027 = x_2016;
 lean_ctor_set_tag(x_2027, 1);
}
lean_ctor_set(x_2027, 0, x_2014);
lean_ctor_set(x_2027, 1, x_2026);
x_2028 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_2027);
x_2029 = l_Lean_Expr_const___override(x_2028, x_2027);
x_2030 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_1942);
x_2031 = lean_array_push(x_2030, x_1942);
lean_inc(x_1931);
x_2032 = lean_array_push(x_2031, x_1931);
lean_inc(x_2012);
x_2033 = lean_array_push(x_2032, x_2012);
lean_inc(x_1943);
x_2034 = lean_array_push(x_2033, x_1943);
lean_inc(x_1);
x_2035 = lean_array_push(x_2034, x_1);
x_2036 = l_Lean_mkAppN(x_2029, x_2035);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2036);
x_2037 = lean_infer_type(x_2036, x_3, x_4, x_5, x_6, x_2023);
if (lean_obj_tag(x_2037) == 0)
{
lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; 
x_2038 = lean_ctor_get(x_2037, 0);
lean_inc(x_2038);
x_2039 = lean_ctor_get(x_2037, 1);
lean_inc(x_2039);
lean_dec(x_2037);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_2040 = l_Lean_Meta_isExprDefEq(x_16, x_2038, x_3, x_4, x_5, x_6, x_2039);
if (lean_obj_tag(x_2040) == 0)
{
lean_object* x_2041; uint8_t x_2042; 
x_2041 = lean_ctor_get(x_2040, 0);
lean_inc(x_2041);
x_2042 = lean_unbox(x_2041);
lean_dec(x_2041);
if (x_2042 == 0)
{
lean_object* x_2043; lean_object* x_2044; 
lean_dec(x_2036);
lean_dec(x_1940);
x_2043 = lean_ctor_get(x_2040, 1);
lean_inc(x_2043);
lean_dec(x_2040);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1931);
x_2044 = l_Lean_Meta_isMonad_x3f(x_1931, x_3, x_4, x_5, x_6, x_2043);
if (lean_obj_tag(x_2044) == 0)
{
lean_object* x_2045; 
x_2045 = lean_ctor_get(x_2044, 0);
lean_inc(x_2045);
if (lean_obj_tag(x_2045) == 0)
{
lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; 
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2046 = lean_ctor_get(x_2044, 1);
lean_inc(x_2046);
if (lean_is_exclusive(x_2044)) {
 lean_ctor_release(x_2044, 0);
 lean_ctor_release(x_2044, 1);
 x_2047 = x_2044;
} else {
 lean_dec_ref(x_2044);
 x_2047 = lean_box(0);
}
if (lean_is_scalar(x_2047)) {
 x_2048 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2048 = x_2047;
}
lean_ctor_set(x_2048, 0, x_2008);
lean_ctor_set(x_2048, 1, x_2046);
return x_2048;
}
else
{
lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; 
x_2049 = lean_ctor_get(x_2044, 1);
lean_inc(x_2049);
lean_dec(x_2044);
x_2050 = lean_ctor_get(x_2045, 0);
lean_inc(x_2050);
lean_dec(x_2045);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1943);
x_2051 = l_Lean_Meta_getLevel(x_1943, x_3, x_4, x_5, x_6, x_2049);
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
lean_inc(x_1932);
x_2055 = l_Lean_Meta_getLevel(x_1932, x_3, x_4, x_5, x_6, x_2053);
if (lean_obj_tag(x_2055) == 0)
{
lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; uint8_t x_2070; lean_object* x_2071; lean_object* x_2072; 
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
if (lean_is_scalar(x_2058)) {
 x_2059 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2059 = x_2058;
 lean_ctor_set_tag(x_2059, 1);
}
lean_ctor_set(x_2059, 0, x_2056);
lean_ctor_set(x_2059, 1, x_1998);
if (lean_is_scalar(x_2054)) {
 x_2060 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2060 = x_2054;
 lean_ctor_set_tag(x_2060, 1);
}
lean_ctor_set(x_2060, 0, x_2052);
lean_ctor_set(x_2060, 1, x_2059);
x_2061 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_2062 = l_Lean_Expr_const___override(x_2061, x_2060);
x_2063 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_1943);
x_2064 = lean_array_push(x_2063, x_1943);
x_2065 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_2066 = lean_array_push(x_2064, x_2065);
lean_inc(x_1932);
x_2067 = lean_array_push(x_2066, x_1932);
x_2068 = l_Lean_mkAppN(x_2062, x_2067);
x_2069 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_2070 = 0;
lean_inc(x_1943);
x_2071 = l_Lean_Expr_forallE___override(x_2069, x_1943, x_2068, x_2070);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2072 = l_Lean_Meta_trySynthInstance(x_2071, x_2008, x_3, x_4, x_5, x_6, x_2057);
if (lean_obj_tag(x_2072) == 0)
{
lean_object* x_2073; 
x_2073 = lean_ctor_get(x_2072, 0);
lean_inc(x_2073);
if (lean_obj_tag(x_2073) == 1)
{
lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; 
x_2074 = lean_ctor_get(x_2072, 1);
lean_inc(x_2074);
lean_dec(x_2072);
x_2075 = lean_ctor_get(x_2073, 0);
lean_inc(x_2075);
lean_dec(x_2073);
x_2076 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_2077 = l_Lean_Expr_const___override(x_2076, x_2027);
x_2078 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_2079 = lean_array_push(x_2078, x_1942);
x_2080 = lean_array_push(x_2079, x_1931);
x_2081 = lean_array_push(x_2080, x_1943);
x_2082 = lean_array_push(x_2081, x_1932);
x_2083 = lean_array_push(x_2082, x_2012);
x_2084 = lean_array_push(x_2083, x_2075);
x_2085 = lean_array_push(x_2084, x_2050);
x_2086 = lean_array_push(x_2085, x_1);
x_2087 = l_Lean_mkAppN(x_2077, x_2086);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2088 = l_Lean_Meta_expandCoe(x_2087, x_3, x_4, x_5, x_6, x_2074);
if (lean_obj_tag(x_2088) == 0)
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; 
x_2089 = lean_ctor_get(x_2088, 0);
lean_inc(x_2089);
x_2090 = lean_ctor_get(x_2088, 1);
lean_inc(x_2090);
lean_dec(x_2088);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2089);
x_2091 = lean_infer_type(x_2089, x_3, x_4, x_5, x_6, x_2090);
if (lean_obj_tag(x_2091) == 0)
{
lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; 
x_2092 = lean_ctor_get(x_2091, 0);
lean_inc(x_2092);
x_2093 = lean_ctor_get(x_2091, 1);
lean_inc(x_2093);
lean_dec(x_2091);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2094 = l_Lean_Meta_isExprDefEq(x_16, x_2092, x_3, x_4, x_5, x_6, x_2093);
if (lean_obj_tag(x_2094) == 0)
{
lean_object* x_2095; uint8_t x_2096; 
x_2095 = lean_ctor_get(x_2094, 0);
lean_inc(x_2095);
x_2096 = lean_unbox(x_2095);
lean_dec(x_2095);
if (x_2096 == 0)
{
lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; 
lean_dec(x_2089);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2097 = lean_ctor_get(x_2094, 1);
lean_inc(x_2097);
if (lean_is_exclusive(x_2094)) {
 lean_ctor_release(x_2094, 0);
 lean_ctor_release(x_2094, 1);
 x_2098 = x_2094;
} else {
 lean_dec_ref(x_2094);
 x_2098 = lean_box(0);
}
if (lean_is_scalar(x_2098)) {
 x_2099 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2099 = x_2098;
}
lean_ctor_set(x_2099, 0, x_2008);
lean_ctor_set(x_2099, 1, x_2097);
return x_2099;
}
else
{
lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; 
x_2100 = lean_ctor_get(x_2094, 1);
lean_inc(x_2100);
lean_dec(x_2094);
x_2101 = lean_box(0);
x_2102 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_2089, x_2101, x_3, x_4, x_5, x_6, x_2100);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2103 = lean_ctor_get(x_2102, 0);
lean_inc(x_2103);
x_2104 = lean_ctor_get(x_2102, 1);
lean_inc(x_2104);
if (lean_is_exclusive(x_2102)) {
 lean_ctor_release(x_2102, 0);
 lean_ctor_release(x_2102, 1);
 x_2105 = x_2102;
} else {
 lean_dec_ref(x_2102);
 x_2105 = lean_box(0);
}
if (lean_is_scalar(x_2105)) {
 x_2106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2106 = x_2105;
}
lean_ctor_set(x_2106, 0, x_2103);
lean_ctor_set(x_2106, 1, x_2104);
return x_2106;
}
}
else
{
lean_object* x_2107; lean_object* x_2108; 
lean_dec(x_2089);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2107 = lean_ctor_get(x_2094, 0);
lean_inc(x_2107);
x_2108 = lean_ctor_get(x_2094, 1);
lean_inc(x_2108);
lean_dec(x_2094);
x_8 = x_2107;
x_9 = x_2108;
goto block_14;
}
}
else
{
lean_object* x_2109; lean_object* x_2110; 
lean_dec(x_2089);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2109 = lean_ctor_get(x_2091, 0);
lean_inc(x_2109);
x_2110 = lean_ctor_get(x_2091, 1);
lean_inc(x_2110);
lean_dec(x_2091);
x_8 = x_2109;
x_9 = x_2110;
goto block_14;
}
}
else
{
lean_object* x_2111; lean_object* x_2112; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2111 = lean_ctor_get(x_2088, 0);
lean_inc(x_2111);
x_2112 = lean_ctor_get(x_2088, 1);
lean_inc(x_2112);
lean_dec(x_2088);
x_8 = x_2111;
x_9 = x_2112;
goto block_14;
}
}
else
{
lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; 
lean_dec(x_2073);
lean_dec(x_2050);
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2113 = lean_ctor_get(x_2072, 1);
lean_inc(x_2113);
if (lean_is_exclusive(x_2072)) {
 lean_ctor_release(x_2072, 0);
 lean_ctor_release(x_2072, 1);
 x_2114 = x_2072;
} else {
 lean_dec_ref(x_2072);
 x_2114 = lean_box(0);
}
if (lean_is_scalar(x_2114)) {
 x_2115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2115 = x_2114;
}
lean_ctor_set(x_2115, 0, x_2008);
lean_ctor_set(x_2115, 1, x_2113);
return x_2115;
}
}
else
{
lean_object* x_2116; lean_object* x_2117; 
lean_dec(x_2050);
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2116 = lean_ctor_get(x_2072, 0);
lean_inc(x_2116);
x_2117 = lean_ctor_get(x_2072, 1);
lean_inc(x_2117);
lean_dec(x_2072);
x_8 = x_2116;
x_9 = x_2117;
goto block_14;
}
}
else
{
lean_object* x_2118; lean_object* x_2119; 
lean_dec(x_2054);
lean_dec(x_2052);
lean_dec(x_2050);
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2118 = lean_ctor_get(x_2055, 0);
lean_inc(x_2118);
x_2119 = lean_ctor_get(x_2055, 1);
lean_inc(x_2119);
lean_dec(x_2055);
x_8 = x_2118;
x_9 = x_2119;
goto block_14;
}
}
else
{
lean_object* x_2120; lean_object* x_2121; 
lean_dec(x_2050);
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2120 = lean_ctor_get(x_2051, 0);
lean_inc(x_2120);
x_2121 = lean_ctor_get(x_2051, 1);
lean_inc(x_2121);
lean_dec(x_2051);
x_8 = x_2120;
x_9 = x_2121;
goto block_14;
}
}
}
else
{
lean_object* x_2122; lean_object* x_2123; 
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2122 = lean_ctor_get(x_2044, 0);
lean_inc(x_2122);
x_2123 = lean_ctor_get(x_2044, 1);
lean_inc(x_2123);
lean_dec(x_2044);
x_8 = x_2122;
x_9 = x_2123;
goto block_14;
}
}
else
{
lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; 
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2124 = lean_ctor_get(x_2040, 1);
lean_inc(x_2124);
if (lean_is_exclusive(x_2040)) {
 lean_ctor_release(x_2040, 0);
 lean_ctor_release(x_2040, 1);
 x_2125 = x_2040;
} else {
 lean_dec_ref(x_2040);
 x_2125 = lean_box(0);
}
if (lean_is_scalar(x_1940)) {
 x_2126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2126 = x_1940;
}
lean_ctor_set(x_2126, 0, x_2036);
if (lean_is_scalar(x_2125)) {
 x_2127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2127 = x_2125;
}
lean_ctor_set(x_2127, 0, x_2126);
lean_ctor_set(x_2127, 1, x_2124);
return x_2127;
}
}
else
{
lean_object* x_2128; lean_object* x_2129; 
lean_dec(x_2036);
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2128 = lean_ctor_get(x_2040, 0);
lean_inc(x_2128);
x_2129 = lean_ctor_get(x_2040, 1);
lean_inc(x_2129);
lean_dec(x_2040);
x_8 = x_2128;
x_9 = x_2129;
goto block_14;
}
}
else
{
lean_object* x_2130; lean_object* x_2131; 
lean_dec(x_2036);
lean_dec(x_2027);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2130 = lean_ctor_get(x_2037, 0);
lean_inc(x_2130);
x_2131 = lean_ctor_get(x_2037, 1);
lean_inc(x_2131);
lean_dec(x_2037);
x_8 = x_2130;
x_9 = x_2131;
goto block_14;
}
}
else
{
lean_object* x_2132; lean_object* x_2133; 
lean_dec(x_2020);
lean_dec(x_2018);
lean_dec(x_2016);
lean_dec(x_2014);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2132 = lean_ctor_get(x_2021, 0);
lean_inc(x_2132);
x_2133 = lean_ctor_get(x_2021, 1);
lean_inc(x_2133);
lean_dec(x_2021);
x_8 = x_2132;
x_9 = x_2133;
goto block_14;
}
}
else
{
lean_object* x_2134; lean_object* x_2135; 
lean_dec(x_2016);
lean_dec(x_2014);
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2134 = lean_ctor_get(x_2017, 0);
lean_inc(x_2134);
x_2135 = lean_ctor_get(x_2017, 1);
lean_inc(x_2135);
lean_dec(x_2017);
x_8 = x_2134;
x_9 = x_2135;
goto block_14;
}
}
else
{
lean_object* x_2136; lean_object* x_2137; 
lean_dec(x_2012);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2136 = lean_ctor_get(x_2013, 0);
lean_inc(x_2136);
x_2137 = lean_ctor_get(x_2013, 1);
lean_inc(x_2137);
lean_dec(x_2013);
x_8 = x_2136;
x_9 = x_2137;
goto block_14;
}
}
else
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; 
lean_dec(x_2010);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2138 = lean_ctor_get(x_2009, 1);
lean_inc(x_2138);
if (lean_is_exclusive(x_2009)) {
 lean_ctor_release(x_2009, 0);
 lean_ctor_release(x_2009, 1);
 x_2139 = x_2009;
} else {
 lean_dec_ref(x_2009);
 x_2139 = lean_box(0);
}
if (lean_is_scalar(x_2139)) {
 x_2140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2140 = x_2139;
}
lean_ctor_set(x_2140, 0, x_2008);
lean_ctor_set(x_2140, 1, x_2138);
return x_2140;
}
}
else
{
lean_object* x_2141; lean_object* x_2142; 
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2141 = lean_ctor_get(x_2009, 0);
lean_inc(x_2141);
x_2142 = lean_ctor_get(x_2009, 1);
lean_inc(x_2142);
lean_dec(x_2009);
x_8 = x_2141;
x_9 = x_2142;
goto block_14;
}
}
else
{
lean_object* x_2143; lean_object* x_2144; 
lean_dec(x_1993);
lean_dec(x_1991);
lean_dec(x_1980);
lean_dec(x_1975);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2143 = lean_ctor_get(x_1994, 0);
lean_inc(x_2143);
x_2144 = lean_ctor_get(x_1994, 1);
lean_inc(x_2144);
lean_dec(x_1994);
x_8 = x_2143;
x_9 = x_2144;
goto block_14;
}
}
else
{
lean_object* x_2145; lean_object* x_2146; 
lean_dec(x_1980);
lean_dec(x_1975);
lean_dec(x_1973);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2145 = lean_ctor_get(x_1990, 0);
lean_inc(x_2145);
x_2146 = lean_ctor_get(x_1990, 1);
lean_inc(x_2146);
lean_dec(x_1990);
x_8 = x_2145;
x_9 = x_2146;
goto block_14;
}
}
}
else
{
lean_object* x_2147; lean_object* x_2148; 
lean_dec(x_1980);
lean_dec(x_1975);
lean_dec(x_1973);
lean_dec(x_1963);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2147 = lean_ctor_get(x_1982, 0);
lean_inc(x_2147);
x_2148 = lean_ctor_get(x_1982, 1);
lean_inc(x_2148);
lean_dec(x_1982);
x_8 = x_2147;
x_9 = x_2148;
goto block_14;
}
}
else
{
lean_object* x_2149; lean_object* x_2150; 
lean_dec(x_1975);
lean_dec(x_1973);
lean_dec(x_1963);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2149 = lean_ctor_get(x_1977, 0);
lean_inc(x_2149);
x_2150 = lean_ctor_get(x_1977, 1);
lean_inc(x_2150);
lean_dec(x_1977);
x_8 = x_2149;
x_9 = x_2150;
goto block_14;
}
}
else
{
lean_object* x_2151; lean_object* x_2152; 
lean_dec(x_1973);
lean_dec(x_1972);
lean_dec(x_1963);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2151 = lean_ctor_get(x_1974, 0);
lean_inc(x_2151);
x_2152 = lean_ctor_get(x_1974, 1);
lean_inc(x_2152);
lean_dec(x_1974);
x_8 = x_2151;
x_9 = x_2152;
goto block_14;
}
}
else
{
lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; 
lean_dec(x_1970);
lean_dec(x_1969);
lean_dec(x_1963);
lean_dec(x_1962);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2153 = lean_ctor_get(x_1967, 1);
lean_inc(x_2153);
if (lean_is_exclusive(x_1967)) {
 lean_ctor_release(x_1967, 0);
 lean_ctor_release(x_1967, 1);
 x_2154 = x_1967;
} else {
 lean_dec_ref(x_1967);
 x_2154 = lean_box(0);
}
x_2155 = lean_box(0);
if (lean_is_scalar(x_2154)) {
 x_2156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2156 = x_2154;
}
lean_ctor_set(x_2156, 0, x_2155);
lean_ctor_set(x_2156, 1, x_2153);
return x_2156;
}
}
else
{
lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; 
lean_dec(x_1969);
lean_dec(x_1968);
lean_dec(x_1963);
lean_dec(x_1962);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2157 = lean_ctor_get(x_1967, 1);
lean_inc(x_2157);
if (lean_is_exclusive(x_1967)) {
 lean_ctor_release(x_1967, 0);
 lean_ctor_release(x_1967, 1);
 x_2158 = x_1967;
} else {
 lean_dec_ref(x_1967);
 x_2158 = lean_box(0);
}
x_2159 = lean_box(0);
if (lean_is_scalar(x_2158)) {
 x_2160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2160 = x_2158;
}
lean_ctor_set(x_2160, 0, x_2159);
lean_ctor_set(x_2160, 1, x_2157);
return x_2160;
}
}
else
{
lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; 
lean_dec(x_1968);
lean_dec(x_1963);
lean_dec(x_1962);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2161 = lean_ctor_get(x_1967, 1);
lean_inc(x_2161);
if (lean_is_exclusive(x_1967)) {
 lean_ctor_release(x_1967, 0);
 lean_ctor_release(x_1967, 1);
 x_2162 = x_1967;
} else {
 lean_dec_ref(x_1967);
 x_2162 = lean_box(0);
}
x_2163 = lean_box(0);
if (lean_is_scalar(x_2162)) {
 x_2164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2164 = x_2162;
}
lean_ctor_set(x_2164, 0, x_2163);
lean_ctor_set(x_2164, 1, x_2161);
return x_2164;
}
}
else
{
lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; uint8_t x_2168; 
lean_dec(x_1963);
lean_dec(x_1962);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2165 = lean_ctor_get(x_1967, 0);
lean_inc(x_2165);
x_2166 = lean_ctor_get(x_1967, 1);
lean_inc(x_2166);
if (lean_is_exclusive(x_1967)) {
 lean_ctor_release(x_1967, 0);
 lean_ctor_release(x_1967, 1);
 x_2167 = x_1967;
} else {
 lean_dec_ref(x_1967);
 x_2167 = lean_box(0);
}
x_2168 = l_Lean_Exception_isRuntime(x_2165);
if (x_2168 == 0)
{
lean_object* x_2169; lean_object* x_2170; 
lean_dec(x_2165);
x_2169 = lean_box(0);
if (lean_is_scalar(x_2167)) {
 x_2170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2170 = x_2167;
 lean_ctor_set_tag(x_2170, 0);
}
lean_ctor_set(x_2170, 0, x_2169);
lean_ctor_set(x_2170, 1, x_2166);
return x_2170;
}
else
{
lean_object* x_2171; 
if (lean_is_scalar(x_2167)) {
 x_2171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2171 = x_2167;
}
lean_ctor_set(x_2171, 0, x_2165);
lean_ctor_set(x_2171, 1, x_2166);
return x_2171;
}
}
}
else
{
lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; uint8_t x_2175; 
lean_dec(x_1963);
lean_dec(x_1962);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2172 = lean_ctor_get(x_1964, 0);
lean_inc(x_2172);
x_2173 = lean_ctor_get(x_1964, 1);
lean_inc(x_2173);
if (lean_is_exclusive(x_1964)) {
 lean_ctor_release(x_1964, 0);
 lean_ctor_release(x_1964, 1);
 x_2174 = x_1964;
} else {
 lean_dec_ref(x_1964);
 x_2174 = lean_box(0);
}
x_2175 = l_Lean_Exception_isRuntime(x_2172);
if (x_2175 == 0)
{
lean_object* x_2176; lean_object* x_2177; 
lean_dec(x_2172);
x_2176 = lean_box(0);
if (lean_is_scalar(x_2174)) {
 x_2177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2177 = x_2174;
 lean_ctor_set_tag(x_2177, 0);
}
lean_ctor_set(x_2177, 0, x_2176);
lean_ctor_set(x_2177, 1, x_2173);
return x_2177;
}
else
{
lean_object* x_2178; 
if (lean_is_scalar(x_2174)) {
 x_2178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2178 = x_2174;
}
lean_ctor_set(x_2178, 0, x_2172);
lean_ctor_set(x_2178, 1, x_2173);
return x_2178;
}
}
}
else
{
lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; 
lean_dec(x_1960);
lean_dec(x_1959);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2179 = lean_ctor_get(x_1957, 1);
lean_inc(x_2179);
if (lean_is_exclusive(x_1957)) {
 lean_ctor_release(x_1957, 0);
 lean_ctor_release(x_1957, 1);
 x_2180 = x_1957;
} else {
 lean_dec_ref(x_1957);
 x_2180 = lean_box(0);
}
x_2181 = lean_box(0);
if (lean_is_scalar(x_2180)) {
 x_2182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2182 = x_2180;
}
lean_ctor_set(x_2182, 0, x_2181);
lean_ctor_set(x_2182, 1, x_2179);
return x_2182;
}
}
else
{
lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; 
lean_dec(x_1959);
lean_dec(x_1958);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2183 = lean_ctor_get(x_1957, 1);
lean_inc(x_2183);
if (lean_is_exclusive(x_1957)) {
 lean_ctor_release(x_1957, 0);
 lean_ctor_release(x_1957, 1);
 x_2184 = x_1957;
} else {
 lean_dec_ref(x_1957);
 x_2184 = lean_box(0);
}
x_2185 = lean_box(0);
if (lean_is_scalar(x_2184)) {
 x_2186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2186 = x_2184;
}
lean_ctor_set(x_2186, 0, x_2185);
lean_ctor_set(x_2186, 1, x_2183);
return x_2186;
}
}
else
{
lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; 
lean_dec(x_1958);
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2187 = lean_ctor_get(x_1957, 1);
lean_inc(x_2187);
if (lean_is_exclusive(x_1957)) {
 lean_ctor_release(x_1957, 0);
 lean_ctor_release(x_1957, 1);
 x_2188 = x_1957;
} else {
 lean_dec_ref(x_1957);
 x_2188 = lean_box(0);
}
x_2189 = lean_box(0);
if (lean_is_scalar(x_2188)) {
 x_2190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2190 = x_2188;
}
lean_ctor_set(x_2190, 0, x_2189);
lean_ctor_set(x_2190, 1, x_2187);
return x_2190;
}
}
else
{
lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; uint8_t x_2194; 
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2191 = lean_ctor_get(x_1957, 0);
lean_inc(x_2191);
x_2192 = lean_ctor_get(x_1957, 1);
lean_inc(x_2192);
if (lean_is_exclusive(x_1957)) {
 lean_ctor_release(x_1957, 0);
 lean_ctor_release(x_1957, 1);
 x_2193 = x_1957;
} else {
 lean_dec_ref(x_1957);
 x_2193 = lean_box(0);
}
x_2194 = l_Lean_Exception_isRuntime(x_2191);
if (x_2194 == 0)
{
lean_object* x_2195; lean_object* x_2196; 
lean_dec(x_2191);
x_2195 = lean_box(0);
if (lean_is_scalar(x_2193)) {
 x_2196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2196 = x_2193;
 lean_ctor_set_tag(x_2196, 0);
}
lean_ctor_set(x_2196, 0, x_2195);
lean_ctor_set(x_2196, 1, x_2192);
return x_2196;
}
else
{
lean_object* x_2197; 
if (lean_is_scalar(x_2193)) {
 x_2197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2197 = x_2193;
}
lean_ctor_set(x_2197, 0, x_2191);
lean_ctor_set(x_2197, 1, x_2192);
return x_2197;
}
}
}
else
{
lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; uint8_t x_2201; 
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2198 = lean_ctor_get(x_1954, 0);
lean_inc(x_2198);
x_2199 = lean_ctor_get(x_1954, 1);
lean_inc(x_2199);
if (lean_is_exclusive(x_1954)) {
 lean_ctor_release(x_1954, 0);
 lean_ctor_release(x_1954, 1);
 x_2200 = x_1954;
} else {
 lean_dec_ref(x_1954);
 x_2200 = lean_box(0);
}
x_2201 = l_Lean_Exception_isRuntime(x_2198);
if (x_2201 == 0)
{
lean_object* x_2202; lean_object* x_2203; 
lean_dec(x_2198);
x_2202 = lean_box(0);
if (lean_is_scalar(x_2200)) {
 x_2203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2203 = x_2200;
 lean_ctor_set_tag(x_2203, 0);
}
lean_ctor_set(x_2203, 0, x_2202);
lean_ctor_set(x_2203, 1, x_2199);
return x_2203;
}
else
{
lean_object* x_2204; 
if (lean_is_scalar(x_2200)) {
 x_2204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2204 = x_2200;
}
lean_ctor_set(x_2204, 0, x_2198);
lean_ctor_set(x_2204, 1, x_2199);
return x_2204;
}
}
}
}
else
{
lean_object* x_2205; lean_object* x_2206; 
lean_dec(x_22);
lean_dec(x_16);
x_2205 = lean_ctor_get(x_1944, 1);
lean_inc(x_2205);
lean_dec(x_1944);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2206 = l_Lean_Meta_isMonad_x3f(x_1931, x_3, x_4, x_5, x_6, x_2205);
if (lean_obj_tag(x_2206) == 0)
{
lean_object* x_2207; 
x_2207 = lean_ctor_get(x_2206, 0);
lean_inc(x_2207);
if (lean_obj_tag(x_2207) == 0)
{
lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; 
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2208 = lean_ctor_get(x_2206, 1);
lean_inc(x_2208);
if (lean_is_exclusive(x_2206)) {
 lean_ctor_release(x_2206, 0);
 lean_ctor_release(x_2206, 1);
 x_2209 = x_2206;
} else {
 lean_dec_ref(x_2206);
 x_2209 = lean_box(0);
}
x_2210 = lean_box(0);
if (lean_is_scalar(x_2209)) {
 x_2211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2211 = x_2209;
}
lean_ctor_set(x_2211, 0, x_2210);
lean_ctor_set(x_2211, 1, x_2208);
return x_2211;
}
else
{
lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; 
x_2212 = lean_ctor_get(x_2206, 1);
lean_inc(x_2212);
lean_dec(x_2206);
x_2213 = lean_ctor_get(x_2207, 0);
lean_inc(x_2213);
if (lean_is_exclusive(x_2207)) {
 lean_ctor_release(x_2207, 0);
 x_2214 = x_2207;
} else {
 lean_dec_ref(x_2207);
 x_2214 = lean_box(0);
}
if (lean_is_scalar(x_2214)) {
 x_2215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2215 = x_2214;
}
lean_ctor_set(x_2215, 0, x_1942);
if (lean_is_scalar(x_1940)) {
 x_2216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2216 = x_1940;
}
lean_ctor_set(x_2216, 0, x_1943);
x_2217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2217, 0, x_1932);
x_2218 = lean_box(0);
x_2219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2219, 0, x_2213);
x_2220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2220, 0, x_1);
x_2221 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_2222 = lean_array_push(x_2221, x_2215);
x_2223 = lean_array_push(x_2222, x_2216);
x_2224 = lean_array_push(x_2223, x_2217);
x_2225 = lean_array_push(x_2224, x_2218);
x_2226 = lean_array_push(x_2225, x_2219);
x_2227 = lean_array_push(x_2226, x_2220);
x_2228 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2229 = l_Lean_Meta_mkAppOptM(x_2228, x_2227, x_3, x_4, x_5, x_6, x_2212);
if (lean_obj_tag(x_2229) == 0)
{
lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; 
x_2230 = lean_ctor_get(x_2229, 0);
lean_inc(x_2230);
x_2231 = lean_ctor_get(x_2229, 1);
lean_inc(x_2231);
lean_dec(x_2229);
x_2232 = l_Lean_Meta_expandCoe(x_2230, x_3, x_4, x_5, x_6, x_2231);
if (lean_obj_tag(x_2232) == 0)
{
lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; 
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
x_2236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2236, 0, x_2233);
if (lean_is_scalar(x_2235)) {
 x_2237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2237 = x_2235;
}
lean_ctor_set(x_2237, 0, x_2236);
lean_ctor_set(x_2237, 1, x_2234);
return x_2237;
}
else
{
lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; uint8_t x_2241; 
x_2238 = lean_ctor_get(x_2232, 0);
lean_inc(x_2238);
x_2239 = lean_ctor_get(x_2232, 1);
lean_inc(x_2239);
if (lean_is_exclusive(x_2232)) {
 lean_ctor_release(x_2232, 0);
 lean_ctor_release(x_2232, 1);
 x_2240 = x_2232;
} else {
 lean_dec_ref(x_2232);
 x_2240 = lean_box(0);
}
x_2241 = l_Lean_Exception_isRuntime(x_2238);
if (x_2241 == 0)
{
lean_object* x_2242; 
lean_dec(x_2238);
if (lean_is_scalar(x_2240)) {
 x_2242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2242 = x_2240;
 lean_ctor_set_tag(x_2242, 0);
}
lean_ctor_set(x_2242, 0, x_2218);
lean_ctor_set(x_2242, 1, x_2239);
return x_2242;
}
else
{
lean_object* x_2243; 
if (lean_is_scalar(x_2240)) {
 x_2243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2243 = x_2240;
}
lean_ctor_set(x_2243, 0, x_2238);
lean_ctor_set(x_2243, 1, x_2239);
return x_2243;
}
}
}
else
{
lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; uint8_t x_2247; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2244 = lean_ctor_get(x_2229, 0);
lean_inc(x_2244);
x_2245 = lean_ctor_get(x_2229, 1);
lean_inc(x_2245);
if (lean_is_exclusive(x_2229)) {
 lean_ctor_release(x_2229, 0);
 lean_ctor_release(x_2229, 1);
 x_2246 = x_2229;
} else {
 lean_dec_ref(x_2229);
 x_2246 = lean_box(0);
}
x_2247 = l_Lean_Exception_isRuntime(x_2244);
if (x_2247 == 0)
{
lean_object* x_2248; 
lean_dec(x_2244);
if (lean_is_scalar(x_2246)) {
 x_2248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2248 = x_2246;
 lean_ctor_set_tag(x_2248, 0);
}
lean_ctor_set(x_2248, 0, x_2218);
lean_ctor_set(x_2248, 1, x_2245);
return x_2248;
}
else
{
lean_object* x_2249; 
if (lean_is_scalar(x_2246)) {
 x_2249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2249 = x_2246;
}
lean_ctor_set(x_2249, 0, x_2244);
lean_ctor_set(x_2249, 1, x_2245);
return x_2249;
}
}
}
}
else
{
lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; 
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2250 = lean_ctor_get(x_2206, 0);
lean_inc(x_2250);
x_2251 = lean_ctor_get(x_2206, 1);
lean_inc(x_2251);
if (lean_is_exclusive(x_2206)) {
 lean_ctor_release(x_2206, 0);
 lean_ctor_release(x_2206, 1);
 x_2252 = x_2206;
} else {
 lean_dec_ref(x_2206);
 x_2252 = lean_box(0);
}
if (lean_is_scalar(x_2252)) {
 x_2253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2253 = x_2252;
}
lean_ctor_set(x_2253, 0, x_2250);
lean_ctor_set(x_2253, 1, x_2251);
return x_2253;
}
}
}
else
{
lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; 
lean_dec(x_1943);
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2254 = lean_ctor_get(x_1944, 0);
lean_inc(x_2254);
x_2255 = lean_ctor_get(x_1944, 1);
lean_inc(x_2255);
if (lean_is_exclusive(x_1944)) {
 lean_ctor_release(x_1944, 0);
 lean_ctor_release(x_1944, 1);
 x_2256 = x_1944;
} else {
 lean_dec_ref(x_1944);
 x_2256 = lean_box(0);
}
if (lean_is_scalar(x_2256)) {
 x_2257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2257 = x_2256;
}
lean_ctor_set(x_2257, 0, x_2254);
lean_ctor_set(x_2257, 1, x_2255);
return x_2257;
}
}
}
else
{
lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; 
lean_dec(x_1932);
lean_dec(x_1931);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2258 = lean_ctor_get(x_1933, 0);
lean_inc(x_2258);
x_2259 = lean_ctor_get(x_1933, 1);
lean_inc(x_2259);
if (lean_is_exclusive(x_1933)) {
 lean_ctor_release(x_1933, 0);
 lean_ctor_release(x_1933, 1);
 x_2260 = x_1933;
} else {
 lean_dec_ref(x_1933);
 x_2260 = lean_box(0);
}
if (lean_is_scalar(x_2260)) {
 x_2261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2261 = x_2260;
}
lean_ctor_set(x_2261, 0, x_2258);
lean_ctor_set(x_2261, 1, x_2259);
return x_2261;
}
}
}
}
else
{
uint8_t x_2262; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2262 = !lean_is_exclusive(x_24);
if (x_2262 == 0)
{
return x_24;
}
else
{
lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; 
x_2263 = lean_ctor_get(x_24, 0);
x_2264 = lean_ctor_get(x_24, 1);
lean_inc(x_2264);
lean_inc(x_2263);
lean_dec(x_24);
x_2265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2265, 0, x_2263);
lean_ctor_set(x_2265, 1, x_2264);
return x_2265;
}
}
}
else
{
uint8_t x_2266; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_2266 = !lean_is_exclusive(x_18);
if (x_2266 == 0)
{
return x_18;
}
else
{
lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; 
x_2267 = lean_ctor_get(x_18, 0);
x_2268 = lean_ctor_get(x_18, 1);
lean_inc(x_2268);
lean_inc(x_2267);
lean_dec(x_18);
x_2269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2269, 0, x_2267);
lean_ctor_set(x_2269, 1, x_2268);
return x_2269;
}
}
block_14:
{
uint8_t x_10; 
x_10 = l_Lean_Exception_isRuntime(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
return x_13;
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
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_216_(lean_io_mk_world());
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
