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
x_39 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_36, x_37, x_38, x_38, x_2, x_3, x_4, x_5, x_6);
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
x_72 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_69, x_70, x_71, x_71, x_68, x_3, x_4, x_5, x_6);
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
lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_19 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_20, x_3, x_4, x_5, x_6, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_25 = l_Lean_Meta_isTypeApp_x3f(x_17, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_23);
x_38 = l_Lean_Meta_isTypeApp_x3f(x_23, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_26);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
lean_inc(x_49);
x_51 = l_Lean_Meta_isExprDefEq(x_49, x_36, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_free_object(x_26);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_55 = x_51;
} else {
 lean_dec_ref(x_51);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_5, 2);
lean_inc(x_56);
x_57 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_58 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_56, x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_55;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_71; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_49);
x_71 = lean_infer_type(x_49, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_74 = lean_whnf(x_72, x_3, x_4, x_5, x_6, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 7)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 3)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 2);
lean_inc(x_77);
lean_dec(x_75);
if (lean_obj_tag(x_77) == 3)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_81 = lean_infer_type(x_36, x_3, x_4, x_5, x_6, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_84 = lean_whnf(x_82, x_3, x_4, x_5, x_6, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 7)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 3)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 2);
lean_inc(x_87);
lean_dec(x_85);
if (lean_obj_tag(x_87) == 3)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l_Lean_Meta_decLevel(x_79, x_3, x_4, x_5, x_6, x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_94 = l_Lean_Meta_decLevel(x_89, x_3, x_4, x_5, x_6, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_92);
x_98 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_92, x_95, x_97, x_3, x_4, x_5, x_6, x_96);
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
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_80);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_98);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_98, 0);
lean_dec(x_102);
x_103 = lean_box(0);
lean_ctor_set(x_98, 0, x_103);
return x_98;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
lean_dec(x_98);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_108 = l_Lean_Meta_decLevel(x_80, x_3, x_4, x_5, x_6, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_111 = l_Lean_Meta_decLevel(x_90, x_3, x_4, x_5, x_6, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_92);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_119 = l_Lean_Expr_const___override(x_118, x_117);
x_120 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_49);
x_121 = lean_array_push(x_120, x_49);
lean_inc(x_36);
x_122 = lean_array_push(x_121, x_36);
x_123 = l_Lean_mkAppN(x_119, x_122);
x_124 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_125 = l_Lean_Meta_trySynthInstance(x_123, x_124, x_3, x_4, x_5, x_6, x_113);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 1)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_50);
x_129 = l_Lean_Meta_getDecLevel(x_50, x_3, x_4, x_5, x_6, x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_132 = l_Lean_Meta_getDecLevel(x_23, x_3, x_4, x_5, x_6, x_131);
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
lean_inc(x_17);
x_135 = l_Lean_Meta_getDecLevel(x_17, x_3, x_4, x_5, x_6, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_114);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_130);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_140);
x_142 = l_Lean_Expr_const___override(x_141, x_140);
x_143 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_49);
x_144 = lean_array_push(x_143, x_49);
lean_inc(x_36);
x_145 = lean_array_push(x_144, x_36);
lean_inc(x_128);
x_146 = lean_array_push(x_145, x_128);
lean_inc(x_50);
x_147 = lean_array_push(x_146, x_50);
lean_inc(x_1);
x_148 = lean_array_push(x_147, x_1);
x_149 = l_Lean_mkAppN(x_142, x_148);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_149);
x_150 = lean_infer_type(x_149, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_153 = l_Lean_Meta_isExprDefEq(x_17, x_151, x_3, x_4, x_5, x_6, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_149);
lean_free_object(x_39);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_157 = l_Lean_Meta_isMonad_x3f(x_36, x_3, x_4, x_5, x_6, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
lean_ctor_set(x_157, 0, x_124);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_124);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = lean_ctor_get(x_158, 0);
lean_inc(x_164);
lean_dec(x_158);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_50);
x_165 = l_Lean_Meta_getLevel(x_50, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_37);
x_168 = l_Lean_Meta_getLevel(x_37, x_3, x_4, x_5, x_6, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_114);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_166);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_174 = l_Lean_Expr_const___override(x_173, x_172);
x_175 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_50);
x_176 = lean_array_push(x_175, x_50);
x_177 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_178 = lean_array_push(x_176, x_177);
lean_inc(x_37);
x_179 = lean_array_push(x_178, x_37);
x_180 = l_Lean_mkAppN(x_174, x_179);
x_181 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_182 = 0;
lean_inc(x_50);
x_183 = l_Lean_Expr_forallE___override(x_181, x_50, x_180, x_182);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_184 = l_Lean_Meta_trySynthInstance(x_183, x_124, x_3, x_4, x_5, x_6, x_170);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 1)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_189 = l_Lean_Expr_const___override(x_188, x_140);
x_190 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_191 = lean_array_push(x_190, x_49);
x_192 = lean_array_push(x_191, x_36);
x_193 = lean_array_push(x_192, x_50);
x_194 = lean_array_push(x_193, x_37);
x_195 = lean_array_push(x_194, x_128);
x_196 = lean_array_push(x_195, x_187);
x_197 = lean_array_push(x_196, x_164);
x_198 = lean_array_push(x_197, x_1);
x_199 = l_Lean_mkAppN(x_189, x_198);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_200 = l_Lean_Meta_expandCoe(x_199, x_3, x_4, x_5, x_6, x_186);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_201);
x_203 = lean_infer_type(x_201, x_3, x_4, x_5, x_6, x_202);
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
x_206 = l_Lean_Meta_isExprDefEq(x_17, x_204, x_3, x_4, x_5, x_6, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; uint8_t x_208; 
lean_dec(x_55);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
uint8_t x_209; 
lean_dec(x_201);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_206, 0);
lean_dec(x_210);
lean_ctor_set(x_206, 0, x_124);
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
lean_dec(x_206);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_124);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_206, 1);
lean_inc(x_213);
lean_dec(x_206);
x_214 = lean_box(0);
x_215 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_201, x_214, x_3, x_4, x_5, x_6, x_213);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
return x_215;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_215);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_201);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_220 = lean_ctor_get(x_206, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_206, 1);
lean_inc(x_221);
lean_dec(x_206);
x_61 = x_220;
x_62 = x_221;
goto block_70;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_201);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_222 = lean_ctor_get(x_203, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_203, 1);
lean_inc(x_223);
lean_dec(x_203);
x_61 = x_222;
x_62 = x_223;
goto block_70;
}
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_224 = lean_ctor_get(x_200, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_200, 1);
lean_inc(x_225);
lean_dec(x_200);
x_61 = x_224;
x_62 = x_225;
goto block_70;
}
}
else
{
uint8_t x_226; 
lean_dec(x_185);
lean_dec(x_164);
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_184);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_184, 0);
lean_dec(x_227);
lean_ctor_set(x_184, 0, x_124);
return x_184;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_184, 1);
lean_inc(x_228);
lean_dec(x_184);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_124);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_164);
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_230 = lean_ctor_get(x_184, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_184, 1);
lean_inc(x_231);
lean_dec(x_184);
x_61 = x_230;
x_62 = x_231;
goto block_70;
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_232 = lean_ctor_get(x_168, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_168, 1);
lean_inc(x_233);
lean_dec(x_168);
x_61 = x_232;
x_62 = x_233;
goto block_70;
}
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_164);
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_234 = lean_ctor_get(x_165, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_165, 1);
lean_inc(x_235);
lean_dec(x_165);
x_61 = x_234;
x_62 = x_235;
goto block_70;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_236 = lean_ctor_get(x_157, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_157, 1);
lean_inc(x_237);
lean_dec(x_157);
x_61 = x_236;
x_62 = x_237;
goto block_70;
}
}
else
{
uint8_t x_238; 
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_153);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_153, 0);
lean_dec(x_239);
lean_ctor_set(x_39, 0, x_149);
lean_ctor_set(x_153, 0, x_39);
return x_153;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_153, 1);
lean_inc(x_240);
lean_dec(x_153);
lean_ctor_set(x_39, 0, x_149);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_39);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_149);
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_242 = lean_ctor_get(x_153, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_153, 1);
lean_inc(x_243);
lean_dec(x_153);
x_61 = x_242;
x_62 = x_243;
goto block_70;
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_149);
lean_dec(x_140);
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_244 = lean_ctor_get(x_150, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_150, 1);
lean_inc(x_245);
lean_dec(x_150);
x_61 = x_244;
x_62 = x_245;
goto block_70;
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_246 = lean_ctor_get(x_135, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_135, 1);
lean_inc(x_247);
lean_dec(x_135);
x_61 = x_246;
x_62 = x_247;
goto block_70;
}
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_248 = lean_ctor_get(x_132, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_132, 1);
lean_inc(x_249);
lean_dec(x_132);
x_61 = x_248;
x_62 = x_249;
goto block_70;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_128);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_250 = lean_ctor_get(x_129, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_129, 1);
lean_inc(x_251);
lean_dec(x_129);
x_61 = x_250;
x_62 = x_251;
goto block_70;
}
}
else
{
uint8_t x_252; 
lean_dec(x_126);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_125);
if (x_252 == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_125, 0);
lean_dec(x_253);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_125, 1);
lean_inc(x_254);
lean_dec(x_125);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_124);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_256 = lean_ctor_get(x_125, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_125, 1);
lean_inc(x_257);
lean_dec(x_125);
x_61 = x_256;
x_62 = x_257;
goto block_70;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_109);
lean_dec(x_92);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_258 = lean_ctor_get(x_111, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_111, 1);
lean_inc(x_259);
lean_dec(x_111);
x_61 = x_258;
x_62 = x_259;
goto block_70;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_260 = lean_ctor_get(x_108, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_108, 1);
lean_inc(x_261);
lean_dec(x_108);
x_61 = x_260;
x_62 = x_261;
goto block_70;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_80);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_262 = lean_ctor_get(x_98, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_98, 1);
lean_inc(x_263);
lean_dec(x_98);
x_61 = x_262;
x_62 = x_263;
goto block_70;
}
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_80);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_264 = lean_ctor_get(x_94, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_94, 1);
lean_inc(x_265);
lean_dec(x_94);
x_61 = x_264;
x_62 = x_265;
goto block_70;
}
}
else
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_80);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_91, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_91, 1);
lean_inc(x_267);
lean_dec(x_91);
x_61 = x_266;
x_62 = x_267;
goto block_70;
}
}
else
{
uint8_t x_268; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_84);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_84, 0);
lean_dec(x_269);
x_270 = lean_box(0);
lean_ctor_set(x_84, 0, x_270);
return x_84;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_84, 1);
lean_inc(x_271);
lean_dec(x_84);
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_84);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_84, 0);
lean_dec(x_275);
x_276 = lean_box(0);
lean_ctor_set(x_84, 0, x_276);
return x_84;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_84, 1);
lean_inc(x_277);
lean_dec(x_84);
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
lean_dec(x_85);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_280 = !lean_is_exclusive(x_84);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_84, 0);
lean_dec(x_281);
x_282 = lean_box(0);
lean_ctor_set(x_84, 0, x_282);
return x_84;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_84, 1);
lean_inc(x_283);
lean_dec(x_84);
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
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_286 = !lean_is_exclusive(x_84);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; 
x_287 = lean_ctor_get(x_84, 0);
x_288 = l_Lean_Exception_isRuntime(x_287);
if (x_288 == 0)
{
lean_object* x_289; 
lean_dec(x_287);
lean_dec(x_5);
x_289 = lean_box(0);
lean_ctor_set_tag(x_84, 0);
lean_ctor_set(x_84, 0, x_289);
return x_84;
}
else
{
uint8_t x_290; 
x_290 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_290 == 0)
{
return x_84;
}
else
{
lean_object* x_291; 
lean_dec(x_287);
x_291 = lean_box(0);
lean_ctor_set_tag(x_84, 0);
lean_ctor_set(x_84, 0, x_291);
return x_84;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_292 = lean_ctor_get(x_84, 0);
x_293 = lean_ctor_get(x_84, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_84);
x_294 = l_Lean_Exception_isRuntime(x_292);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_292);
lean_dec(x_5);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_293);
return x_296;
}
else
{
uint8_t x_297; 
x_297 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_297 == 0)
{
lean_object* x_298; 
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_292);
lean_ctor_set(x_298, 1, x_293);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_292);
x_299 = lean_box(0);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_293);
return x_300;
}
}
}
}
}
else
{
uint8_t x_301; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_301 = !lean_is_exclusive(x_81);
if (x_301 == 0)
{
lean_object* x_302; uint8_t x_303; 
x_302 = lean_ctor_get(x_81, 0);
x_303 = l_Lean_Exception_isRuntime(x_302);
if (x_303 == 0)
{
lean_object* x_304; 
lean_dec(x_302);
lean_dec(x_5);
x_304 = lean_box(0);
lean_ctor_set_tag(x_81, 0);
lean_ctor_set(x_81, 0, x_304);
return x_81;
}
else
{
uint8_t x_305; 
x_305 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_305 == 0)
{
return x_81;
}
else
{
lean_object* x_306; 
lean_dec(x_302);
x_306 = lean_box(0);
lean_ctor_set_tag(x_81, 0);
lean_ctor_set(x_81, 0, x_306);
return x_81;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_81, 0);
x_308 = lean_ctor_get(x_81, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_81);
x_309 = l_Lean_Exception_isRuntime(x_307);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_307);
lean_dec(x_5);
x_310 = lean_box(0);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_308);
return x_311;
}
else
{
uint8_t x_312; 
x_312 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_312 == 0)
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_307);
lean_ctor_set(x_313, 1, x_308);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_307);
x_314 = lean_box(0);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_308);
return x_315;
}
}
}
}
}
else
{
uint8_t x_316; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_316 = !lean_is_exclusive(x_74);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_74, 0);
lean_dec(x_317);
x_318 = lean_box(0);
lean_ctor_set(x_74, 0, x_318);
return x_74;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_74, 1);
lean_inc(x_319);
lean_dec(x_74);
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
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_74);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_74, 0);
lean_dec(x_323);
x_324 = lean_box(0);
lean_ctor_set(x_74, 0, x_324);
return x_74;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_74, 1);
lean_inc(x_325);
lean_dec(x_74);
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
lean_dec(x_75);
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_328 = !lean_is_exclusive(x_74);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_74, 0);
lean_dec(x_329);
x_330 = lean_box(0);
lean_ctor_set(x_74, 0, x_330);
return x_74;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_74, 1);
lean_inc(x_331);
lean_dec(x_74);
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
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_334 = !lean_is_exclusive(x_74);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_ctor_get(x_74, 0);
x_336 = l_Lean_Exception_isRuntime(x_335);
if (x_336 == 0)
{
lean_object* x_337; 
lean_dec(x_335);
lean_dec(x_5);
x_337 = lean_box(0);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 0, x_337);
return x_74;
}
else
{
uint8_t x_338; 
x_338 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_338 == 0)
{
return x_74;
}
else
{
lean_object* x_339; 
lean_dec(x_335);
x_339 = lean_box(0);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 0, x_339);
return x_74;
}
}
}
else
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_340 = lean_ctor_get(x_74, 0);
x_341 = lean_ctor_get(x_74, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_74);
x_342 = l_Lean_Exception_isRuntime(x_340);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_340);
lean_dec(x_5);
x_343 = lean_box(0);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_341);
return x_344;
}
else
{
uint8_t x_345; 
x_345 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_345 == 0)
{
lean_object* x_346; 
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_340);
lean_ctor_set(x_346, 1, x_341);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_340);
x_347 = lean_box(0);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_341);
return x_348;
}
}
}
}
}
else
{
uint8_t x_349; 
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_349 = !lean_is_exclusive(x_71);
if (x_349 == 0)
{
lean_object* x_350; uint8_t x_351; 
x_350 = lean_ctor_get(x_71, 0);
x_351 = l_Lean_Exception_isRuntime(x_350);
if (x_351 == 0)
{
lean_object* x_352; 
lean_dec(x_350);
lean_dec(x_5);
x_352 = lean_box(0);
lean_ctor_set_tag(x_71, 0);
lean_ctor_set(x_71, 0, x_352);
return x_71;
}
else
{
uint8_t x_353; 
x_353 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_353 == 0)
{
return x_71;
}
else
{
lean_object* x_354; 
lean_dec(x_350);
x_354 = lean_box(0);
lean_ctor_set_tag(x_71, 0);
lean_ctor_set(x_71, 0, x_354);
return x_71;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_355 = lean_ctor_get(x_71, 0);
x_356 = lean_ctor_get(x_71, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_71);
x_357 = l_Lean_Exception_isRuntime(x_355);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_355);
lean_dec(x_5);
x_358 = lean_box(0);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_356);
return x_359;
}
else
{
uint8_t x_360; 
x_360 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_360 == 0)
{
lean_object* x_361; 
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_355);
lean_ctor_set(x_361, 1, x_356);
return x_361;
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_355);
x_362 = lean_box(0);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_356);
return x_363;
}
}
}
}
block_70:
{
uint8_t x_63; 
x_63 = l_Lean_Exception_isRuntime(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_5);
x_64 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_55;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_66 == 0)
{
lean_object* x_67; 
if (lean_is_scalar(x_55)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_55;
 lean_ctor_set_tag(x_67, 1);
}
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_61);
x_68 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_55;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_62);
return x_69;
}
}
}
}
}
else
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_23);
lean_dec(x_17);
x_364 = lean_ctor_get(x_51, 1);
lean_inc(x_364);
lean_dec(x_51);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_365 = l_Lean_Meta_isMonad_x3f(x_36, x_3, x_4, x_5, x_6, x_364);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 0)
{
uint8_t x_367; 
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_free_object(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_367 = !lean_is_exclusive(x_365);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_365, 0);
lean_dec(x_368);
x_369 = lean_box(0);
lean_ctor_set(x_365, 0, x_369);
return x_365;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_365, 1);
lean_inc(x_370);
lean_dec(x_365);
x_371 = lean_box(0);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; uint8_t x_374; 
x_373 = lean_ctor_get(x_365, 1);
lean_inc(x_373);
lean_dec(x_365);
x_374 = !lean_is_exclusive(x_366);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_375 = lean_ctor_get(x_366, 0);
lean_ctor_set(x_366, 0, x_49);
lean_ctor_set(x_39, 0, x_50);
lean_ctor_set(x_26, 0, x_37);
x_376 = lean_box(0);
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_375);
x_378 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_378, 0, x_1);
x_379 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_380 = lean_array_push(x_379, x_366);
x_381 = lean_array_push(x_380, x_39);
x_382 = lean_array_push(x_381, x_26);
x_383 = lean_array_push(x_382, x_376);
x_384 = lean_array_push(x_383, x_377);
x_385 = lean_array_push(x_384, x_378);
x_386 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_387 = l_Lean_Meta_mkAppOptM(x_386, x_385, x_3, x_4, x_5, x_6, x_373);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
lean_inc(x_5);
x_390 = l_Lean_Meta_expandCoe(x_388, x_3, x_4, x_5, x_6, x_389);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_5);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_box(0);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_393);
x_8 = x_394;
x_9 = x_392;
goto block_15;
}
else
{
uint8_t x_395; 
x_395 = !lean_is_exclusive(x_390);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_396 = lean_ctor_get(x_390, 0);
x_397 = lean_ctor_get(x_390, 1);
x_398 = l_Lean_Exception_isRuntime(x_396);
if (x_398 == 0)
{
lean_object* x_399; 
lean_free_object(x_390);
lean_dec(x_396);
lean_dec(x_5);
x_399 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_399;
x_9 = x_397;
goto block_15;
}
else
{
uint8_t x_400; 
x_400 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_400 == 0)
{
return x_390;
}
else
{
lean_object* x_401; 
lean_free_object(x_390);
lean_dec(x_396);
x_401 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_401;
x_9 = x_397;
goto block_15;
}
}
}
else
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_402 = lean_ctor_get(x_390, 0);
x_403 = lean_ctor_get(x_390, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_390);
x_404 = l_Lean_Exception_isRuntime(x_402);
if (x_404 == 0)
{
lean_object* x_405; 
lean_dec(x_402);
lean_dec(x_5);
x_405 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_405;
x_9 = x_403;
goto block_15;
}
else
{
uint8_t x_406; 
x_406 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_406 == 0)
{
lean_object* x_407; 
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_402);
lean_ctor_set(x_407, 1, x_403);
return x_407;
}
else
{
lean_object* x_408; 
lean_dec(x_402);
x_408 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_408;
x_9 = x_403;
goto block_15;
}
}
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_409 = !lean_is_exclusive(x_387);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_410 = lean_ctor_get(x_387, 0);
x_411 = lean_ctor_get(x_387, 1);
x_412 = l_Lean_Exception_isRuntime(x_410);
if (x_412 == 0)
{
lean_object* x_413; 
lean_free_object(x_387);
lean_dec(x_410);
lean_dec(x_5);
x_413 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_413;
x_9 = x_411;
goto block_15;
}
else
{
uint8_t x_414; 
x_414 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_414 == 0)
{
return x_387;
}
else
{
lean_object* x_415; 
lean_free_object(x_387);
lean_dec(x_410);
x_415 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_415;
x_9 = x_411;
goto block_15;
}
}
}
else
{
lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_416 = lean_ctor_get(x_387, 0);
x_417 = lean_ctor_get(x_387, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_387);
x_418 = l_Lean_Exception_isRuntime(x_416);
if (x_418 == 0)
{
lean_object* x_419; 
lean_dec(x_416);
lean_dec(x_5);
x_419 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_419;
x_9 = x_417;
goto block_15;
}
else
{
uint8_t x_420; 
x_420 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_420 == 0)
{
lean_object* x_421; 
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_416);
lean_ctor_set(x_421, 1, x_417);
return x_421;
}
else
{
lean_object* x_422; 
lean_dec(x_416);
x_422 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_422;
x_9 = x_417;
goto block_15;
}
}
}
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_423 = lean_ctor_get(x_366, 0);
lean_inc(x_423);
lean_dec(x_366);
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_49);
lean_ctor_set(x_39, 0, x_50);
lean_ctor_set(x_26, 0, x_37);
x_425 = lean_box(0);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_423);
x_427 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_427, 0, x_1);
x_428 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_429 = lean_array_push(x_428, x_424);
x_430 = lean_array_push(x_429, x_39);
x_431 = lean_array_push(x_430, x_26);
x_432 = lean_array_push(x_431, x_425);
x_433 = lean_array_push(x_432, x_426);
x_434 = lean_array_push(x_433, x_427);
x_435 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_436 = l_Lean_Meta_mkAppOptM(x_435, x_434, x_3, x_4, x_5, x_6, x_373);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
lean_inc(x_5);
x_439 = l_Lean_Meta_expandCoe(x_437, x_3, x_4, x_5, x_6, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_5);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_box(0);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_442);
x_8 = x_443;
x_9 = x_441;
goto block_15;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_444 = lean_ctor_get(x_439, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_439, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_446 = x_439;
} else {
 lean_dec_ref(x_439);
 x_446 = lean_box(0);
}
x_447 = l_Lean_Exception_isRuntime(x_444);
if (x_447 == 0)
{
lean_object* x_448; 
lean_dec(x_446);
lean_dec(x_444);
lean_dec(x_5);
x_448 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_448;
x_9 = x_445;
goto block_15;
}
else
{
uint8_t x_449; 
x_449 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_449 == 0)
{
lean_object* x_450; 
if (lean_is_scalar(x_446)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_446;
}
lean_ctor_set(x_450, 0, x_444);
lean_ctor_set(x_450, 1, x_445);
return x_450;
}
else
{
lean_object* x_451; 
lean_dec(x_446);
lean_dec(x_444);
x_451 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_451;
x_9 = x_445;
goto block_15;
}
}
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_452 = lean_ctor_get(x_436, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_436, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_454 = x_436;
} else {
 lean_dec_ref(x_436);
 x_454 = lean_box(0);
}
x_455 = l_Lean_Exception_isRuntime(x_452);
if (x_455 == 0)
{
lean_object* x_456; 
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_5);
x_456 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_456;
x_9 = x_453;
goto block_15;
}
else
{
uint8_t x_457; 
x_457 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_457 == 0)
{
lean_object* x_458; 
if (lean_is_scalar(x_454)) {
 x_458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_458 = x_454;
}
lean_ctor_set(x_458, 0, x_452);
lean_ctor_set(x_458, 1, x_453);
return x_458;
}
else
{
lean_object* x_459; 
lean_dec(x_454);
lean_dec(x_452);
x_459 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_459;
x_9 = x_453;
goto block_15;
}
}
}
}
}
}
else
{
uint8_t x_460; 
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_free_object(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_460 = !lean_is_exclusive(x_365);
if (x_460 == 0)
{
return x_365;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_365, 0);
x_462 = lean_ctor_get(x_365, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_365);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
}
}
else
{
uint8_t x_464; 
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_26);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_464 = !lean_is_exclusive(x_51);
if (x_464 == 0)
{
return x_51;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_51, 0);
x_466 = lean_ctor_get(x_51, 1);
lean_inc(x_466);
lean_inc(x_465);
lean_dec(x_51);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
return x_467;
}
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_468 = lean_ctor_get(x_39, 0);
lean_inc(x_468);
lean_dec(x_39);
x_469 = lean_ctor_get(x_38, 1);
lean_inc(x_469);
lean_dec(x_38);
x_470 = lean_ctor_get(x_468, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_468, 1);
lean_inc(x_471);
lean_dec(x_468);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
lean_inc(x_470);
x_472 = l_Lean_Meta_isExprDefEq(x_470, x_36, x_3, x_4, x_5, x_6, x_469);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; uint8_t x_474; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_unbox(x_473);
lean_dec(x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
lean_free_object(x_26);
x_475 = lean_ctor_get(x_472, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_476 = x_472;
} else {
 lean_dec_ref(x_472);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_5, 2);
lean_inc(x_477);
x_478 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_479 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_477, x_478);
lean_dec(x_477);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_480 = lean_box(0);
if (lean_is_scalar(x_476)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_476;
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_475);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_492; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_470);
x_492 = lean_infer_type(x_470, x_3, x_4, x_5, x_6, x_475);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_495 = lean_whnf(x_493, x_3, x_4, x_5, x_6, x_494);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 7)
{
lean_object* x_497; 
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
if (lean_obj_tag(x_497) == 3)
{
lean_object* x_498; 
x_498 = lean_ctor_get(x_496, 2);
lean_inc(x_498);
lean_dec(x_496);
if (lean_obj_tag(x_498) == 3)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_499 = lean_ctor_get(x_495, 1);
lean_inc(x_499);
lean_dec(x_495);
x_500 = lean_ctor_get(x_497, 0);
lean_inc(x_500);
lean_dec(x_497);
x_501 = lean_ctor_get(x_498, 0);
lean_inc(x_501);
lean_dec(x_498);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_502 = lean_infer_type(x_36, x_3, x_4, x_5, x_6, x_499);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_505 = lean_whnf(x_503, x_3, x_4, x_5, x_6, x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
if (lean_obj_tag(x_506) == 7)
{
lean_object* x_507; 
x_507 = lean_ctor_get(x_506, 1);
lean_inc(x_507);
if (lean_obj_tag(x_507) == 3)
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_506, 2);
lean_inc(x_508);
lean_dec(x_506);
if (lean_obj_tag(x_508) == 3)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_509 = lean_ctor_get(x_505, 1);
lean_inc(x_509);
lean_dec(x_505);
x_510 = lean_ctor_get(x_507, 0);
lean_inc(x_510);
lean_dec(x_507);
x_511 = lean_ctor_get(x_508, 0);
lean_inc(x_511);
lean_dec(x_508);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_512 = l_Lean_Meta_decLevel(x_500, x_3, x_4, x_5, x_6, x_509);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_515 = l_Lean_Meta_decLevel(x_510, x_3, x_4, x_5, x_6, x_514);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; uint8_t x_518; lean_object* x_519; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_513);
x_519 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_513, x_516, x_518, x_3, x_4, x_5, x_6, x_517);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; uint8_t x_521; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_unbox(x_520);
lean_dec(x_520);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_501);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_523 = x_519;
} else {
 lean_dec_ref(x_519);
 x_523 = lean_box(0);
}
x_524 = lean_box(0);
if (lean_is_scalar(x_523)) {
 x_525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_525 = x_523;
}
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_522);
return x_525;
}
else
{
lean_object* x_526; lean_object* x_527; 
x_526 = lean_ctor_get(x_519, 1);
lean_inc(x_526);
lean_dec(x_519);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_527 = l_Lean_Meta_decLevel(x_501, x_3, x_4, x_5, x_6, x_526);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_530 = l_Lean_Meta_decLevel(x_511, x_3, x_4, x_5, x_6, x_529);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = lean_box(0);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_531);
lean_ctor_set(x_534, 1, x_533);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_528);
lean_ctor_set(x_535, 1, x_534);
x_536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_536, 0, x_513);
lean_ctor_set(x_536, 1, x_535);
x_537 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_538 = l_Lean_Expr_const___override(x_537, x_536);
x_539 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_470);
x_540 = lean_array_push(x_539, x_470);
lean_inc(x_36);
x_541 = lean_array_push(x_540, x_36);
x_542 = l_Lean_mkAppN(x_538, x_541);
x_543 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_544 = l_Lean_Meta_trySynthInstance(x_542, x_543, x_3, x_4, x_5, x_6, x_532);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
if (lean_obj_tag(x_545) == 1)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_547 = lean_ctor_get(x_545, 0);
lean_inc(x_547);
lean_dec(x_545);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_471);
x_548 = l_Lean_Meta_getDecLevel(x_471, x_3, x_4, x_5, x_6, x_546);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_551 = l_Lean_Meta_getDecLevel(x_23, x_3, x_4, x_5, x_6, x_550);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_554 = l_Lean_Meta_getDecLevel(x_17, x_3, x_4, x_5, x_6, x_553);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_533);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_552);
lean_ctor_set(x_558, 1, x_557);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_549);
lean_ctor_set(x_559, 1, x_558);
x_560 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_559);
x_561 = l_Lean_Expr_const___override(x_560, x_559);
x_562 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_470);
x_563 = lean_array_push(x_562, x_470);
lean_inc(x_36);
x_564 = lean_array_push(x_563, x_36);
lean_inc(x_547);
x_565 = lean_array_push(x_564, x_547);
lean_inc(x_471);
x_566 = lean_array_push(x_565, x_471);
lean_inc(x_1);
x_567 = lean_array_push(x_566, x_1);
x_568 = l_Lean_mkAppN(x_561, x_567);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_568);
x_569 = lean_infer_type(x_568, x_3, x_4, x_5, x_6, x_556);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_572 = l_Lean_Meta_isExprDefEq(x_17, x_570, x_3, x_4, x_5, x_6, x_571);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; uint8_t x_574; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_unbox(x_573);
lean_dec(x_573);
if (x_574 == 0)
{
lean_object* x_575; lean_object* x_576; 
lean_dec(x_568);
x_575 = lean_ctor_get(x_572, 1);
lean_inc(x_575);
lean_dec(x_572);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_576 = l_Lean_Meta_isMonad_x3f(x_36, x_3, x_4, x_5, x_6, x_575);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_579 = x_576;
} else {
 lean_dec_ref(x_576);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(0, 2, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_543);
lean_ctor_set(x_580, 1, x_578);
return x_580;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_576, 1);
lean_inc(x_581);
lean_dec(x_576);
x_582 = lean_ctor_get(x_577, 0);
lean_inc(x_582);
lean_dec(x_577);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_471);
x_583 = l_Lean_Meta_getLevel(x_471, x_3, x_4, x_5, x_6, x_581);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
lean_dec(x_583);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_37);
x_586 = l_Lean_Meta_getLevel(x_37, x_3, x_4, x_5, x_6, x_585);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; uint8_t x_600; lean_object* x_601; lean_object* x_602; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_533);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_584);
lean_ctor_set(x_590, 1, x_589);
x_591 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_592 = l_Lean_Expr_const___override(x_591, x_590);
x_593 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_471);
x_594 = lean_array_push(x_593, x_471);
x_595 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_596 = lean_array_push(x_594, x_595);
lean_inc(x_37);
x_597 = lean_array_push(x_596, x_37);
x_598 = l_Lean_mkAppN(x_592, x_597);
x_599 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_600 = 0;
lean_inc(x_471);
x_601 = l_Lean_Expr_forallE___override(x_599, x_471, x_598, x_600);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_602 = l_Lean_Meta_trySynthInstance(x_601, x_543, x_3, x_4, x_5, x_6, x_588);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
if (lean_obj_tag(x_603) == 1)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = lean_ctor_get(x_603, 0);
lean_inc(x_605);
lean_dec(x_603);
x_606 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_607 = l_Lean_Expr_const___override(x_606, x_559);
x_608 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_609 = lean_array_push(x_608, x_470);
x_610 = lean_array_push(x_609, x_36);
x_611 = lean_array_push(x_610, x_471);
x_612 = lean_array_push(x_611, x_37);
x_613 = lean_array_push(x_612, x_547);
x_614 = lean_array_push(x_613, x_605);
x_615 = lean_array_push(x_614, x_582);
x_616 = lean_array_push(x_615, x_1);
x_617 = l_Lean_mkAppN(x_607, x_616);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_618 = l_Lean_Meta_expandCoe(x_617, x_3, x_4, x_5, x_6, x_604);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_618, 1);
lean_inc(x_620);
lean_dec(x_618);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_619);
x_621 = lean_infer_type(x_619, x_3, x_4, x_5, x_6, x_620);
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
x_624 = l_Lean_Meta_isExprDefEq(x_17, x_622, x_3, x_4, x_5, x_6, x_623);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; uint8_t x_626; 
lean_dec(x_476);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_unbox(x_625);
lean_dec(x_625);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_619);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_627 = lean_ctor_get(x_624, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_628 = x_624;
} else {
 lean_dec_ref(x_624);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_543);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_630 = lean_ctor_get(x_624, 1);
lean_inc(x_630);
lean_dec(x_624);
x_631 = lean_box(0);
x_632 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_619, x_631, x_3, x_4, x_5, x_6, x_630);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_635 = x_632;
} else {
 lean_dec_ref(x_632);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(0, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
return x_636;
}
}
else
{
lean_object* x_637; lean_object* x_638; 
lean_dec(x_619);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_637 = lean_ctor_get(x_624, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_624, 1);
lean_inc(x_638);
lean_dec(x_624);
x_482 = x_637;
x_483 = x_638;
goto block_491;
}
}
else
{
lean_object* x_639; lean_object* x_640; 
lean_dec(x_619);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_639 = lean_ctor_get(x_621, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_621, 1);
lean_inc(x_640);
lean_dec(x_621);
x_482 = x_639;
x_483 = x_640;
goto block_491;
}
}
else
{
lean_object* x_641; lean_object* x_642; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_641 = lean_ctor_get(x_618, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_618, 1);
lean_inc(x_642);
lean_dec(x_618);
x_482 = x_641;
x_483 = x_642;
goto block_491;
}
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_603);
lean_dec(x_582);
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_643 = lean_ctor_get(x_602, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_644 = x_602;
} else {
 lean_dec_ref(x_602);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_543);
lean_ctor_set(x_645, 1, x_643);
return x_645;
}
}
else
{
lean_object* x_646; lean_object* x_647; 
lean_dec(x_582);
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_646 = lean_ctor_get(x_602, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_602, 1);
lean_inc(x_647);
lean_dec(x_602);
x_482 = x_646;
x_483 = x_647;
goto block_491;
}
}
else
{
lean_object* x_648; lean_object* x_649; 
lean_dec(x_584);
lean_dec(x_582);
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_648 = lean_ctor_get(x_586, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_586, 1);
lean_inc(x_649);
lean_dec(x_586);
x_482 = x_648;
x_483 = x_649;
goto block_491;
}
}
else
{
lean_object* x_650; lean_object* x_651; 
lean_dec(x_582);
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_650 = lean_ctor_get(x_583, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_583, 1);
lean_inc(x_651);
lean_dec(x_583);
x_482 = x_650;
x_483 = x_651;
goto block_491;
}
}
}
else
{
lean_object* x_652; lean_object* x_653; 
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_652 = lean_ctor_get(x_576, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_576, 1);
lean_inc(x_653);
lean_dec(x_576);
x_482 = x_652;
x_483 = x_653;
goto block_491;
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_654 = lean_ctor_get(x_572, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_655 = x_572;
} else {
 lean_dec_ref(x_572);
 x_655 = lean_box(0);
}
x_656 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_656, 0, x_568);
if (lean_is_scalar(x_655)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_655;
}
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_654);
return x_657;
}
}
else
{
lean_object* x_658; lean_object* x_659; 
lean_dec(x_568);
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_658 = lean_ctor_get(x_572, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_572, 1);
lean_inc(x_659);
lean_dec(x_572);
x_482 = x_658;
x_483 = x_659;
goto block_491;
}
}
else
{
lean_object* x_660; lean_object* x_661; 
lean_dec(x_568);
lean_dec(x_559);
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_660 = lean_ctor_get(x_569, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_569, 1);
lean_inc(x_661);
lean_dec(x_569);
x_482 = x_660;
x_483 = x_661;
goto block_491;
}
}
else
{
lean_object* x_662; lean_object* x_663; 
lean_dec(x_552);
lean_dec(x_549);
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_662 = lean_ctor_get(x_554, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_554, 1);
lean_inc(x_663);
lean_dec(x_554);
x_482 = x_662;
x_483 = x_663;
goto block_491;
}
}
else
{
lean_object* x_664; lean_object* x_665; 
lean_dec(x_549);
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_664 = lean_ctor_get(x_551, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_551, 1);
lean_inc(x_665);
lean_dec(x_551);
x_482 = x_664;
x_483 = x_665;
goto block_491;
}
}
else
{
lean_object* x_666; lean_object* x_667; 
lean_dec(x_547);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_666 = lean_ctor_get(x_548, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_548, 1);
lean_inc(x_667);
lean_dec(x_548);
x_482 = x_666;
x_483 = x_667;
goto block_491;
}
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_545);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_668 = lean_ctor_get(x_544, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_669 = x_544;
} else {
 lean_dec_ref(x_544);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_543);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
}
else
{
lean_object* x_671; lean_object* x_672; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_671 = lean_ctor_get(x_544, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_544, 1);
lean_inc(x_672);
lean_dec(x_544);
x_482 = x_671;
x_483 = x_672;
goto block_491;
}
}
else
{
lean_object* x_673; lean_object* x_674; 
lean_dec(x_528);
lean_dec(x_513);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_673 = lean_ctor_get(x_530, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_530, 1);
lean_inc(x_674);
lean_dec(x_530);
x_482 = x_673;
x_483 = x_674;
goto block_491;
}
}
else
{
lean_object* x_675; lean_object* x_676; 
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_675 = lean_ctor_get(x_527, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_527, 1);
lean_inc(x_676);
lean_dec(x_527);
x_482 = x_675;
x_483 = x_676;
goto block_491;
}
}
}
else
{
lean_object* x_677; lean_object* x_678; 
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_501);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_677 = lean_ctor_get(x_519, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_519, 1);
lean_inc(x_678);
lean_dec(x_519);
x_482 = x_677;
x_483 = x_678;
goto block_491;
}
}
else
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_501);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_679 = lean_ctor_get(x_515, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_515, 1);
lean_inc(x_680);
lean_dec(x_515);
x_482 = x_679;
x_483 = x_680;
goto block_491;
}
}
else
{
lean_object* x_681; lean_object* x_682; 
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_501);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_681 = lean_ctor_get(x_512, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_512, 1);
lean_inc(x_682);
lean_dec(x_512);
x_482 = x_681;
x_483 = x_682;
goto block_491;
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_683 = lean_ctor_get(x_505, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_684 = x_505;
} else {
 lean_dec_ref(x_505);
 x_684 = lean_box(0);
}
x_685 = lean_box(0);
if (lean_is_scalar(x_684)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_684;
}
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_683);
return x_686;
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_687 = lean_ctor_get(x_505, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_688 = x_505;
} else {
 lean_dec_ref(x_505);
 x_688 = lean_box(0);
}
x_689 = lean_box(0);
if (lean_is_scalar(x_688)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_688;
}
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_687);
return x_690;
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_506);
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_691 = lean_ctor_get(x_505, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_692 = x_505;
} else {
 lean_dec_ref(x_505);
 x_692 = lean_box(0);
}
x_693 = lean_box(0);
if (lean_is_scalar(x_692)) {
 x_694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_694 = x_692;
}
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_691);
return x_694;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; 
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_695 = lean_ctor_get(x_505, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_505, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_697 = x_505;
} else {
 lean_dec_ref(x_505);
 x_697 = lean_box(0);
}
x_698 = l_Lean_Exception_isRuntime(x_695);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; 
lean_dec(x_695);
lean_dec(x_5);
x_699 = lean_box(0);
if (lean_is_scalar(x_697)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_697;
 lean_ctor_set_tag(x_700, 0);
}
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_696);
return x_700;
}
else
{
uint8_t x_701; 
x_701 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_701 == 0)
{
lean_object* x_702; 
if (lean_is_scalar(x_697)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_697;
}
lean_ctor_set(x_702, 0, x_695);
lean_ctor_set(x_702, 1, x_696);
return x_702;
}
else
{
lean_object* x_703; lean_object* x_704; 
lean_dec(x_695);
x_703 = lean_box(0);
if (lean_is_scalar(x_697)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_697;
 lean_ctor_set_tag(x_704, 0);
}
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_696);
return x_704;
}
}
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; 
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_705 = lean_ctor_get(x_502, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_502, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_707 = x_502;
} else {
 lean_dec_ref(x_502);
 x_707 = lean_box(0);
}
x_708 = l_Lean_Exception_isRuntime(x_705);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
lean_dec(x_705);
lean_dec(x_5);
x_709 = lean_box(0);
if (lean_is_scalar(x_707)) {
 x_710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_710 = x_707;
 lean_ctor_set_tag(x_710, 0);
}
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_706);
return x_710;
}
else
{
uint8_t x_711; 
x_711 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_711 == 0)
{
lean_object* x_712; 
if (lean_is_scalar(x_707)) {
 x_712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_712 = x_707;
}
lean_ctor_set(x_712, 0, x_705);
lean_ctor_set(x_712, 1, x_706);
return x_712;
}
else
{
lean_object* x_713; lean_object* x_714; 
lean_dec(x_705);
x_713 = lean_box(0);
if (lean_is_scalar(x_707)) {
 x_714 = lean_alloc_ctor(0, 2, 0);
} else {
 x_714 = x_707;
 lean_ctor_set_tag(x_714, 0);
}
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_706);
return x_714;
}
}
}
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_715 = lean_ctor_get(x_495, 1);
lean_inc(x_715);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_716 = x_495;
} else {
 lean_dec_ref(x_495);
 x_716 = lean_box(0);
}
x_717 = lean_box(0);
if (lean_is_scalar(x_716)) {
 x_718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_718 = x_716;
}
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_715);
return x_718;
}
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_719 = lean_ctor_get(x_495, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_720 = x_495;
} else {
 lean_dec_ref(x_495);
 x_720 = lean_box(0);
}
x_721 = lean_box(0);
if (lean_is_scalar(x_720)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_720;
}
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_719);
return x_722;
}
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_496);
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_723 = lean_ctor_get(x_495, 1);
lean_inc(x_723);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_724 = x_495;
} else {
 lean_dec_ref(x_495);
 x_724 = lean_box(0);
}
x_725 = lean_box(0);
if (lean_is_scalar(x_724)) {
 x_726 = lean_alloc_ctor(0, 2, 0);
} else {
 x_726 = x_724;
}
lean_ctor_set(x_726, 0, x_725);
lean_ctor_set(x_726, 1, x_723);
return x_726;
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; 
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_727 = lean_ctor_get(x_495, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_495, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_729 = x_495;
} else {
 lean_dec_ref(x_495);
 x_729 = lean_box(0);
}
x_730 = l_Lean_Exception_isRuntime(x_727);
if (x_730 == 0)
{
lean_object* x_731; lean_object* x_732; 
lean_dec(x_727);
lean_dec(x_5);
x_731 = lean_box(0);
if (lean_is_scalar(x_729)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_729;
 lean_ctor_set_tag(x_732, 0);
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_728);
return x_732;
}
else
{
uint8_t x_733; 
x_733 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_733 == 0)
{
lean_object* x_734; 
if (lean_is_scalar(x_729)) {
 x_734 = lean_alloc_ctor(1, 2, 0);
} else {
 x_734 = x_729;
}
lean_ctor_set(x_734, 0, x_727);
lean_ctor_set(x_734, 1, x_728);
return x_734;
}
else
{
lean_object* x_735; lean_object* x_736; 
lean_dec(x_727);
x_735 = lean_box(0);
if (lean_is_scalar(x_729)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_729;
 lean_ctor_set_tag(x_736, 0);
}
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_728);
return x_736;
}
}
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; uint8_t x_740; 
lean_dec(x_476);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_737 = lean_ctor_get(x_492, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_492, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_739 = x_492;
} else {
 lean_dec_ref(x_492);
 x_739 = lean_box(0);
}
x_740 = l_Lean_Exception_isRuntime(x_737);
if (x_740 == 0)
{
lean_object* x_741; lean_object* x_742; 
lean_dec(x_737);
lean_dec(x_5);
x_741 = lean_box(0);
if (lean_is_scalar(x_739)) {
 x_742 = lean_alloc_ctor(0, 2, 0);
} else {
 x_742 = x_739;
 lean_ctor_set_tag(x_742, 0);
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_738);
return x_742;
}
else
{
uint8_t x_743; 
x_743 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_743 == 0)
{
lean_object* x_744; 
if (lean_is_scalar(x_739)) {
 x_744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_744 = x_739;
}
lean_ctor_set(x_744, 0, x_737);
lean_ctor_set(x_744, 1, x_738);
return x_744;
}
else
{
lean_object* x_745; lean_object* x_746; 
lean_dec(x_737);
x_745 = lean_box(0);
if (lean_is_scalar(x_739)) {
 x_746 = lean_alloc_ctor(0, 2, 0);
} else {
 x_746 = x_739;
 lean_ctor_set_tag(x_746, 0);
}
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set(x_746, 1, x_738);
return x_746;
}
}
}
block_491:
{
uint8_t x_484; 
x_484 = l_Lean_Exception_isRuntime(x_482);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; 
lean_dec(x_482);
lean_dec(x_5);
x_485 = lean_box(0);
if (lean_is_scalar(x_476)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_476;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_483);
return x_486;
}
else
{
uint8_t x_487; 
x_487 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_487 == 0)
{
lean_object* x_488; 
if (lean_is_scalar(x_476)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_476;
 lean_ctor_set_tag(x_488, 1);
}
lean_ctor_set(x_488, 0, x_482);
lean_ctor_set(x_488, 1, x_483);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; 
lean_dec(x_482);
x_489 = lean_box(0);
if (lean_is_scalar(x_476)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_476;
}
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_483);
return x_490;
}
}
}
}
}
else
{
lean_object* x_747; lean_object* x_748; 
lean_dec(x_23);
lean_dec(x_17);
x_747 = lean_ctor_get(x_472, 1);
lean_inc(x_747);
lean_dec(x_472);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_748 = l_Lean_Meta_isMonad_x3f(x_36, x_3, x_4, x_5, x_6, x_747);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_free_object(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_751 = x_748;
} else {
 lean_dec_ref(x_748);
 x_751 = lean_box(0);
}
x_752 = lean_box(0);
if (lean_is_scalar(x_751)) {
 x_753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_753 = x_751;
}
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_750);
return x_753;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_754 = lean_ctor_get(x_748, 1);
lean_inc(x_754);
lean_dec(x_748);
x_755 = lean_ctor_get(x_749, 0);
lean_inc(x_755);
if (lean_is_exclusive(x_749)) {
 lean_ctor_release(x_749, 0);
 x_756 = x_749;
} else {
 lean_dec_ref(x_749);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 1, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_470);
x_758 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_758, 0, x_471);
lean_ctor_set(x_26, 0, x_37);
x_759 = lean_box(0);
x_760 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_760, 0, x_755);
x_761 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_761, 0, x_1);
x_762 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_763 = lean_array_push(x_762, x_757);
x_764 = lean_array_push(x_763, x_758);
x_765 = lean_array_push(x_764, x_26);
x_766 = lean_array_push(x_765, x_759);
x_767 = lean_array_push(x_766, x_760);
x_768 = lean_array_push(x_767, x_761);
x_769 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_770 = l_Lean_Meta_mkAppOptM(x_769, x_768, x_3, x_4, x_5, x_6, x_754);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_770, 1);
lean_inc(x_772);
lean_dec(x_770);
lean_inc(x_5);
x_773 = l_Lean_Meta_expandCoe(x_771, x_3, x_4, x_5, x_6, x_772);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_5);
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
lean_dec(x_773);
x_776 = lean_box(0);
x_777 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_777, 0, x_774);
lean_ctor_set(x_777, 1, x_776);
x_8 = x_777;
x_9 = x_775;
goto block_15;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; 
x_778 = lean_ctor_get(x_773, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_773, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_780 = x_773;
} else {
 lean_dec_ref(x_773);
 x_780 = lean_box(0);
}
x_781 = l_Lean_Exception_isRuntime(x_778);
if (x_781 == 0)
{
lean_object* x_782; 
lean_dec(x_780);
lean_dec(x_778);
lean_dec(x_5);
x_782 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_782;
x_9 = x_779;
goto block_15;
}
else
{
uint8_t x_783; 
x_783 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_783 == 0)
{
lean_object* x_784; 
if (lean_is_scalar(x_780)) {
 x_784 = lean_alloc_ctor(1, 2, 0);
} else {
 x_784 = x_780;
}
lean_ctor_set(x_784, 0, x_778);
lean_ctor_set(x_784, 1, x_779);
return x_784;
}
else
{
lean_object* x_785; 
lean_dec(x_780);
lean_dec(x_778);
x_785 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_785;
x_9 = x_779;
goto block_15;
}
}
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; uint8_t x_789; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_786 = lean_ctor_get(x_770, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_770, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 lean_ctor_release(x_770, 1);
 x_788 = x_770;
} else {
 lean_dec_ref(x_770);
 x_788 = lean_box(0);
}
x_789 = l_Lean_Exception_isRuntime(x_786);
if (x_789 == 0)
{
lean_object* x_790; 
lean_dec(x_788);
lean_dec(x_786);
lean_dec(x_5);
x_790 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_790;
x_9 = x_787;
goto block_15;
}
else
{
uint8_t x_791; 
x_791 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_791 == 0)
{
lean_object* x_792; 
if (lean_is_scalar(x_788)) {
 x_792 = lean_alloc_ctor(1, 2, 0);
} else {
 x_792 = x_788;
}
lean_ctor_set(x_792, 0, x_786);
lean_ctor_set(x_792, 1, x_787);
return x_792;
}
else
{
lean_object* x_793; 
lean_dec(x_788);
lean_dec(x_786);
x_793 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_793;
x_9 = x_787;
goto block_15;
}
}
}
}
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_free_object(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_794 = lean_ctor_get(x_748, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_748, 1);
lean_inc(x_795);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_796 = x_748;
} else {
 lean_dec_ref(x_748);
 x_796 = lean_box(0);
}
if (lean_is_scalar(x_796)) {
 x_797 = lean_alloc_ctor(1, 2, 0);
} else {
 x_797 = x_796;
}
lean_ctor_set(x_797, 0, x_794);
lean_ctor_set(x_797, 1, x_795);
return x_797;
}
}
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_26);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_798 = lean_ctor_get(x_472, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_472, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_800 = x_472;
} else {
 lean_dec_ref(x_472);
 x_800 = lean_box(0);
}
if (lean_is_scalar(x_800)) {
 x_801 = lean_alloc_ctor(1, 2, 0);
} else {
 x_801 = x_800;
}
lean_ctor_set(x_801, 0, x_798);
lean_ctor_set(x_801, 1, x_799);
return x_801;
}
}
}
}
else
{
uint8_t x_802; 
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_26);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_802 = !lean_is_exclusive(x_38);
if (x_802 == 0)
{
return x_38;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_38, 0);
x_804 = lean_ctor_get(x_38, 1);
lean_inc(x_804);
lean_inc(x_803);
lean_dec(x_38);
x_805 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_805, 0, x_803);
lean_ctor_set(x_805, 1, x_804);
return x_805;
}
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_806 = lean_ctor_get(x_26, 0);
lean_inc(x_806);
lean_dec(x_26);
x_807 = lean_ctor_get(x_25, 1);
lean_inc(x_807);
lean_dec(x_25);
x_808 = lean_ctor_get(x_806, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_806, 1);
lean_inc(x_809);
lean_dec(x_806);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_23);
x_810 = l_Lean_Meta_isTypeApp_x3f(x_23, x_3, x_4, x_5, x_6, x_807);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_813 = x_810;
} else {
 lean_dec_ref(x_810);
 x_813 = lean_box(0);
}
x_814 = lean_box(0);
if (lean_is_scalar(x_813)) {
 x_815 = lean_alloc_ctor(0, 2, 0);
} else {
 x_815 = x_813;
}
lean_ctor_set(x_815, 0, x_814);
lean_ctor_set(x_815, 1, x_812);
return x_815;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_816 = lean_ctor_get(x_811, 0);
lean_inc(x_816);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 x_817 = x_811;
} else {
 lean_dec_ref(x_811);
 x_817 = lean_box(0);
}
x_818 = lean_ctor_get(x_810, 1);
lean_inc(x_818);
lean_dec(x_810);
x_819 = lean_ctor_get(x_816, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_816, 1);
lean_inc(x_820);
lean_dec(x_816);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_808);
lean_inc(x_819);
x_821 = l_Lean_Meta_isExprDefEq(x_819, x_808, x_3, x_4, x_5, x_6, x_818);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; uint8_t x_823; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_unbox(x_822);
lean_dec(x_822);
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; uint8_t x_828; 
x_824 = lean_ctor_get(x_821, 1);
lean_inc(x_824);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_825 = x_821;
} else {
 lean_dec_ref(x_821);
 x_825 = lean_box(0);
}
x_826 = lean_ctor_get(x_5, 2);
lean_inc(x_826);
x_827 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_828 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_826, x_827);
lean_dec(x_826);
if (x_828 == 0)
{
lean_object* x_829; lean_object* x_830; 
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_829 = lean_box(0);
if (lean_is_scalar(x_825)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_825;
}
lean_ctor_set(x_830, 0, x_829);
lean_ctor_set(x_830, 1, x_824);
return x_830;
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_841; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_819);
x_841 = lean_infer_type(x_819, x_3, x_4, x_5, x_6, x_824);
if (lean_obj_tag(x_841) == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_844 = lean_whnf(x_842, x_3, x_4, x_5, x_6, x_843);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; 
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
if (lean_obj_tag(x_845) == 7)
{
lean_object* x_846; 
x_846 = lean_ctor_get(x_845, 1);
lean_inc(x_846);
if (lean_obj_tag(x_846) == 3)
{
lean_object* x_847; 
x_847 = lean_ctor_get(x_845, 2);
lean_inc(x_847);
lean_dec(x_845);
if (lean_obj_tag(x_847) == 3)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_848 = lean_ctor_get(x_844, 1);
lean_inc(x_848);
lean_dec(x_844);
x_849 = lean_ctor_get(x_846, 0);
lean_inc(x_849);
lean_dec(x_846);
x_850 = lean_ctor_get(x_847, 0);
lean_inc(x_850);
lean_dec(x_847);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_808);
x_851 = lean_infer_type(x_808, x_3, x_4, x_5, x_6, x_848);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
lean_dec(x_851);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_854 = lean_whnf(x_852, x_3, x_4, x_5, x_6, x_853);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
if (lean_obj_tag(x_855) == 7)
{
lean_object* x_856; 
x_856 = lean_ctor_get(x_855, 1);
lean_inc(x_856);
if (lean_obj_tag(x_856) == 3)
{
lean_object* x_857; 
x_857 = lean_ctor_get(x_855, 2);
lean_inc(x_857);
lean_dec(x_855);
if (lean_obj_tag(x_857) == 3)
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_858 = lean_ctor_get(x_854, 1);
lean_inc(x_858);
lean_dec(x_854);
x_859 = lean_ctor_get(x_856, 0);
lean_inc(x_859);
lean_dec(x_856);
x_860 = lean_ctor_get(x_857, 0);
lean_inc(x_860);
lean_dec(x_857);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_861 = l_Lean_Meta_decLevel(x_849, x_3, x_4, x_5, x_6, x_858);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_864 = l_Lean_Meta_decLevel(x_859, x_3, x_4, x_5, x_6, x_863);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; uint8_t x_867; lean_object* x_868; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_862);
x_868 = l_Lean_Meta_checkpointDefEq___at_Lean_Meta_isLevelDefEq___spec__1(x_862, x_865, x_867, x_3, x_4, x_5, x_6, x_866);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; uint8_t x_870; 
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_unbox(x_869);
lean_dec(x_869);
if (x_870 == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_850);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_871 = lean_ctor_get(x_868, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_872 = x_868;
} else {
 lean_dec_ref(x_868);
 x_872 = lean_box(0);
}
x_873 = lean_box(0);
if (lean_is_scalar(x_872)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_872;
}
lean_ctor_set(x_874, 0, x_873);
lean_ctor_set(x_874, 1, x_871);
return x_874;
}
else
{
lean_object* x_875; lean_object* x_876; 
x_875 = lean_ctor_get(x_868, 1);
lean_inc(x_875);
lean_dec(x_868);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_876 = l_Lean_Meta_decLevel(x_850, x_3, x_4, x_5, x_6, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
lean_dec(x_876);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_879 = l_Lean_Meta_decLevel(x_860, x_3, x_4, x_5, x_6, x_878);
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_879, 1);
lean_inc(x_881);
lean_dec(x_879);
x_882 = lean_box(0);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_880);
lean_ctor_set(x_883, 1, x_882);
x_884 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_884, 0, x_877);
lean_ctor_set(x_884, 1, x_883);
x_885 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_885, 0, x_862);
lean_ctor_set(x_885, 1, x_884);
x_886 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
x_887 = l_Lean_Expr_const___override(x_886, x_885);
x_888 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_819);
x_889 = lean_array_push(x_888, x_819);
lean_inc(x_808);
x_890 = lean_array_push(x_889, x_808);
x_891 = l_Lean_mkAppN(x_887, x_890);
x_892 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_893 = l_Lean_Meta_trySynthInstance(x_891, x_892, x_3, x_4, x_5, x_6, x_881);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
if (lean_obj_tag(x_894) == 1)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec(x_893);
x_896 = lean_ctor_get(x_894, 0);
lean_inc(x_896);
lean_dec(x_894);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_820);
x_897 = l_Lean_Meta_getDecLevel(x_820, x_3, x_4, x_5, x_6, x_895);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
lean_dec(x_897);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_900 = l_Lean_Meta_getDecLevel(x_23, x_3, x_4, x_5, x_6, x_899);
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
lean_inc(x_17);
x_903 = l_Lean_Meta_getDecLevel(x_17, x_3, x_4, x_5, x_6, x_902);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_903, 1);
lean_inc(x_905);
lean_dec(x_903);
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_904);
lean_ctor_set(x_906, 1, x_882);
x_907 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_907, 0, x_901);
lean_ctor_set(x_907, 1, x_906);
x_908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_908, 0, x_898);
lean_ctor_set(x_908, 1, x_907);
x_909 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_908);
x_910 = l_Lean_Expr_const___override(x_909, x_908);
x_911 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_819);
x_912 = lean_array_push(x_911, x_819);
lean_inc(x_808);
x_913 = lean_array_push(x_912, x_808);
lean_inc(x_896);
x_914 = lean_array_push(x_913, x_896);
lean_inc(x_820);
x_915 = lean_array_push(x_914, x_820);
lean_inc(x_1);
x_916 = lean_array_push(x_915, x_1);
x_917 = l_Lean_mkAppN(x_910, x_916);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_917);
x_918 = lean_infer_type(x_917, x_3, x_4, x_5, x_6, x_905);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec(x_918);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_921 = l_Lean_Meta_isExprDefEq(x_17, x_919, x_3, x_4, x_5, x_6, x_920);
if (lean_obj_tag(x_921) == 0)
{
lean_object* x_922; uint8_t x_923; 
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_unbox(x_922);
lean_dec(x_922);
if (x_923 == 0)
{
lean_object* x_924; lean_object* x_925; 
lean_dec(x_917);
lean_dec(x_817);
x_924 = lean_ctor_get(x_921, 1);
lean_inc(x_924);
lean_dec(x_921);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_808);
x_925 = l_Lean_Meta_isMonad_x3f(x_808, x_3, x_4, x_5, x_6, x_924);
if (lean_obj_tag(x_925) == 0)
{
lean_object* x_926; 
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; 
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 lean_ctor_release(x_925, 1);
 x_928 = x_925;
} else {
 lean_dec_ref(x_925);
 x_928 = lean_box(0);
}
if (lean_is_scalar(x_928)) {
 x_929 = lean_alloc_ctor(0, 2, 0);
} else {
 x_929 = x_928;
}
lean_ctor_set(x_929, 0, x_892);
lean_ctor_set(x_929, 1, x_927);
return x_929;
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_930 = lean_ctor_get(x_925, 1);
lean_inc(x_930);
lean_dec(x_925);
x_931 = lean_ctor_get(x_926, 0);
lean_inc(x_931);
lean_dec(x_926);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_820);
x_932 = l_Lean_Meta_getLevel(x_820, x_3, x_4, x_5, x_6, x_930);
if (lean_obj_tag(x_932) == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_932, 1);
lean_inc(x_934);
lean_dec(x_932);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_809);
x_935 = l_Lean_Meta_getLevel(x_809, x_3, x_4, x_5, x_6, x_934);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; uint8_t x_949; lean_object* x_950; lean_object* x_951; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
lean_dec(x_935);
x_938 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_938, 0, x_936);
lean_ctor_set(x_938, 1, x_882);
x_939 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_939, 0, x_933);
lean_ctor_set(x_939, 1, x_938);
x_940 = l_Lean_Meta_coerceSimple_x3f___closed__2;
x_941 = l_Lean_Expr_const___override(x_940, x_939);
x_942 = l_Lean_Meta_coerceSimple_x3f___closed__3;
lean_inc(x_820);
x_943 = lean_array_push(x_942, x_820);
x_944 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_945 = lean_array_push(x_943, x_944);
lean_inc(x_809);
x_946 = lean_array_push(x_945, x_809);
x_947 = l_Lean_mkAppN(x_941, x_946);
x_948 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_949 = 0;
lean_inc(x_820);
x_950 = l_Lean_Expr_forallE___override(x_948, x_820, x_947, x_949);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_951 = l_Lean_Meta_trySynthInstance(x_950, x_892, x_3, x_4, x_5, x_6, x_937);
if (lean_obj_tag(x_951) == 0)
{
lean_object* x_952; 
x_952 = lean_ctor_get(x_951, 0);
lean_inc(x_952);
if (lean_obj_tag(x_952) == 1)
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_953 = lean_ctor_get(x_951, 1);
lean_inc(x_953);
lean_dec(x_951);
x_954 = lean_ctor_get(x_952, 0);
lean_inc(x_954);
lean_dec(x_952);
x_955 = l_Lean_Meta_coerceMonadLift_x3f___closed__13;
x_956 = l_Lean_Expr_const___override(x_955, x_908);
x_957 = l_Lean_Meta_coerceMonadLift_x3f___closed__14;
x_958 = lean_array_push(x_957, x_819);
x_959 = lean_array_push(x_958, x_808);
x_960 = lean_array_push(x_959, x_820);
x_961 = lean_array_push(x_960, x_809);
x_962 = lean_array_push(x_961, x_896);
x_963 = lean_array_push(x_962, x_954);
x_964 = lean_array_push(x_963, x_931);
x_965 = lean_array_push(x_964, x_1);
x_966 = l_Lean_mkAppN(x_956, x_965);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_967 = l_Lean_Meta_expandCoe(x_966, x_3, x_4, x_5, x_6, x_953);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
lean_dec(x_967);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_968);
x_970 = lean_infer_type(x_968, x_3, x_4, x_5, x_6, x_969);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec(x_970);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_973 = l_Lean_Meta_isExprDefEq(x_17, x_971, x_3, x_4, x_5, x_6, x_972);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; uint8_t x_975; 
lean_dec(x_825);
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_unbox(x_974);
lean_dec(x_974);
if (x_975 == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; 
lean_dec(x_968);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_976 = lean_ctor_get(x_973, 1);
lean_inc(x_976);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 x_977 = x_973;
} else {
 lean_dec_ref(x_973);
 x_977 = lean_box(0);
}
if (lean_is_scalar(x_977)) {
 x_978 = lean_alloc_ctor(0, 2, 0);
} else {
 x_978 = x_977;
}
lean_ctor_set(x_978, 0, x_892);
lean_ctor_set(x_978, 1, x_976);
return x_978;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_979 = lean_ctor_get(x_973, 1);
lean_inc(x_979);
lean_dec(x_973);
x_980 = lean_box(0);
x_981 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_968, x_980, x_3, x_4, x_5, x_6, x_979);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_982);
lean_ctor_set(x_985, 1, x_983);
return x_985;
}
}
else
{
lean_object* x_986; lean_object* x_987; 
lean_dec(x_968);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_986 = lean_ctor_get(x_973, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_973, 1);
lean_inc(x_987);
lean_dec(x_973);
x_831 = x_986;
x_832 = x_987;
goto block_840;
}
}
else
{
lean_object* x_988; lean_object* x_989; 
lean_dec(x_968);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_988 = lean_ctor_get(x_970, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_970, 1);
lean_inc(x_989);
lean_dec(x_970);
x_831 = x_988;
x_832 = x_989;
goto block_840;
}
}
else
{
lean_object* x_990; lean_object* x_991; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_990 = lean_ctor_get(x_967, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_967, 1);
lean_inc(x_991);
lean_dec(x_967);
x_831 = x_990;
x_832 = x_991;
goto block_840;
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_952);
lean_dec(x_931);
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_992 = lean_ctor_get(x_951, 1);
lean_inc(x_992);
if (lean_is_exclusive(x_951)) {
 lean_ctor_release(x_951, 0);
 lean_ctor_release(x_951, 1);
 x_993 = x_951;
} else {
 lean_dec_ref(x_951);
 x_993 = lean_box(0);
}
if (lean_is_scalar(x_993)) {
 x_994 = lean_alloc_ctor(0, 2, 0);
} else {
 x_994 = x_993;
}
lean_ctor_set(x_994, 0, x_892);
lean_ctor_set(x_994, 1, x_992);
return x_994;
}
}
else
{
lean_object* x_995; lean_object* x_996; 
lean_dec(x_931);
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_995 = lean_ctor_get(x_951, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_951, 1);
lean_inc(x_996);
lean_dec(x_951);
x_831 = x_995;
x_832 = x_996;
goto block_840;
}
}
else
{
lean_object* x_997; lean_object* x_998; 
lean_dec(x_933);
lean_dec(x_931);
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_997 = lean_ctor_get(x_935, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_935, 1);
lean_inc(x_998);
lean_dec(x_935);
x_831 = x_997;
x_832 = x_998;
goto block_840;
}
}
else
{
lean_object* x_999; lean_object* x_1000; 
lean_dec(x_931);
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_999 = lean_ctor_get(x_932, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_932, 1);
lean_inc(x_1000);
lean_dec(x_932);
x_831 = x_999;
x_832 = x_1000;
goto block_840;
}
}
}
else
{
lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1001 = lean_ctor_get(x_925, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_925, 1);
lean_inc(x_1002);
lean_dec(x_925);
x_831 = x_1001;
x_832 = x_1002;
goto block_840;
}
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1003 = lean_ctor_get(x_921, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 x_1004 = x_921;
} else {
 lean_dec_ref(x_921);
 x_1004 = lean_box(0);
}
if (lean_is_scalar(x_817)) {
 x_1005 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1005 = x_817;
}
lean_ctor_set(x_1005, 0, x_917);
if (lean_is_scalar(x_1004)) {
 x_1006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1006 = x_1004;
}
lean_ctor_set(x_1006, 0, x_1005);
lean_ctor_set(x_1006, 1, x_1003);
return x_1006;
}
}
else
{
lean_object* x_1007; lean_object* x_1008; 
lean_dec(x_917);
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1007 = lean_ctor_get(x_921, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_921, 1);
lean_inc(x_1008);
lean_dec(x_921);
x_831 = x_1007;
x_832 = x_1008;
goto block_840;
}
}
else
{
lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_917);
lean_dec(x_908);
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1009 = lean_ctor_get(x_918, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_918, 1);
lean_inc(x_1010);
lean_dec(x_918);
x_831 = x_1009;
x_832 = x_1010;
goto block_840;
}
}
else
{
lean_object* x_1011; lean_object* x_1012; 
lean_dec(x_901);
lean_dec(x_898);
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1011 = lean_ctor_get(x_903, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_903, 1);
lean_inc(x_1012);
lean_dec(x_903);
x_831 = x_1011;
x_832 = x_1012;
goto block_840;
}
}
else
{
lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_898);
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1013 = lean_ctor_get(x_900, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_900, 1);
lean_inc(x_1014);
lean_dec(x_900);
x_831 = x_1013;
x_832 = x_1014;
goto block_840;
}
}
else
{
lean_object* x_1015; lean_object* x_1016; 
lean_dec(x_896);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1015 = lean_ctor_get(x_897, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_897, 1);
lean_inc(x_1016);
lean_dec(x_897);
x_831 = x_1015;
x_832 = x_1016;
goto block_840;
}
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
lean_dec(x_894);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1017 = lean_ctor_get(x_893, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_1018 = x_893;
} else {
 lean_dec_ref(x_893);
 x_1018 = lean_box(0);
}
if (lean_is_scalar(x_1018)) {
 x_1019 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1019 = x_1018;
}
lean_ctor_set(x_1019, 0, x_892);
lean_ctor_set(x_1019, 1, x_1017);
return x_1019;
}
}
else
{
lean_object* x_1020; lean_object* x_1021; 
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1020 = lean_ctor_get(x_893, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_893, 1);
lean_inc(x_1021);
lean_dec(x_893);
x_831 = x_1020;
x_832 = x_1021;
goto block_840;
}
}
else
{
lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_877);
lean_dec(x_862);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1022 = lean_ctor_get(x_879, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_879, 1);
lean_inc(x_1023);
lean_dec(x_879);
x_831 = x_1022;
x_832 = x_1023;
goto block_840;
}
}
else
{
lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1024 = lean_ctor_get(x_876, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_876, 1);
lean_inc(x_1025);
lean_dec(x_876);
x_831 = x_1024;
x_832 = x_1025;
goto block_840;
}
}
}
else
{
lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_850);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1026 = lean_ctor_get(x_868, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_868, 1);
lean_inc(x_1027);
lean_dec(x_868);
x_831 = x_1026;
x_832 = x_1027;
goto block_840;
}
}
else
{
lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_850);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1028 = lean_ctor_get(x_864, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_864, 1);
lean_inc(x_1029);
lean_dec(x_864);
x_831 = x_1028;
x_832 = x_1029;
goto block_840;
}
}
else
{
lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_860);
lean_dec(x_859);
lean_dec(x_850);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1030 = lean_ctor_get(x_861, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_861, 1);
lean_inc(x_1031);
lean_dec(x_861);
x_831 = x_1030;
x_832 = x_1031;
goto block_840;
}
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1032 = lean_ctor_get(x_854, 1);
lean_inc(x_1032);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_1033 = x_854;
} else {
 lean_dec_ref(x_854);
 x_1033 = lean_box(0);
}
x_1034 = lean_box(0);
if (lean_is_scalar(x_1033)) {
 x_1035 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1035 = x_1033;
}
lean_ctor_set(x_1035, 0, x_1034);
lean_ctor_set(x_1035, 1, x_1032);
return x_1035;
}
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1036 = lean_ctor_get(x_854, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_1037 = x_854;
} else {
 lean_dec_ref(x_854);
 x_1037 = lean_box(0);
}
x_1038 = lean_box(0);
if (lean_is_scalar(x_1037)) {
 x_1039 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1039 = x_1037;
}
lean_ctor_set(x_1039, 0, x_1038);
lean_ctor_set(x_1039, 1, x_1036);
return x_1039;
}
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_855);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1040 = lean_ctor_get(x_854, 1);
lean_inc(x_1040);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_1041 = x_854;
} else {
 lean_dec_ref(x_854);
 x_1041 = lean_box(0);
}
x_1042 = lean_box(0);
if (lean_is_scalar(x_1041)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_1041;
}
lean_ctor_set(x_1043, 0, x_1042);
lean_ctor_set(x_1043, 1, x_1040);
return x_1043;
}
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; 
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1044 = lean_ctor_get(x_854, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_854, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_1046 = x_854;
} else {
 lean_dec_ref(x_854);
 x_1046 = lean_box(0);
}
x_1047 = l_Lean_Exception_isRuntime(x_1044);
if (x_1047 == 0)
{
lean_object* x_1048; lean_object* x_1049; 
lean_dec(x_1044);
lean_dec(x_5);
x_1048 = lean_box(0);
if (lean_is_scalar(x_1046)) {
 x_1049 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1049 = x_1046;
 lean_ctor_set_tag(x_1049, 0);
}
lean_ctor_set(x_1049, 0, x_1048);
lean_ctor_set(x_1049, 1, x_1045);
return x_1049;
}
else
{
uint8_t x_1050; 
x_1050 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_1050 == 0)
{
lean_object* x_1051; 
if (lean_is_scalar(x_1046)) {
 x_1051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1051 = x_1046;
}
lean_ctor_set(x_1051, 0, x_1044);
lean_ctor_set(x_1051, 1, x_1045);
return x_1051;
}
else
{
lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_1044);
x_1052 = lean_box(0);
if (lean_is_scalar(x_1046)) {
 x_1053 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1053 = x_1046;
 lean_ctor_set_tag(x_1053, 0);
}
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_1045);
return x_1053;
}
}
}
}
else
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; uint8_t x_1057; 
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1054 = lean_ctor_get(x_851, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_851, 1);
lean_inc(x_1055);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_1056 = x_851;
} else {
 lean_dec_ref(x_851);
 x_1056 = lean_box(0);
}
x_1057 = l_Lean_Exception_isRuntime(x_1054);
if (x_1057 == 0)
{
lean_object* x_1058; lean_object* x_1059; 
lean_dec(x_1054);
lean_dec(x_5);
x_1058 = lean_box(0);
if (lean_is_scalar(x_1056)) {
 x_1059 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1059 = x_1056;
 lean_ctor_set_tag(x_1059, 0);
}
lean_ctor_set(x_1059, 0, x_1058);
lean_ctor_set(x_1059, 1, x_1055);
return x_1059;
}
else
{
uint8_t x_1060; 
x_1060 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_1060 == 0)
{
lean_object* x_1061; 
if (lean_is_scalar(x_1056)) {
 x_1061 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1061 = x_1056;
}
lean_ctor_set(x_1061, 0, x_1054);
lean_ctor_set(x_1061, 1, x_1055);
return x_1061;
}
else
{
lean_object* x_1062; lean_object* x_1063; 
lean_dec(x_1054);
x_1062 = lean_box(0);
if (lean_is_scalar(x_1056)) {
 x_1063 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1063 = x_1056;
 lean_ctor_set_tag(x_1063, 0);
}
lean_ctor_set(x_1063, 0, x_1062);
lean_ctor_set(x_1063, 1, x_1055);
return x_1063;
}
}
}
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_847);
lean_dec(x_846);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1064 = lean_ctor_get(x_844, 1);
lean_inc(x_1064);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_1065 = x_844;
} else {
 lean_dec_ref(x_844);
 x_1065 = lean_box(0);
}
x_1066 = lean_box(0);
if (lean_is_scalar(x_1065)) {
 x_1067 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1067 = x_1065;
}
lean_ctor_set(x_1067, 0, x_1066);
lean_ctor_set(x_1067, 1, x_1064);
return x_1067;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_846);
lean_dec(x_845);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1068 = lean_ctor_get(x_844, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_1069 = x_844;
} else {
 lean_dec_ref(x_844);
 x_1069 = lean_box(0);
}
x_1070 = lean_box(0);
if (lean_is_scalar(x_1069)) {
 x_1071 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1071 = x_1069;
}
lean_ctor_set(x_1071, 0, x_1070);
lean_ctor_set(x_1071, 1, x_1068);
return x_1071;
}
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_845);
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1072 = lean_ctor_get(x_844, 1);
lean_inc(x_1072);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_1073 = x_844;
} else {
 lean_dec_ref(x_844);
 x_1073 = lean_box(0);
}
x_1074 = lean_box(0);
if (lean_is_scalar(x_1073)) {
 x_1075 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1075 = x_1073;
}
lean_ctor_set(x_1075, 0, x_1074);
lean_ctor_set(x_1075, 1, x_1072);
return x_1075;
}
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; uint8_t x_1079; 
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1076 = lean_ctor_get(x_844, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_844, 1);
lean_inc(x_1077);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_1078 = x_844;
} else {
 lean_dec_ref(x_844);
 x_1078 = lean_box(0);
}
x_1079 = l_Lean_Exception_isRuntime(x_1076);
if (x_1079 == 0)
{
lean_object* x_1080; lean_object* x_1081; 
lean_dec(x_1076);
lean_dec(x_5);
x_1080 = lean_box(0);
if (lean_is_scalar(x_1078)) {
 x_1081 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1081 = x_1078;
 lean_ctor_set_tag(x_1081, 0);
}
lean_ctor_set(x_1081, 0, x_1080);
lean_ctor_set(x_1081, 1, x_1077);
return x_1081;
}
else
{
uint8_t x_1082; 
x_1082 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_1082 == 0)
{
lean_object* x_1083; 
if (lean_is_scalar(x_1078)) {
 x_1083 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1083 = x_1078;
}
lean_ctor_set(x_1083, 0, x_1076);
lean_ctor_set(x_1083, 1, x_1077);
return x_1083;
}
else
{
lean_object* x_1084; lean_object* x_1085; 
lean_dec(x_1076);
x_1084 = lean_box(0);
if (lean_is_scalar(x_1078)) {
 x_1085 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1085 = x_1078;
 lean_ctor_set_tag(x_1085, 0);
}
lean_ctor_set(x_1085, 0, x_1084);
lean_ctor_set(x_1085, 1, x_1077);
return x_1085;
}
}
}
}
else
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; uint8_t x_1089; 
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1086 = lean_ctor_get(x_841, 0);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_841, 1);
lean_inc(x_1087);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_1088 = x_841;
} else {
 lean_dec_ref(x_841);
 x_1088 = lean_box(0);
}
x_1089 = l_Lean_Exception_isRuntime(x_1086);
if (x_1089 == 0)
{
lean_object* x_1090; lean_object* x_1091; 
lean_dec(x_1086);
lean_dec(x_5);
x_1090 = lean_box(0);
if (lean_is_scalar(x_1088)) {
 x_1091 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1091 = x_1088;
 lean_ctor_set_tag(x_1091, 0);
}
lean_ctor_set(x_1091, 0, x_1090);
lean_ctor_set(x_1091, 1, x_1087);
return x_1091;
}
else
{
uint8_t x_1092; 
x_1092 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_1092 == 0)
{
lean_object* x_1093; 
if (lean_is_scalar(x_1088)) {
 x_1093 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1093 = x_1088;
}
lean_ctor_set(x_1093, 0, x_1086);
lean_ctor_set(x_1093, 1, x_1087);
return x_1093;
}
else
{
lean_object* x_1094; lean_object* x_1095; 
lean_dec(x_1086);
x_1094 = lean_box(0);
if (lean_is_scalar(x_1088)) {
 x_1095 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1095 = x_1088;
 lean_ctor_set_tag(x_1095, 0);
}
lean_ctor_set(x_1095, 0, x_1094);
lean_ctor_set(x_1095, 1, x_1087);
return x_1095;
}
}
}
block_840:
{
uint8_t x_833; 
x_833 = l_Lean_Exception_isRuntime(x_831);
if (x_833 == 0)
{
lean_object* x_834; lean_object* x_835; 
lean_dec(x_831);
lean_dec(x_5);
x_834 = lean_box(0);
if (lean_is_scalar(x_825)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_825;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_832);
return x_835;
}
else
{
uint8_t x_836; 
x_836 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_836 == 0)
{
lean_object* x_837; 
if (lean_is_scalar(x_825)) {
 x_837 = lean_alloc_ctor(1, 2, 0);
} else {
 x_837 = x_825;
 lean_ctor_set_tag(x_837, 1);
}
lean_ctor_set(x_837, 0, x_831);
lean_ctor_set(x_837, 1, x_832);
return x_837;
}
else
{
lean_object* x_838; lean_object* x_839; 
lean_dec(x_831);
x_838 = lean_box(0);
if (lean_is_scalar(x_825)) {
 x_839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_839 = x_825;
}
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_832);
return x_839;
}
}
}
}
}
else
{
lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_23);
lean_dec(x_17);
x_1096 = lean_ctor_get(x_821, 1);
lean_inc(x_1096);
lean_dec(x_821);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1097 = l_Lean_Meta_isMonad_x3f(x_808, x_3, x_4, x_5, x_6, x_1096);
if (lean_obj_tag(x_1097) == 0)
{
lean_object* x_1098; 
x_1098 = lean_ctor_get(x_1097, 0);
lean_inc(x_1098);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1099 = lean_ctor_get(x_1097, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_1097)) {
 lean_ctor_release(x_1097, 0);
 lean_ctor_release(x_1097, 1);
 x_1100 = x_1097;
} else {
 lean_dec_ref(x_1097);
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
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
x_1103 = lean_ctor_get(x_1097, 1);
lean_inc(x_1103);
lean_dec(x_1097);
x_1104 = lean_ctor_get(x_1098, 0);
lean_inc(x_1104);
if (lean_is_exclusive(x_1098)) {
 lean_ctor_release(x_1098, 0);
 x_1105 = x_1098;
} else {
 lean_dec_ref(x_1098);
 x_1105 = lean_box(0);
}
if (lean_is_scalar(x_1105)) {
 x_1106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1106 = x_1105;
}
lean_ctor_set(x_1106, 0, x_819);
if (lean_is_scalar(x_817)) {
 x_1107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1107 = x_817;
}
lean_ctor_set(x_1107, 0, x_820);
x_1108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1108, 0, x_809);
x_1109 = lean_box(0);
x_1110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1110, 0, x_1104);
x_1111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1111, 0, x_1);
x_1112 = l_Lean_Meta_coerceMonadLift_x3f___closed__17;
x_1113 = lean_array_push(x_1112, x_1106);
x_1114 = lean_array_push(x_1113, x_1107);
x_1115 = lean_array_push(x_1114, x_1108);
x_1116 = lean_array_push(x_1115, x_1109);
x_1117 = lean_array_push(x_1116, x_1110);
x_1118 = lean_array_push(x_1117, x_1111);
x_1119 = l_Lean_Meta_coerceMonadLift_x3f___closed__16;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1120 = l_Lean_Meta_mkAppOptM(x_1119, x_1118, x_3, x_4, x_5, x_6, x_1103);
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1120, 0);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_1120, 1);
lean_inc(x_1122);
lean_dec(x_1120);
lean_inc(x_5);
x_1123 = l_Lean_Meta_expandCoe(x_1121, x_3, x_4, x_5, x_6, x_1122);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
lean_dec(x_5);
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1123, 1);
lean_inc(x_1125);
lean_dec(x_1123);
x_1126 = lean_box(0);
x_1127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1127, 0, x_1124);
lean_ctor_set(x_1127, 1, x_1126);
x_8 = x_1127;
x_9 = x_1125;
goto block_15;
}
else
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; uint8_t x_1131; 
x_1128 = lean_ctor_get(x_1123, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1123, 1);
lean_inc(x_1129);
if (lean_is_exclusive(x_1123)) {
 lean_ctor_release(x_1123, 0);
 lean_ctor_release(x_1123, 1);
 x_1130 = x_1123;
} else {
 lean_dec_ref(x_1123);
 x_1130 = lean_box(0);
}
x_1131 = l_Lean_Exception_isRuntime(x_1128);
if (x_1131 == 0)
{
lean_object* x_1132; 
lean_dec(x_1130);
lean_dec(x_1128);
lean_dec(x_5);
x_1132 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_1132;
x_9 = x_1129;
goto block_15;
}
else
{
uint8_t x_1133; 
x_1133 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_1133 == 0)
{
lean_object* x_1134; 
if (lean_is_scalar(x_1130)) {
 x_1134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1134 = x_1130;
}
lean_ctor_set(x_1134, 0, x_1128);
lean_ctor_set(x_1134, 1, x_1129);
return x_1134;
}
else
{
lean_object* x_1135; 
lean_dec(x_1130);
lean_dec(x_1128);
x_1135 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_1135;
x_9 = x_1129;
goto block_15;
}
}
}
}
else
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1136 = lean_ctor_get(x_1120, 0);
lean_inc(x_1136);
x_1137 = lean_ctor_get(x_1120, 1);
lean_inc(x_1137);
if (lean_is_exclusive(x_1120)) {
 lean_ctor_release(x_1120, 0);
 lean_ctor_release(x_1120, 1);
 x_1138 = x_1120;
} else {
 lean_dec_ref(x_1120);
 x_1138 = lean_box(0);
}
x_1139 = l_Lean_Exception_isRuntime(x_1136);
if (x_1139 == 0)
{
lean_object* x_1140; 
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_5);
x_1140 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_1140;
x_9 = x_1137;
goto block_15;
}
else
{
uint8_t x_1141; 
x_1141 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_1141 == 0)
{
lean_object* x_1142; 
if (lean_is_scalar(x_1138)) {
 x_1142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1142 = x_1138;
}
lean_ctor_set(x_1142, 0, x_1136);
lean_ctor_set(x_1142, 1, x_1137);
return x_1142;
}
else
{
lean_object* x_1143; 
lean_dec(x_1138);
lean_dec(x_1136);
x_1143 = l_Lean_Meta_coerceMonadLift_x3f___closed__18;
x_8 = x_1143;
x_9 = x_1137;
goto block_15;
}
}
}
}
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1144 = lean_ctor_get(x_1097, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1097, 1);
lean_inc(x_1145);
if (lean_is_exclusive(x_1097)) {
 lean_ctor_release(x_1097, 0);
 lean_ctor_release(x_1097, 1);
 x_1146 = x_1097;
} else {
 lean_dec_ref(x_1097);
 x_1146 = lean_box(0);
}
if (lean_is_scalar(x_1146)) {
 x_1147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1147 = x_1146;
}
lean_ctor_set(x_1147, 0, x_1144);
lean_ctor_set(x_1147, 1, x_1145);
return x_1147;
}
}
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_817);
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1148 = lean_ctor_get(x_821, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_821, 1);
lean_inc(x_1149);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_1150 = x_821;
} else {
 lean_dec_ref(x_821);
 x_1150 = lean_box(0);
}
if (lean_is_scalar(x_1150)) {
 x_1151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1151 = x_1150;
}
lean_ctor_set(x_1151, 0, x_1148);
lean_ctor_set(x_1151, 1, x_1149);
return x_1151;
}
}
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_809);
lean_dec(x_808);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1152 = lean_ctor_get(x_810, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_810, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_1154 = x_810;
} else {
 lean_dec_ref(x_810);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_1152);
lean_ctor_set(x_1155, 1, x_1153);
return x_1155;
}
}
}
}
else
{
uint8_t x_1156; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1156 = !lean_is_exclusive(x_25);
if (x_1156 == 0)
{
return x_25;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1157 = lean_ctor_get(x_25, 0);
x_1158 = lean_ctor_get(x_25, 1);
lean_inc(x_1158);
lean_inc(x_1157);
lean_dec(x_25);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_1158);
return x_1159;
}
}
}
else
{
uint8_t x_1160; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1160 = !lean_is_exclusive(x_19);
if (x_1160 == 0)
{
return x_19;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1161 = lean_ctor_get(x_19, 0);
x_1162 = lean_ctor_get(x_19, 1);
lean_inc(x_1162);
lean_inc(x_1161);
lean_dec(x_19);
x_1163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1162);
return x_1163;
}
}
block_15:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
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
l_Lean_Meta_coerceMonadLift_x3f___closed__18 = _init_l_Lean_Meta_coerceMonadLift_x3f___closed__18();
lean_mark_persistent(l_Lean_Meta_coerceMonadLift_x3f___closed__18);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
