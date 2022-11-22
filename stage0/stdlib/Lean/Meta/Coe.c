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
static lean_object* l_Lean_Meta_isCoeDecl___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__3;
static lean_object* l_Lean_Meta_isCoeDecl___closed__1;
static lean_object* l_Lean_Meta_isCoeDecl___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_isCoeDecl___closed__8;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__6;
static lean_object* l_Lean_Meta_isCoeDecl___closed__25;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__2;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__10;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__5;
static lean_object* l_Lean_Meta_isCoeDecl___closed__14;
static lean_object* l_Lean_Meta_trySynthInstanceForCoe___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__4;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_trySynthInstanceForCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__7;
static lean_object* l_Lean_Meta_isCoeDecl___closed__4;
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_expandCoe___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__5;
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__12;
static lean_object* l_Lean_Meta_isCoeDecl___closed__15;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__10;
static lean_object* l_Lean_Meta_isCoeDecl___closed__18;
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_95____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__13;
static lean_object* l_Lean_Meta_isCoeDecl___closed__23;
static lean_object* l_Lean_Meta_isCoeDecl___closed__24;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__3;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__1;
uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__20;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__7;
static lean_object* l_Lean_Meta_isCoeDecl___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__8;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_maxCoeSize;
static lean_object* l_Lean_Meta_isCoeDecl___closed__12;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__4;
static lean_object* l_Lean_Meta_isCoeDecl___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338_(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__5;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__9;
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__1;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__8;
static lean_object* l_Lean_Meta_expandCoe___closed__2;
static lean_object* l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__2;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__4;
static lean_object* l_Lean_Meta_expandCoe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_autoLift;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object*);
static lean_object* l_Lean_Meta_expandCoe___lambda__1___closed__1;
static lean_object* l_Lean_Meta_isCoeDecl___closed__21;
static lean_object* l_Lean_Meta_isCoeDecl___closed__19;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__5;
static lean_object* l_Lean_Meta_isCoeDecl___closed__11;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__6;
static lean_object* l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__4;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__1;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__6;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__5;
static lean_object* l_Lean_Meta_isCoeDecl___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__6;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__4;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__2;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__2;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__3;
static lean_object* l_Lean_Meta_coerceSimple_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Coe", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coe", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__1;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeTC", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__4;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeHead", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__6;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeTail", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__8;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeHTCT", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__10;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeDep", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__12;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeT", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__14;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeFun", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__16;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeSort", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__18;
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Internal", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("liftCoeM", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_isCoeDecl___closed__20;
x_2 = l_Lean_Meta_isCoeDecl___closed__21;
x_3 = l_Lean_Meta_isCoeDecl___closed__22;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coeM", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_isCoeDecl___closed__20;
x_2 = l_Lean_Meta_isCoeDecl___closed__21;
x_3 = l_Lean_Meta_isCoeDecl___closed__24;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_isCoeDecl___closed__5;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_isCoeDecl___closed__7;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_isCoeDecl___closed__9;
x_9 = lean_name_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_isCoeDecl___closed__11;
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_isCoeDecl___closed__13;
x_13 = lean_name_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_isCoeDecl___closed__15;
x_15 = lean_name_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Meta_isCoeDecl___closed__17;
x_17 = lean_name_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Meta_isCoeDecl___closed__19;
x_19 = lean_name_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_isCoeDecl___closed__23;
x_21 = lean_name_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Meta_isCoeDecl___closed__25;
x_23 = lean_name_eq(x_1, x_22);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = 1;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = 1;
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = 1;
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = 1;
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = 1;
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_isCoeDecl(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Expr_constName_x21(x_7);
lean_dec(x_7);
x_13 = l_Lean_Meta_isCoeDecl(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_8, x_14, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_apply_6(x_8, x_19, x_2, x_3, x_4, x_5, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Lean_Expr_headBeta(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = l_Lean_Expr_headBeta(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
lean_ctor_set_uint8(x_8, 5, x_10);
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
uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_23 = lean_ctor_get_uint8(x_8, 0);
x_24 = lean_ctor_get_uint8(x_8, 1);
x_25 = lean_ctor_get_uint8(x_8, 2);
x_26 = lean_ctor_get_uint8(x_8, 3);
x_27 = lean_ctor_get_uint8(x_8, 4);
x_28 = lean_ctor_get_uint8(x_8, 6);
x_29 = lean_ctor_get_uint8(x_8, 7);
x_30 = lean_ctor_get_uint8(x_8, 8);
x_31 = lean_ctor_get_uint8(x_8, 9);
x_32 = lean_ctor_get_uint8(x_8, 10);
x_33 = lean_ctor_get_uint8(x_8, 11);
x_34 = lean_ctor_get_uint8(x_8, 12);
x_35 = lean_ctor_get_uint8(x_8, 13);
lean_dec(x_8);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_37, 0, x_23);
lean_ctor_set_uint8(x_37, 1, x_24);
lean_ctor_set_uint8(x_37, 2, x_25);
lean_ctor_set_uint8(x_37, 3, x_26);
lean_ctor_set_uint8(x_37, 4, x_27);
lean_ctor_set_uint8(x_37, 5, x_36);
lean_ctor_set_uint8(x_37, 6, x_28);
lean_ctor_set_uint8(x_37, 7, x_29);
lean_ctor_set_uint8(x_37, 8, x_30);
lean_ctor_set_uint8(x_37, 9, x_31);
lean_ctor_set_uint8(x_37, 10, x_32);
lean_ctor_set_uint8(x_37, 11, x_33);
lean_ctor_set_uint8(x_37, 12, x_34);
lean_ctor_set_uint8(x_37, 13, x_35);
lean_ctor_set(x_2, 0, x_37);
x_38 = l_Lean_Meta_expandCoe___closed__1;
x_39 = l_Lean_Meta_expandCoe___closed__2;
x_40 = 0;
x_41 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_38, x_39, x_40, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_48 = x_41;
} else {
 lean_dec_ref(x_41);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_ctor_get(x_2, 1);
x_52 = lean_ctor_get(x_2, 2);
x_53 = lean_ctor_get(x_2, 3);
x_54 = lean_ctor_get(x_2, 4);
x_55 = lean_ctor_get(x_2, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_2);
x_56 = lean_ctor_get_uint8(x_50, 0);
x_57 = lean_ctor_get_uint8(x_50, 1);
x_58 = lean_ctor_get_uint8(x_50, 2);
x_59 = lean_ctor_get_uint8(x_50, 3);
x_60 = lean_ctor_get_uint8(x_50, 4);
x_61 = lean_ctor_get_uint8(x_50, 6);
x_62 = lean_ctor_get_uint8(x_50, 7);
x_63 = lean_ctor_get_uint8(x_50, 8);
x_64 = lean_ctor_get_uint8(x_50, 9);
x_65 = lean_ctor_get_uint8(x_50, 10);
x_66 = lean_ctor_get_uint8(x_50, 11);
x_67 = lean_ctor_get_uint8(x_50, 12);
x_68 = lean_ctor_get_uint8(x_50, 13);
if (lean_is_exclusive(x_50)) {
 x_69 = x_50;
} else {
 lean_dec_ref(x_50);
 x_69 = lean_box(0);
}
x_70 = 3;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 0, 14);
} else {
 x_71 = x_69;
}
lean_ctor_set_uint8(x_71, 0, x_56);
lean_ctor_set_uint8(x_71, 1, x_57);
lean_ctor_set_uint8(x_71, 2, x_58);
lean_ctor_set_uint8(x_71, 3, x_59);
lean_ctor_set_uint8(x_71, 4, x_60);
lean_ctor_set_uint8(x_71, 5, x_70);
lean_ctor_set_uint8(x_71, 6, x_61);
lean_ctor_set_uint8(x_71, 7, x_62);
lean_ctor_set_uint8(x_71, 8, x_63);
lean_ctor_set_uint8(x_71, 9, x_64);
lean_ctor_set_uint8(x_71, 10, x_65);
lean_ctor_set_uint8(x_71, 11, x_66);
lean_ctor_set_uint8(x_71, 12, x_67);
lean_ctor_set_uint8(x_71, 13, x_68);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_51);
lean_ctor_set(x_72, 2, x_52);
lean_ctor_set(x_72, 3, x_53);
lean_ctor_set(x_72, 4, x_54);
lean_ctor_set(x_72, 5, x_55);
x_73 = l_Lean_Meta_expandCoe___closed__1;
x_74 = l_Lean_Meta_expandCoe___closed__2;
x_75 = 0;
x_76 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_73, x_74, x_75, x_72, x_3, x_4, x_5, x_6);
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maxCoeSize", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maximum number of instances used to construct an automatic coercion", 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_isCoeDecl___closed__20;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__6;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__7;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("autoLift", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("insert monadic lifts (i.e., `liftM` and coercions) when needed", 62);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_isCoeDecl___closed__20;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__6;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__4;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__5;
x_5 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_95____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_trySynthInstanceForCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_maxCoeSize;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySynthInstanceForCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Meta_trySynthInstanceForCoe___closed__1;
x_9 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_7, x_8);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Meta_trySynthInstance(x_1, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("could not coerce", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nto", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\ncoerced expression has wrong type:", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceSimple_x3f___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimple_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__3;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_20 = l_Lean_Meta_coerceSimple_x3f___closed__1;
lean_inc(x_19);
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = l_Lean_Meta_coerceSimple_x3f___closed__2;
lean_inc(x_9);
x_23 = lean_array_push(x_22, x_9);
lean_inc(x_1);
x_24 = lean_array_push(x_23, x_1);
lean_inc(x_2);
x_25 = lean_array_push(x_24, x_2);
x_26 = l_Lean_mkAppN(x_21, x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_Meta_trySynthInstanceForCoe(x_26, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
switch (lean_obj_tag(x_28)) {
case 0:
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = l_Lean_Meta_isCoeDecl___closed__15;
x_38 = l_Lean_Expr_const___override(x_37, x_19);
x_39 = l_Lean_Meta_coerceSimple_x3f___closed__3;
x_40 = lean_array_push(x_39, x_9);
lean_inc(x_1);
x_41 = lean_array_push(x_40, x_1);
lean_inc(x_2);
x_42 = lean_array_push(x_41, x_2);
x_43 = lean_array_push(x_42, x_36);
x_44 = l_Lean_mkAppN(x_38, x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = l_Lean_Meta_expandCoe(x_44, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_46);
x_48 = lean_infer_type(x_46, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = l_Lean_Meta_isExprDefEq(x_49, x_2, x_3, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lean_indentExpr(x_1);
x_56 = l_Lean_Meta_coerceSimple_x3f___closed__5;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Meta_coerceSimple_x3f___closed__7;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_indentExpr(x_2);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Meta_coerceSimple_x3f___closed__9;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_indentExpr(x_46);
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Meta_coerceSimple_x3f___closed__10;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_67, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_51, 1);
lean_inc(x_73);
lean_dec(x_51);
x_74 = lean_box(0);
x_75 = l_Lean_Meta_coerceSimple_x3f___lambda__1(x_46, x_74, x_3, x_4, x_5, x_6, x_73);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_51);
if (x_76 == 0)
{
return x_51;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_51, 0);
x_78 = lean_ctor_get(x_51, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_51);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_48);
if (x_80 == 0)
{
return x_48;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_48, 0);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_48);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_45);
if (x_84 == 0)
{
return x_45;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_45, 0);
x_86 = lean_ctor_get(x_45, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_45);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
default: 
{
uint8_t x_88; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_27);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_27, 0);
lean_dec(x_89);
x_90 = lean_box(2);
lean_ctor_set(x_27, 0, x_90);
return x_27;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_27, 1);
lean_inc(x_91);
lean_dec(x_27);
x_92 = lean_box(2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_27);
if (x_94 == 0)
{
return x_27;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_27, 0);
x_96 = lean_ctor_get(x_27, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_27);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_14);
if (x_98 == 0)
{
return x_14;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_14, 0);
x_100 = lean_ctor_get(x_14, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_14);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_11);
if (x_102 == 0)
{
return x_11;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_11, 0);
x_104 = lean_ctor_get(x_11, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_11);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_8);
if (x_106 == 0)
{
return x_8;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_8, 0);
x_108 = lean_ctor_get(x_8, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_8);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
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
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to coerce", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nto a function, after applying `CoeFun.coe`, result is still not a function", 75);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nthis is often due to incorrect `CoeFun` instances, the synthesized instance was", 80);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_expandCoe(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = lean_infer_type(x_9, x_3, x_4, x_5, x_6, x_10);
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
x_14 = lean_whnf(x_12, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_isForall(x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_18 = l_Lean_indentExpr(x_1);
x_19 = l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_9);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Expr_appFn_x21(x_2);
lean_dec(x_2);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_indentExpr(x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_coerceSimple_x3f___closed__10;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_32, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_9, x_38, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_coerceToFunction_x3f___closed__1;
lean_inc(x_1);
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_isCoeDecl___closed__17;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_coerceToFunction_x3f___lambda__2(x_1, x_11, x_2, x_3, x_4, x_5, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
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
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nto a type, after applying `CoeSort.coe`, result is still not a type", 68);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nthis is often due to incorrect `CoeSort` instances, the synthesized instance was", 81);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_expandCoe(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = lean_infer_type(x_9, x_3, x_4, x_5, x_6, x_10);
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
x_14 = lean_whnf(x_12, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_isSort(x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_18 = l_Lean_indentExpr(x_1);
x_19 = l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_9);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Expr_appFn_x21(x_2);
lean_dec(x_2);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_indentExpr(x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_coerceSimple_x3f___closed__10;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_32, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_9, x_38, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_coerceToFunction_x3f___closed__1;
lean_inc(x_1);
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_isCoeDecl___closed__19;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_coerceToSort_x3f___lambda__1(x_1, x_11, x_2, x_3, x_4, x_5, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
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
lean_ctor_set_uint8(x_7, 5, x_14);
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
x_21 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_19, x_2, x_3, x_4, x_5, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_20, x_2, x_3, x_4, x_5, x_23);
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
uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = lean_ctor_get_uint8(x_7, 0);
x_45 = lean_ctor_get_uint8(x_7, 1);
x_46 = lean_ctor_get_uint8(x_7, 2);
x_47 = lean_ctor_get_uint8(x_7, 3);
x_48 = lean_ctor_get_uint8(x_7, 4);
x_49 = lean_ctor_get_uint8(x_7, 6);
x_50 = lean_ctor_get_uint8(x_7, 7);
x_51 = lean_ctor_get_uint8(x_7, 8);
x_52 = lean_ctor_get_uint8(x_7, 9);
x_53 = lean_ctor_get_uint8(x_7, 10);
x_54 = lean_ctor_get_uint8(x_7, 11);
x_55 = lean_ctor_get_uint8(x_7, 12);
x_56 = lean_ctor_get_uint8(x_7, 13);
lean_dec(x_7);
x_57 = 2;
x_58 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_58, 0, x_44);
lean_ctor_set_uint8(x_58, 1, x_45);
lean_ctor_set_uint8(x_58, 2, x_46);
lean_ctor_set_uint8(x_58, 3, x_47);
lean_ctor_set_uint8(x_58, 4, x_48);
lean_ctor_set_uint8(x_58, 5, x_57);
lean_ctor_set_uint8(x_58, 6, x_49);
lean_ctor_set_uint8(x_58, 7, x_50);
lean_ctor_set_uint8(x_58, 8, x_51);
lean_ctor_set_uint8(x_58, 9, x_52);
lean_ctor_set_uint8(x_58, 10, x_53);
lean_ctor_set_uint8(x_58, 11, x_54);
lean_ctor_set_uint8(x_58, 12, x_55);
lean_ctor_set_uint8(x_58, 13, x_56);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_8);
lean_ctor_set(x_59, 2, x_9);
lean_ctor_set(x_59, 3, x_10);
lean_ctor_set(x_59, 4, x_11);
lean_ctor_set(x_59, 5, x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = lean_whnf(x_1, x_59, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 5)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_63, x_2, x_3, x_4, x_5, x_62);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_64, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_61);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_60, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_60, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_81 = x_60;
} else {
 lean_dec_ref(x_60);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__12() {
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
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_12, x_3, x_4, x_5, x_6, x_13);
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
x_51 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_49, x_50);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_43);
x_53 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_41);
x_54 = lean_array_push(x_53, x_41);
lean_inc(x_28);
x_55 = lean_array_push(x_54, x_28);
x_56 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_57 = l_Lean_Meta_mkAppM(x_56, x_55, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_61 = l_Lean_Meta_trySynthInstance(x_58, x_60, x_3, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_65 = l_Lean_Meta_getDecLevel(x_42, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_68 = l_Lean_Meta_getDecLevel(x_15, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_71 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_77);
x_79 = l_Lean_Expr_const___override(x_78, x_77);
x_80 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_41);
x_81 = lean_array_push(x_80, x_41);
lean_inc(x_28);
x_82 = lean_array_push(x_81, x_28);
lean_inc(x_64);
x_83 = lean_array_push(x_82, x_64);
lean_inc(x_42);
x_84 = lean_array_push(x_83, x_42);
lean_inc(x_1);
x_85 = lean_array_push(x_84, x_1);
x_86 = l_Lean_mkAppN(x_79, x_85);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_86);
x_87 = lean_infer_type(x_86, x_3, x_4, x_5, x_6, x_73);
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
lean_inc(x_9);
x_90 = l_Lean_Meta_isExprDefEq(x_9, x_88, x_3, x_4, x_5, x_6, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_86);
lean_free_object(x_31);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_94 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
lean_dec(x_77);
lean_dec(x_64);
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
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_94, 0);
lean_dec(x_97);
lean_ctor_set(x_94, 0, x_60);
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_60);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
lean_dec(x_95);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_102 = l_Lean_Meta_getLevel(x_42, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_105 = l_Lean_Meta_getLevel(x_29, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_74);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Meta_coerceSimple_x3f___closed__1;
x_111 = l_Lean_Expr_const___override(x_110, x_109);
x_112 = l_Lean_Meta_coerceSimple_x3f___closed__2;
lean_inc(x_42);
x_113 = lean_array_push(x_112, x_42);
x_114 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_115 = lean_array_push(x_113, x_114);
lean_inc(x_29);
x_116 = lean_array_push(x_115, x_29);
x_117 = l_Lean_mkAppN(x_111, x_116);
x_118 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_119 = 0;
lean_inc(x_42);
x_120 = l_Lean_Expr_forallE___override(x_118, x_42, x_117, x_119);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_121 = l_Lean_Meta_trySynthInstance(x_120, x_60, x_3, x_4, x_5, x_6, x_107);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 1)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Meta_isCoeDecl___closed__23;
x_126 = l_Lean_Expr_const___override(x_125, x_77);
x_127 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_128 = lean_array_push(x_127, x_41);
x_129 = lean_array_push(x_128, x_28);
x_130 = lean_array_push(x_129, x_42);
x_131 = lean_array_push(x_130, x_29);
x_132 = lean_array_push(x_131, x_64);
x_133 = lean_array_push(x_132, x_124);
x_134 = lean_array_push(x_133, x_101);
x_135 = lean_array_push(x_134, x_1);
x_136 = l_Lean_mkAppN(x_126, x_135);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_137 = l_Lean_Meta_expandCoe(x_136, x_3, x_4, x_5, x_6, x_123);
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
lean_inc(x_138);
x_140 = lean_infer_type(x_138, x_3, x_4, x_5, x_6, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_143 = l_Lean_Meta_isExprDefEq(x_9, x_141, x_3, x_4, x_5, x_6, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
uint8_t x_146; 
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_146 = !lean_is_exclusive(x_143);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_143, 0);
lean_dec(x_147);
lean_ctor_set(x_143, 0, x_60);
return x_143;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_dec(x_143);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_60);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_dec(x_143);
x_151 = lean_box(0);
x_152 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_138, x_151, x_3, x_4, x_5, x_6, x_150);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
return x_152;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_152);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_143);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_143, 0);
lean_dec(x_158);
lean_ctor_set_tag(x_143, 0);
lean_ctor_set(x_143, 0, x_60);
return x_143;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_143, 1);
lean_inc(x_159);
lean_dec(x_143);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_60);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_138);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_161 = !lean_is_exclusive(x_140);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_140, 0);
lean_dec(x_162);
lean_ctor_set_tag(x_140, 0);
lean_ctor_set(x_140, 0, x_60);
return x_140;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_140, 1);
lean_inc(x_163);
lean_dec(x_140);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_60);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_165 = !lean_is_exclusive(x_137);
if (x_165 == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_137, 0);
lean_dec(x_166);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_60);
return x_137;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_137, 1);
lean_inc(x_167);
lean_dec(x_137);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_60);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_122);
lean_dec(x_101);
lean_dec(x_77);
lean_dec(x_64);
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
x_169 = !lean_is_exclusive(x_121);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_121, 0);
lean_dec(x_170);
lean_ctor_set(x_121, 0, x_60);
return x_121;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_121, 1);
lean_inc(x_171);
lean_dec(x_121);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_60);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_101);
lean_dec(x_77);
lean_dec(x_64);
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
x_173 = !lean_is_exclusive(x_121);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_121, 0);
lean_dec(x_174);
lean_ctor_set_tag(x_121, 0);
lean_ctor_set(x_121, 0, x_60);
return x_121;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_121, 1);
lean_inc(x_175);
lean_dec(x_121);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_60);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_77);
lean_dec(x_64);
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
x_177 = !lean_is_exclusive(x_105);
if (x_177 == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_105, 0);
lean_dec(x_178);
lean_ctor_set_tag(x_105, 0);
lean_ctor_set(x_105, 0, x_60);
return x_105;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_105, 1);
lean_inc(x_179);
lean_dec(x_105);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_60);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_101);
lean_dec(x_77);
lean_dec(x_64);
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
x_181 = !lean_is_exclusive(x_102);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_102, 0);
lean_dec(x_182);
lean_ctor_set_tag(x_102, 0);
lean_ctor_set(x_102, 0, x_60);
return x_102;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_102, 1);
lean_inc(x_183);
lean_dec(x_102);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_60);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_77);
lean_dec(x_64);
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
x_185 = !lean_is_exclusive(x_90);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_90, 0);
lean_dec(x_186);
lean_ctor_set(x_31, 0, x_86);
lean_ctor_set(x_90, 0, x_31);
return x_90;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_90, 1);
lean_inc(x_187);
lean_dec(x_90);
lean_ctor_set(x_31, 0, x_86);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_31);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_86);
lean_dec(x_77);
lean_dec(x_64);
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
x_189 = !lean_is_exclusive(x_90);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_90, 0);
lean_dec(x_190);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 0, x_60);
return x_90;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_90, 1);
lean_inc(x_191);
lean_dec(x_90);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_60);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_86);
lean_dec(x_77);
lean_dec(x_64);
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
x_193 = !lean_is_exclusive(x_87);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_87, 0);
lean_dec(x_194);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_60);
return x_87;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_87, 1);
lean_inc(x_195);
lean_dec(x_87);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_60);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_64);
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
x_197 = !lean_is_exclusive(x_71);
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_71, 0);
lean_dec(x_198);
lean_ctor_set_tag(x_71, 0);
lean_ctor_set(x_71, 0, x_60);
return x_71;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_71, 1);
lean_inc(x_199);
lean_dec(x_71);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_60);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_66);
lean_dec(x_64);
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
x_201 = !lean_is_exclusive(x_68);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_68, 0);
lean_dec(x_202);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 0, x_60);
return x_68;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_68, 1);
lean_inc(x_203);
lean_dec(x_68);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_60);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_64);
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
x_205 = !lean_is_exclusive(x_65);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_65, 0);
lean_dec(x_206);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_60);
return x_65;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_65, 1);
lean_inc(x_207);
lean_dec(x_65);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_60);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
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
x_209 = !lean_is_exclusive(x_61);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_61, 0);
lean_dec(x_210);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_61, 1);
lean_inc(x_211);
lean_dec(x_61);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_60);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
uint8_t x_213; 
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
x_213 = !lean_is_exclusive(x_61);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_61, 0);
lean_dec(x_214);
lean_ctor_set_tag(x_61, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_61, 1);
lean_inc(x_215);
lean_dec(x_61);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_60);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
uint8_t x_217; 
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
x_217 = !lean_is_exclusive(x_57);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_57, 0);
lean_dec(x_218);
x_219 = lean_box(0);
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_219);
return x_57;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_57, 1);
lean_inc(x_220);
lean_dec(x_57);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_223 = lean_ctor_get(x_43, 1);
lean_inc(x_223);
lean_dec(x_43);
x_224 = lean_ctor_get(x_5, 2);
lean_inc(x_224);
x_225 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_226 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_224, x_225);
lean_dec(x_224);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
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
x_227 = lean_box(0);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_223);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_41);
x_230 = lean_array_push(x_229, x_41);
lean_inc(x_28);
x_231 = lean_array_push(x_230, x_28);
x_232 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_233 = l_Lean_Meta_mkAppM(x_232, x_231, x_3, x_4, x_5, x_6, x_223);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_237 = l_Lean_Meta_trySynthInstance(x_234, x_236, x_3, x_4, x_5, x_6, x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 1)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
lean_dec(x_238);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_241 = l_Lean_Meta_getDecLevel(x_42, x_3, x_4, x_5, x_6, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_244 = l_Lean_Meta_getDecLevel(x_15, x_3, x_4, x_5, x_6, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_247 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_box(0);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_245);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_242);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_253);
x_255 = l_Lean_Expr_const___override(x_254, x_253);
x_256 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_41);
x_257 = lean_array_push(x_256, x_41);
lean_inc(x_28);
x_258 = lean_array_push(x_257, x_28);
lean_inc(x_240);
x_259 = lean_array_push(x_258, x_240);
lean_inc(x_42);
x_260 = lean_array_push(x_259, x_42);
lean_inc(x_1);
x_261 = lean_array_push(x_260, x_1);
x_262 = l_Lean_mkAppN(x_255, x_261);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_262);
x_263 = lean_infer_type(x_262, x_3, x_4, x_5, x_6, x_249);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_266 = l_Lean_Meta_isExprDefEq(x_9, x_264, x_3, x_4, x_5, x_6, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_unbox(x_267);
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_262);
lean_free_object(x_31);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec(x_266);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_270 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_269);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_253);
lean_dec(x_240);
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
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_236);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_270, 1);
lean_inc(x_275);
lean_dec(x_270);
x_276 = lean_ctor_get(x_271, 0);
lean_inc(x_276);
lean_dec(x_271);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_42);
x_277 = l_Lean_Meta_getLevel(x_42, x_3, x_4, x_5, x_6, x_275);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_280 = l_Lean_Meta_getLevel(x_29, x_3, x_4, x_5, x_6, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_250);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_278);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Lean_Meta_coerceSimple_x3f___closed__1;
x_286 = l_Lean_Expr_const___override(x_285, x_284);
x_287 = l_Lean_Meta_coerceSimple_x3f___closed__2;
lean_inc(x_42);
x_288 = lean_array_push(x_287, x_42);
x_289 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_290 = lean_array_push(x_288, x_289);
lean_inc(x_29);
x_291 = lean_array_push(x_290, x_29);
x_292 = l_Lean_mkAppN(x_286, x_291);
x_293 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_294 = 0;
lean_inc(x_42);
x_295 = l_Lean_Expr_forallE___override(x_293, x_42, x_292, x_294);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_296 = l_Lean_Meta_trySynthInstance(x_295, x_236, x_3, x_4, x_5, x_6, x_282);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 1)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
x_300 = l_Lean_Meta_isCoeDecl___closed__23;
x_301 = l_Lean_Expr_const___override(x_300, x_253);
x_302 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_303 = lean_array_push(x_302, x_41);
x_304 = lean_array_push(x_303, x_28);
x_305 = lean_array_push(x_304, x_42);
x_306 = lean_array_push(x_305, x_29);
x_307 = lean_array_push(x_306, x_240);
x_308 = lean_array_push(x_307, x_299);
x_309 = lean_array_push(x_308, x_276);
x_310 = lean_array_push(x_309, x_1);
x_311 = l_Lean_mkAppN(x_301, x_310);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_312 = l_Lean_Meta_expandCoe(x_311, x_3, x_4, x_5, x_6, x_298);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_313);
x_315 = lean_infer_type(x_313, x_3, x_4, x_5, x_6, x_314);
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
x_318 = l_Lean_Meta_isExprDefEq(x_9, x_316, x_3, x_4, x_5, x_6, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_unbox(x_319);
lean_dec(x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_313);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_322 = x_318;
} else {
 lean_dec_ref(x_318);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_236);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_324 = lean_ctor_get(x_318, 1);
lean_inc(x_324);
lean_dec(x_318);
x_325 = lean_box(0);
x_326 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_313, x_325, x_3, x_4, x_5, x_6, x_324);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_329 = x_326;
} else {
 lean_dec_ref(x_326);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_313);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_331 = lean_ctor_get(x_318, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_332 = x_318;
} else {
 lean_dec_ref(x_318);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_332;
 lean_ctor_set_tag(x_333, 0);
}
lean_ctor_set(x_333, 0, x_236);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_313);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_334 = lean_ctor_get(x_315, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_335 = x_315;
} else {
 lean_dec_ref(x_315);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_335;
 lean_ctor_set_tag(x_336, 0);
}
lean_ctor_set(x_336, 0, x_236);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_337 = lean_ctor_get(x_312, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_338 = x_312;
} else {
 lean_dec_ref(x_312);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_338;
 lean_ctor_set_tag(x_339, 0);
}
lean_ctor_set(x_339, 0, x_236);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_297);
lean_dec(x_276);
lean_dec(x_253);
lean_dec(x_240);
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
x_340 = lean_ctor_get(x_296, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_341 = x_296;
} else {
 lean_dec_ref(x_296);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_236);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_276);
lean_dec(x_253);
lean_dec(x_240);
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
x_343 = lean_ctor_get(x_296, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_344 = x_296;
} else {
 lean_dec_ref(x_296);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_344;
 lean_ctor_set_tag(x_345, 0);
}
lean_ctor_set(x_345, 0, x_236);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_278);
lean_dec(x_276);
lean_dec(x_253);
lean_dec(x_240);
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
x_346 = lean_ctor_get(x_280, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_347 = x_280;
} else {
 lean_dec_ref(x_280);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_347;
 lean_ctor_set_tag(x_348, 0);
}
lean_ctor_set(x_348, 0, x_236);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_276);
lean_dec(x_253);
lean_dec(x_240);
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
x_349 = lean_ctor_get(x_277, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_350 = x_277;
} else {
 lean_dec_ref(x_277);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_350;
 lean_ctor_set_tag(x_351, 0);
}
lean_ctor_set(x_351, 0, x_236);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_253);
lean_dec(x_240);
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
x_352 = lean_ctor_get(x_266, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_353 = x_266;
} else {
 lean_dec_ref(x_266);
 x_353 = lean_box(0);
}
lean_ctor_set(x_31, 0, x_262);
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_31);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_262);
lean_dec(x_253);
lean_dec(x_240);
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
x_355 = lean_ctor_get(x_266, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_356 = x_266;
} else {
 lean_dec_ref(x_266);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_356;
 lean_ctor_set_tag(x_357, 0);
}
lean_ctor_set(x_357, 0, x_236);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_262);
lean_dec(x_253);
lean_dec(x_240);
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
x_358 = lean_ctor_get(x_263, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_359 = x_263;
} else {
 lean_dec_ref(x_263);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_359;
 lean_ctor_set_tag(x_360, 0);
}
lean_ctor_set(x_360, 0, x_236);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_245);
lean_dec(x_242);
lean_dec(x_240);
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
x_361 = lean_ctor_get(x_247, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_362 = x_247;
} else {
 lean_dec_ref(x_247);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_362;
 lean_ctor_set_tag(x_363, 0);
}
lean_ctor_set(x_363, 0, x_236);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_242);
lean_dec(x_240);
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
x_364 = lean_ctor_get(x_244, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_365 = x_244;
} else {
 lean_dec_ref(x_244);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_365;
 lean_ctor_set_tag(x_366, 0);
}
lean_ctor_set(x_366, 0, x_236);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_240);
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
x_367 = lean_ctor_get(x_241, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_368 = x_241;
} else {
 lean_dec_ref(x_241);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_368;
 lean_ctor_set_tag(x_369, 0);
}
lean_ctor_set(x_369, 0, x_236);
lean_ctor_set(x_369, 1, x_367);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_238);
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
x_370 = lean_ctor_get(x_237, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_371 = x_237;
} else {
 lean_dec_ref(x_237);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_236);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
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
x_373 = lean_ctor_get(x_237, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_374 = x_237;
} else {
 lean_dec_ref(x_237);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_374;
 lean_ctor_set_tag(x_375, 0);
}
lean_ctor_set(x_375, 0, x_236);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
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
x_376 = lean_ctor_get(x_233, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_377 = x_233;
} else {
 lean_dec_ref(x_233);
 x_377 = lean_box(0);
}
x_378 = lean_box(0);
if (lean_is_scalar(x_377)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_377;
 lean_ctor_set_tag(x_379, 0);
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_376);
return x_379;
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_15);
lean_dec(x_9);
x_380 = lean_ctor_get(x_43, 1);
lean_inc(x_380);
lean_dec(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_381 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_380);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
if (lean_obj_tag(x_382) == 0)
{
uint8_t x_383; 
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
x_383 = !lean_is_exclusive(x_381);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; 
x_384 = lean_ctor_get(x_381, 0);
lean_dec(x_384);
x_385 = lean_box(0);
lean_ctor_set(x_381, 0, x_385);
return x_381;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_381, 1);
lean_inc(x_386);
lean_dec(x_381);
x_387 = lean_box(0);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
else
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_381, 1);
lean_inc(x_389);
lean_dec(x_381);
x_390 = !lean_is_exclusive(x_382);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_391 = lean_ctor_get(x_382, 0);
lean_ctor_set(x_382, 0, x_41);
lean_ctor_set(x_31, 0, x_42);
lean_ctor_set(x_18, 0, x_29);
x_392 = lean_box(0);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_391);
x_394 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_394, 0, x_1);
x_395 = l_Lean_Meta_coerceMonadLift_x3f___closed__12;
x_396 = lean_array_push(x_395, x_382);
x_397 = lean_array_push(x_396, x_31);
x_398 = lean_array_push(x_397, x_18);
x_399 = lean_array_push(x_398, x_392);
x_400 = lean_array_push(x_399, x_393);
x_401 = lean_array_push(x_400, x_394);
x_402 = l_Lean_Meta_isCoeDecl___closed__25;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_403 = l_Lean_Meta_mkAppOptM(x_402, x_401, x_3, x_4, x_5, x_6, x_389);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = l_Lean_Meta_expandCoe(x_404, x_3, x_4, x_5, x_6, x_405);
if (lean_obj_tag(x_406) == 0)
{
uint8_t x_407; 
x_407 = !lean_is_exclusive(x_406);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_406, 0);
x_409 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_406, 0, x_409);
return x_406;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_410 = lean_ctor_get(x_406, 0);
x_411 = lean_ctor_get(x_406, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_406);
x_412 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_412, 0, x_410);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
else
{
uint8_t x_414; 
x_414 = !lean_is_exclusive(x_406);
if (x_414 == 0)
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_406, 0);
lean_dec(x_415);
lean_ctor_set_tag(x_406, 0);
lean_ctor_set(x_406, 0, x_392);
return x_406;
}
else
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_406, 1);
lean_inc(x_416);
lean_dec(x_406);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_392);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
else
{
uint8_t x_418; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_418 = !lean_is_exclusive(x_403);
if (x_418 == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_403, 0);
lean_dec(x_419);
lean_ctor_set_tag(x_403, 0);
lean_ctor_set(x_403, 0, x_392);
return x_403;
}
else
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_403, 1);
lean_inc(x_420);
lean_dec(x_403);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_392);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_422 = lean_ctor_get(x_382, 0);
lean_inc(x_422);
lean_dec(x_382);
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_41);
lean_ctor_set(x_31, 0, x_42);
lean_ctor_set(x_18, 0, x_29);
x_424 = lean_box(0);
x_425 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_425, 0, x_422);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_1);
x_427 = l_Lean_Meta_coerceMonadLift_x3f___closed__12;
x_428 = lean_array_push(x_427, x_423);
x_429 = lean_array_push(x_428, x_31);
x_430 = lean_array_push(x_429, x_18);
x_431 = lean_array_push(x_430, x_424);
x_432 = lean_array_push(x_431, x_425);
x_433 = lean_array_push(x_432, x_426);
x_434 = l_Lean_Meta_isCoeDecl___closed__25;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_435 = l_Lean_Meta_mkAppOptM(x_434, x_433, x_3, x_4, x_5, x_6, x_389);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
x_438 = l_Lean_Meta_expandCoe(x_436, x_3, x_4, x_5, x_6, x_437);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_441 = x_438;
} else {
 lean_dec_ref(x_438);
 x_441 = lean_box(0);
}
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_439);
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_440);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_438, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_445 = x_438;
} else {
 lean_dec_ref(x_438);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_445;
 lean_ctor_set_tag(x_446, 0);
}
lean_ctor_set(x_446, 0, x_424);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_447 = lean_ctor_get(x_435, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_448 = x_435;
} else {
 lean_dec_ref(x_435);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_448;
 lean_ctor_set_tag(x_449, 0);
}
lean_ctor_set(x_449, 0, x_424);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
}
}
else
{
uint8_t x_450; 
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
x_450 = !lean_is_exclusive(x_43);
if (x_450 == 0)
{
return x_43;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_43, 0);
x_452 = lean_ctor_get(x_43, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_43);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_454 = lean_ctor_get(x_31, 0);
lean_inc(x_454);
lean_dec(x_31);
x_455 = lean_ctor_get(x_30, 1);
lean_inc(x_455);
lean_dec(x_30);
x_456 = lean_ctor_get(x_454, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_454, 1);
lean_inc(x_457);
lean_dec(x_454);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
lean_inc(x_456);
x_458 = l_Lean_Meta_isExprDefEq(x_456, x_28, x_3, x_4, x_5, x_6, x_455);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; uint8_t x_460; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_unbox(x_459);
lean_dec(x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; 
lean_free_object(x_18);
x_461 = lean_ctor_get(x_458, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_462 = x_458;
} else {
 lean_dec_ref(x_458);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_5, 2);
lean_inc(x_463);
x_464 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_465 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_463, x_464);
lean_dec(x_463);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_466 = lean_box(0);
if (lean_is_scalar(x_462)) {
 x_467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_467 = x_462;
}
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_461);
return x_467;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_462);
x_468 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_456);
x_469 = lean_array_push(x_468, x_456);
lean_inc(x_28);
x_470 = lean_array_push(x_469, x_28);
x_471 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_472 = l_Lean_Meta_mkAppM(x_471, x_470, x_3, x_4, x_5, x_6, x_461);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_476 = l_Lean_Meta_trySynthInstance(x_473, x_475, x_3, x_4, x_5, x_6, x_474);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
if (lean_obj_tag(x_477) == 1)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = lean_ctor_get(x_477, 0);
lean_inc(x_479);
lean_dec(x_477);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_457);
x_480 = l_Lean_Meta_getDecLevel(x_457, x_3, x_4, x_5, x_6, x_478);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_483 = l_Lean_Meta_getDecLevel(x_15, x_3, x_4, x_5, x_6, x_482);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_486 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_box(0);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_489);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_484);
lean_ctor_set(x_491, 1, x_490);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_481);
lean_ctor_set(x_492, 1, x_491);
x_493 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_492);
x_494 = l_Lean_Expr_const___override(x_493, x_492);
x_495 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_456);
x_496 = lean_array_push(x_495, x_456);
lean_inc(x_28);
x_497 = lean_array_push(x_496, x_28);
lean_inc(x_479);
x_498 = lean_array_push(x_497, x_479);
lean_inc(x_457);
x_499 = lean_array_push(x_498, x_457);
lean_inc(x_1);
x_500 = lean_array_push(x_499, x_1);
x_501 = l_Lean_mkAppN(x_494, x_500);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_501);
x_502 = lean_infer_type(x_501, x_3, x_4, x_5, x_6, x_488);
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
lean_inc(x_9);
x_505 = l_Lean_Meta_isExprDefEq(x_9, x_503, x_3, x_4, x_5, x_6, x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; uint8_t x_507; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_unbox(x_506);
lean_dec(x_506);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_501);
x_508 = lean_ctor_get(x_505, 1);
lean_inc(x_508);
lean_dec(x_505);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_509 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_508);
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_512 = x_509;
} else {
 lean_dec_ref(x_509);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_475);
lean_ctor_set(x_513, 1, x_511);
return x_513;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_509, 1);
lean_inc(x_514);
lean_dec(x_509);
x_515 = lean_ctor_get(x_510, 0);
lean_inc(x_515);
lean_dec(x_510);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_457);
x_516 = l_Lean_Meta_getLevel(x_457, x_3, x_4, x_5, x_6, x_514);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_519 = l_Lean_Meta_getLevel(x_29, x_3, x_4, x_5, x_6, x_518);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; lean_object* x_534; lean_object* x_535; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_489);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_517);
lean_ctor_set(x_523, 1, x_522);
x_524 = l_Lean_Meta_coerceSimple_x3f___closed__1;
x_525 = l_Lean_Expr_const___override(x_524, x_523);
x_526 = l_Lean_Meta_coerceSimple_x3f___closed__2;
lean_inc(x_457);
x_527 = lean_array_push(x_526, x_457);
x_528 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_529 = lean_array_push(x_527, x_528);
lean_inc(x_29);
x_530 = lean_array_push(x_529, x_29);
x_531 = l_Lean_mkAppN(x_525, x_530);
x_532 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_533 = 0;
lean_inc(x_457);
x_534 = l_Lean_Expr_forallE___override(x_532, x_457, x_531, x_533);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_535 = l_Lean_Meta_trySynthInstance(x_534, x_475, x_3, x_4, x_5, x_6, x_521);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
if (lean_obj_tag(x_536) == 1)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_538 = lean_ctor_get(x_536, 0);
lean_inc(x_538);
lean_dec(x_536);
x_539 = l_Lean_Meta_isCoeDecl___closed__23;
x_540 = l_Lean_Expr_const___override(x_539, x_492);
x_541 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_542 = lean_array_push(x_541, x_456);
x_543 = lean_array_push(x_542, x_28);
x_544 = lean_array_push(x_543, x_457);
x_545 = lean_array_push(x_544, x_29);
x_546 = lean_array_push(x_545, x_479);
x_547 = lean_array_push(x_546, x_538);
x_548 = lean_array_push(x_547, x_515);
x_549 = lean_array_push(x_548, x_1);
x_550 = l_Lean_mkAppN(x_540, x_549);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_551 = l_Lean_Meta_expandCoe(x_550, x_3, x_4, x_5, x_6, x_537);
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
lean_inc(x_552);
x_554 = lean_infer_type(x_552, x_3, x_4, x_5, x_6, x_553);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_557 = l_Lean_Meta_isExprDefEq(x_9, x_555, x_3, x_4, x_5, x_6, x_556);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; uint8_t x_559; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_unbox(x_558);
lean_dec(x_558);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_552);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_560 = lean_ctor_get(x_557, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_561 = x_557;
} else {
 lean_dec_ref(x_557);
 x_561 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_561;
}
lean_ctor_set(x_562, 0, x_475);
lean_ctor_set(x_562, 1, x_560);
return x_562;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_563 = lean_ctor_get(x_557, 1);
lean_inc(x_563);
lean_dec(x_557);
x_564 = lean_box(0);
x_565 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_552, x_564, x_3, x_4, x_5, x_6, x_563);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_568 = x_565;
} else {
 lean_dec_ref(x_565);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_552);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_570 = lean_ctor_get(x_557, 1);
lean_inc(x_570);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_571 = x_557;
} else {
 lean_dec_ref(x_557);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_571)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_571;
 lean_ctor_set_tag(x_572, 0);
}
lean_ctor_set(x_572, 0, x_475);
lean_ctor_set(x_572, 1, x_570);
return x_572;
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_552);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_573 = lean_ctor_get(x_554, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_574 = x_554;
} else {
 lean_dec_ref(x_554);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_574;
 lean_ctor_set_tag(x_575, 0);
}
lean_ctor_set(x_575, 0, x_475);
lean_ctor_set(x_575, 1, x_573);
return x_575;
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_576 = lean_ctor_get(x_551, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_577 = x_551;
} else {
 lean_dec_ref(x_551);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_577;
 lean_ctor_set_tag(x_578, 0);
}
lean_ctor_set(x_578, 0, x_475);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_536);
lean_dec(x_515);
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_579 = lean_ctor_get(x_535, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_580 = x_535;
} else {
 lean_dec_ref(x_535);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_475);
lean_ctor_set(x_581, 1, x_579);
return x_581;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_515);
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_582 = lean_ctor_get(x_535, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_583 = x_535;
} else {
 lean_dec_ref(x_535);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_584 = x_583;
 lean_ctor_set_tag(x_584, 0);
}
lean_ctor_set(x_584, 0, x_475);
lean_ctor_set(x_584, 1, x_582);
return x_584;
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_517);
lean_dec(x_515);
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_585 = lean_ctor_get(x_519, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_586 = x_519;
} else {
 lean_dec_ref(x_519);
 x_586 = lean_box(0);
}
if (lean_is_scalar(x_586)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_586;
 lean_ctor_set_tag(x_587, 0);
}
lean_ctor_set(x_587, 0, x_475);
lean_ctor_set(x_587, 1, x_585);
return x_587;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_515);
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_588 = lean_ctor_get(x_516, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_589 = x_516;
} else {
 lean_dec_ref(x_516);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_589;
 lean_ctor_set_tag(x_590, 0);
}
lean_ctor_set(x_590, 0, x_475);
lean_ctor_set(x_590, 1, x_588);
return x_590;
}
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_591 = lean_ctor_get(x_505, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_592 = x_505;
} else {
 lean_dec_ref(x_505);
 x_592 = lean_box(0);
}
x_593 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_593, 0, x_501);
if (lean_is_scalar(x_592)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_592;
}
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_591);
return x_594;
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_501);
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_595 = lean_ctor_get(x_505, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_596 = x_505;
} else {
 lean_dec_ref(x_505);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_596;
 lean_ctor_set_tag(x_597, 0);
}
lean_ctor_set(x_597, 0, x_475);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_501);
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_598 = lean_ctor_get(x_502, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_599 = x_502;
} else {
 lean_dec_ref(x_502);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_600 = x_599;
 lean_ctor_set_tag(x_600, 0);
}
lean_ctor_set(x_600, 0, x_475);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_484);
lean_dec(x_481);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_601 = lean_ctor_get(x_486, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_602 = x_486;
} else {
 lean_dec_ref(x_486);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_602;
 lean_ctor_set_tag(x_603, 0);
}
lean_ctor_set(x_603, 0, x_475);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_481);
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_604 = lean_ctor_get(x_483, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_605 = x_483;
} else {
 lean_dec_ref(x_483);
 x_605 = lean_box(0);
}
if (lean_is_scalar(x_605)) {
 x_606 = lean_alloc_ctor(0, 2, 0);
} else {
 x_606 = x_605;
 lean_ctor_set_tag(x_606, 0);
}
lean_ctor_set(x_606, 0, x_475);
lean_ctor_set(x_606, 1, x_604);
return x_606;
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_479);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_607 = lean_ctor_get(x_480, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_608 = x_480;
} else {
 lean_dec_ref(x_480);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_608;
 lean_ctor_set_tag(x_609, 0);
}
lean_ctor_set(x_609, 0, x_475);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_477);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_610 = lean_ctor_get(x_476, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_611 = x_476;
} else {
 lean_dec_ref(x_476);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_475);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_613 = lean_ctor_get(x_476, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_614 = x_476;
} else {
 lean_dec_ref(x_476);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_614;
 lean_ctor_set_tag(x_615, 0);
}
lean_ctor_set(x_615, 0, x_475);
lean_ctor_set(x_615, 1, x_613);
return x_615;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_616 = lean_ctor_get(x_472, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_617 = x_472;
} else {
 lean_dec_ref(x_472);
 x_617 = lean_box(0);
}
x_618 = lean_box(0);
if (lean_is_scalar(x_617)) {
 x_619 = lean_alloc_ctor(0, 2, 0);
} else {
 x_619 = x_617;
 lean_ctor_set_tag(x_619, 0);
}
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_616);
return x_619;
}
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_15);
lean_dec(x_9);
x_620 = lean_ctor_get(x_458, 1);
lean_inc(x_620);
lean_dec(x_458);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_621 = l_Lean_Meta_isMonad_x3f(x_28, x_3, x_4, x_5, x_6, x_620);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_29);
lean_free_object(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_624 = x_621;
} else {
 lean_dec_ref(x_621);
 x_624 = lean_box(0);
}
x_625 = lean_box(0);
if (lean_is_scalar(x_624)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_624;
}
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_623);
return x_626;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_627 = lean_ctor_get(x_621, 1);
lean_inc(x_627);
lean_dec(x_621);
x_628 = lean_ctor_get(x_622, 0);
lean_inc(x_628);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 x_629 = x_622;
} else {
 lean_dec_ref(x_622);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(1, 1, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_456);
x_631 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_631, 0, x_457);
lean_ctor_set(x_18, 0, x_29);
x_632 = lean_box(0);
x_633 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_633, 0, x_628);
x_634 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_634, 0, x_1);
x_635 = l_Lean_Meta_coerceMonadLift_x3f___closed__12;
x_636 = lean_array_push(x_635, x_630);
x_637 = lean_array_push(x_636, x_631);
x_638 = lean_array_push(x_637, x_18);
x_639 = lean_array_push(x_638, x_632);
x_640 = lean_array_push(x_639, x_633);
x_641 = lean_array_push(x_640, x_634);
x_642 = l_Lean_Meta_isCoeDecl___closed__25;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_643 = l_Lean_Meta_mkAppOptM(x_642, x_641, x_3, x_4, x_5, x_6, x_627);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_646 = l_Lean_Meta_expandCoe(x_644, x_3, x_4, x_5, x_6, x_645);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_649 = x_646;
} else {
 lean_dec_ref(x_646);
 x_649 = lean_box(0);
}
x_650 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_650, 0, x_647);
if (lean_is_scalar(x_649)) {
 x_651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_651 = x_649;
}
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_648);
return x_651;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_646, 1);
lean_inc(x_652);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_653 = x_646;
} else {
 lean_dec_ref(x_646);
 x_653 = lean_box(0);
}
if (lean_is_scalar(x_653)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_653;
 lean_ctor_set_tag(x_654, 0);
}
lean_ctor_set(x_654, 0, x_632);
lean_ctor_set(x_654, 1, x_652);
return x_654;
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_655 = lean_ctor_get(x_643, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_656 = x_643;
} else {
 lean_dec_ref(x_643);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_656;
 lean_ctor_set_tag(x_657, 0);
}
lean_ctor_set(x_657, 0, x_632);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_457);
lean_dec(x_456);
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
x_658 = lean_ctor_get(x_458, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_458, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_660 = x_458;
} else {
 lean_dec_ref(x_458);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 2, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_658);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
}
}
else
{
uint8_t x_662; 
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
x_662 = !lean_is_exclusive(x_30);
if (x_662 == 0)
{
return x_30;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_30, 0);
x_664 = lean_ctor_get(x_30, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_30);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_666 = lean_ctor_get(x_18, 0);
lean_inc(x_666);
lean_dec(x_18);
x_667 = lean_ctor_get(x_17, 1);
lean_inc(x_667);
lean_dec(x_17);
x_668 = lean_ctor_get(x_666, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_666, 1);
lean_inc(x_669);
lean_dec(x_666);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
x_670 = l_Lean_Meta_isTypeApp_x3f(x_15, x_3, x_4, x_5, x_6, x_667);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_674 = lean_box(0);
if (lean_is_scalar(x_673)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_673;
}
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_672);
return x_675;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_676 = lean_ctor_get(x_671, 0);
lean_inc(x_676);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 x_677 = x_671;
} else {
 lean_dec_ref(x_671);
 x_677 = lean_box(0);
}
x_678 = lean_ctor_get(x_670, 1);
lean_inc(x_678);
lean_dec(x_670);
x_679 = lean_ctor_get(x_676, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_676, 1);
lean_inc(x_680);
lean_dec(x_676);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_668);
lean_inc(x_679);
x_681 = l_Lean_Meta_isExprDefEq(x_679, x_668, x_3, x_4, x_5, x_6, x_678);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; uint8_t x_683; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_unbox(x_682);
lean_dec(x_682);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_684 = lean_ctor_get(x_681, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_685 = x_681;
} else {
 lean_dec_ref(x_681);
 x_685 = lean_box(0);
}
x_686 = lean_ctor_get(x_5, 2);
lean_inc(x_686);
x_687 = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
x_688 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_686, x_687);
lean_dec(x_686);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; 
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_689 = lean_box(0);
if (lean_is_scalar(x_685)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_685;
}
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_684);
return x_690;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_685);
x_691 = l_Lean_Meta_coerceMonadLift_x3f___closed__4;
lean_inc(x_679);
x_692 = lean_array_push(x_691, x_679);
lean_inc(x_668);
x_693 = lean_array_push(x_692, x_668);
x_694 = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_695 = l_Lean_Meta_mkAppM(x_694, x_693, x_3, x_4, x_5, x_6, x_684);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_699 = l_Lean_Meta_trySynthInstance(x_696, x_698, x_3, x_4, x_5, x_6, x_697);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
if (lean_obj_tag(x_700) == 1)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_ctor_get(x_700, 0);
lean_inc(x_702);
lean_dec(x_700);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_680);
x_703 = l_Lean_Meta_getDecLevel(x_680, x_3, x_4, x_5, x_6, x_701);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_706 = l_Lean_Meta_getDecLevel(x_15, x_3, x_4, x_5, x_6, x_705);
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
lean_inc(x_9);
x_709 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_708);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
x_712 = lean_box(0);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_710);
lean_ctor_set(x_713, 1, x_712);
x_714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_714, 0, x_707);
lean_ctor_set(x_714, 1, x_713);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_704);
lean_ctor_set(x_715, 1, x_714);
x_716 = l_Lean_Meta_coerceMonadLift_x3f___closed__6;
lean_inc(x_715);
x_717 = l_Lean_Expr_const___override(x_716, x_715);
x_718 = l_Lean_Meta_coerceMonadLift_x3f___closed__7;
lean_inc(x_679);
x_719 = lean_array_push(x_718, x_679);
lean_inc(x_668);
x_720 = lean_array_push(x_719, x_668);
lean_inc(x_702);
x_721 = lean_array_push(x_720, x_702);
lean_inc(x_680);
x_722 = lean_array_push(x_721, x_680);
lean_inc(x_1);
x_723 = lean_array_push(x_722, x_1);
x_724 = l_Lean_mkAppN(x_717, x_723);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_724);
x_725 = lean_infer_type(x_724, x_3, x_4, x_5, x_6, x_711);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
lean_dec(x_725);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_728 = l_Lean_Meta_isExprDefEq(x_9, x_726, x_3, x_4, x_5, x_6, x_727);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; uint8_t x_730; 
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_unbox(x_729);
lean_dec(x_729);
if (x_730 == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; 
lean_dec(x_724);
lean_dec(x_677);
x_731 = lean_ctor_get(x_728, 1);
lean_inc(x_731);
lean_dec(x_728);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_668);
x_732 = l_Lean_Meta_isMonad_x3f(x_668, x_3, x_4, x_5, x_6, x_731);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_715);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_732)) {
 lean_ctor_release(x_732, 0);
 lean_ctor_release(x_732, 1);
 x_735 = x_732;
} else {
 lean_dec_ref(x_732);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_698);
lean_ctor_set(x_736, 1, x_734);
return x_736;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_732, 1);
lean_inc(x_737);
lean_dec(x_732);
x_738 = lean_ctor_get(x_733, 0);
lean_inc(x_738);
lean_dec(x_733);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_680);
x_739 = l_Lean_Meta_getLevel(x_680, x_3, x_4, x_5, x_6, x_737);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_669);
x_742 = l_Lean_Meta_getLevel(x_669, x_3, x_4, x_5, x_6, x_741);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint8_t x_756; lean_object* x_757; lean_object* x_758; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
lean_dec(x_742);
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_743);
lean_ctor_set(x_745, 1, x_712);
x_746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_746, 0, x_740);
lean_ctor_set(x_746, 1, x_745);
x_747 = l_Lean_Meta_coerceSimple_x3f___closed__1;
x_748 = l_Lean_Expr_const___override(x_747, x_746);
x_749 = l_Lean_Meta_coerceSimple_x3f___closed__2;
lean_inc(x_680);
x_750 = lean_array_push(x_749, x_680);
x_751 = l_Lean_Meta_coerceMonadLift_x3f___closed__10;
x_752 = lean_array_push(x_750, x_751);
lean_inc(x_669);
x_753 = lean_array_push(x_752, x_669);
x_754 = l_Lean_mkAppN(x_748, x_753);
x_755 = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
x_756 = 0;
lean_inc(x_680);
x_757 = l_Lean_Expr_forallE___override(x_755, x_680, x_754, x_756);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_758 = l_Lean_Meta_trySynthInstance(x_757, x_698, x_3, x_4, x_5, x_6, x_744);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
if (lean_obj_tag(x_759) == 1)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = lean_ctor_get(x_759, 0);
lean_inc(x_761);
lean_dec(x_759);
x_762 = l_Lean_Meta_isCoeDecl___closed__23;
x_763 = l_Lean_Expr_const___override(x_762, x_715);
x_764 = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
x_765 = lean_array_push(x_764, x_679);
x_766 = lean_array_push(x_765, x_668);
x_767 = lean_array_push(x_766, x_680);
x_768 = lean_array_push(x_767, x_669);
x_769 = lean_array_push(x_768, x_702);
x_770 = lean_array_push(x_769, x_761);
x_771 = lean_array_push(x_770, x_738);
x_772 = lean_array_push(x_771, x_1);
x_773 = l_Lean_mkAppN(x_763, x_772);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_774 = l_Lean_Meta_expandCoe(x_773, x_3, x_4, x_5, x_6, x_760);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
lean_dec(x_774);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_775);
x_777 = lean_infer_type(x_775, x_3, x_4, x_5, x_6, x_776);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_780 = l_Lean_Meta_isExprDefEq(x_9, x_778, x_3, x_4, x_5, x_6, x_779);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; uint8_t x_782; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_unbox(x_781);
lean_dec(x_781);
if (x_782 == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_775);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_783 = lean_ctor_get(x_780, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_784 = x_780;
} else {
 lean_dec_ref(x_780);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_698);
lean_ctor_set(x_785, 1, x_783);
return x_785;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_786 = lean_ctor_get(x_780, 1);
lean_inc(x_786);
lean_dec(x_780);
x_787 = lean_box(0);
x_788 = l_Lean_Meta_coerceToFunction_x3f___lambda__1(x_775, x_787, x_3, x_4, x_5, x_6, x_786);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_791 = x_788;
} else {
 lean_dec_ref(x_788);
 x_791 = lean_box(0);
}
if (lean_is_scalar(x_791)) {
 x_792 = lean_alloc_ctor(0, 2, 0);
} else {
 x_792 = x_791;
}
lean_ctor_set(x_792, 0, x_789);
lean_ctor_set(x_792, 1, x_790);
return x_792;
}
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_775);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_793 = lean_ctor_get(x_780, 1);
lean_inc(x_793);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_794 = x_780;
} else {
 lean_dec_ref(x_780);
 x_794 = lean_box(0);
}
if (lean_is_scalar(x_794)) {
 x_795 = lean_alloc_ctor(0, 2, 0);
} else {
 x_795 = x_794;
 lean_ctor_set_tag(x_795, 0);
}
lean_ctor_set(x_795, 0, x_698);
lean_ctor_set(x_795, 1, x_793);
return x_795;
}
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_775);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_796 = lean_ctor_get(x_777, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_777)) {
 lean_ctor_release(x_777, 0);
 lean_ctor_release(x_777, 1);
 x_797 = x_777;
} else {
 lean_dec_ref(x_777);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_798 = x_797;
 lean_ctor_set_tag(x_798, 0);
}
lean_ctor_set(x_798, 0, x_698);
lean_ctor_set(x_798, 1, x_796);
return x_798;
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_799 = lean_ctor_get(x_774, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_800 = x_774;
} else {
 lean_dec_ref(x_774);
 x_800 = lean_box(0);
}
if (lean_is_scalar(x_800)) {
 x_801 = lean_alloc_ctor(0, 2, 0);
} else {
 x_801 = x_800;
 lean_ctor_set_tag(x_801, 0);
}
lean_ctor_set(x_801, 0, x_698);
lean_ctor_set(x_801, 1, x_799);
return x_801;
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_dec(x_759);
lean_dec(x_738);
lean_dec(x_715);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_802 = lean_ctor_get(x_758, 1);
lean_inc(x_802);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_803 = x_758;
} else {
 lean_dec_ref(x_758);
 x_803 = lean_box(0);
}
if (lean_is_scalar(x_803)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_803;
}
lean_ctor_set(x_804, 0, x_698);
lean_ctor_set(x_804, 1, x_802);
return x_804;
}
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_738);
lean_dec(x_715);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_805 = lean_ctor_get(x_758, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_806 = x_758;
} else {
 lean_dec_ref(x_758);
 x_806 = lean_box(0);
}
if (lean_is_scalar(x_806)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_806;
 lean_ctor_set_tag(x_807, 0);
}
lean_ctor_set(x_807, 0, x_698);
lean_ctor_set(x_807, 1, x_805);
return x_807;
}
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_715);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_808 = lean_ctor_get(x_742, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_809 = x_742;
} else {
 lean_dec_ref(x_742);
 x_809 = lean_box(0);
}
if (lean_is_scalar(x_809)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_809;
 lean_ctor_set_tag(x_810, 0);
}
lean_ctor_set(x_810, 0, x_698);
lean_ctor_set(x_810, 1, x_808);
return x_810;
}
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_738);
lean_dec(x_715);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_811 = lean_ctor_get(x_739, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_739)) {
 lean_ctor_release(x_739, 0);
 lean_ctor_release(x_739, 1);
 x_812 = x_739;
} else {
 lean_dec_ref(x_739);
 x_812 = lean_box(0);
}
if (lean_is_scalar(x_812)) {
 x_813 = lean_alloc_ctor(0, 2, 0);
} else {
 x_813 = x_812;
 lean_ctor_set_tag(x_813, 0);
}
lean_ctor_set(x_813, 0, x_698);
lean_ctor_set(x_813, 1, x_811);
return x_813;
}
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_715);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_814 = lean_ctor_get(x_728, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_815 = x_728;
} else {
 lean_dec_ref(x_728);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_816 = lean_alloc_ctor(1, 1, 0);
} else {
 x_816 = x_677;
}
lean_ctor_set(x_816, 0, x_724);
if (lean_is_scalar(x_815)) {
 x_817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_817 = x_815;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_814);
return x_817;
}
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_724);
lean_dec(x_715);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_818 = lean_ctor_get(x_728, 1);
lean_inc(x_818);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_819 = x_728;
} else {
 lean_dec_ref(x_728);
 x_819 = lean_box(0);
}
if (lean_is_scalar(x_819)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_819;
 lean_ctor_set_tag(x_820, 0);
}
lean_ctor_set(x_820, 0, x_698);
lean_ctor_set(x_820, 1, x_818);
return x_820;
}
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_724);
lean_dec(x_715);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_821 = lean_ctor_get(x_725, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_822 = x_725;
} else {
 lean_dec_ref(x_725);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_822)) {
 x_823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_823 = x_822;
 lean_ctor_set_tag(x_823, 0);
}
lean_ctor_set(x_823, 0, x_698);
lean_ctor_set(x_823, 1, x_821);
return x_823;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
lean_dec(x_707);
lean_dec(x_704);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_824 = lean_ctor_get(x_709, 1);
lean_inc(x_824);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_825 = x_709;
} else {
 lean_dec_ref(x_709);
 x_825 = lean_box(0);
}
if (lean_is_scalar(x_825)) {
 x_826 = lean_alloc_ctor(0, 2, 0);
} else {
 x_826 = x_825;
 lean_ctor_set_tag(x_826, 0);
}
lean_ctor_set(x_826, 0, x_698);
lean_ctor_set(x_826, 1, x_824);
return x_826;
}
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; 
lean_dec(x_704);
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_827 = lean_ctor_get(x_706, 1);
lean_inc(x_827);
if (lean_is_exclusive(x_706)) {
 lean_ctor_release(x_706, 0);
 lean_ctor_release(x_706, 1);
 x_828 = x_706;
} else {
 lean_dec_ref(x_706);
 x_828 = lean_box(0);
}
if (lean_is_scalar(x_828)) {
 x_829 = lean_alloc_ctor(0, 2, 0);
} else {
 x_829 = x_828;
 lean_ctor_set_tag(x_829, 0);
}
lean_ctor_set(x_829, 0, x_698);
lean_ctor_set(x_829, 1, x_827);
return x_829;
}
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_702);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_830 = lean_ctor_get(x_703, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_831 = x_703;
} else {
 lean_dec_ref(x_703);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(0, 2, 0);
} else {
 x_832 = x_831;
 lean_ctor_set_tag(x_832, 0);
}
lean_ctor_set(x_832, 0, x_698);
lean_ctor_set(x_832, 1, x_830);
return x_832;
}
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; 
lean_dec(x_700);
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_833 = lean_ctor_get(x_699, 1);
lean_inc(x_833);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_834 = x_699;
} else {
 lean_dec_ref(x_699);
 x_834 = lean_box(0);
}
if (lean_is_scalar(x_834)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_834;
}
lean_ctor_set(x_835, 0, x_698);
lean_ctor_set(x_835, 1, x_833);
return x_835;
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_836 = lean_ctor_get(x_699, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_837 = x_699;
} else {
 lean_dec_ref(x_699);
 x_837 = lean_box(0);
}
if (lean_is_scalar(x_837)) {
 x_838 = lean_alloc_ctor(0, 2, 0);
} else {
 x_838 = x_837;
 lean_ctor_set_tag(x_838, 0);
}
lean_ctor_set(x_838, 0, x_698);
lean_ctor_set(x_838, 1, x_836);
return x_838;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_839 = lean_ctor_get(x_695, 1);
lean_inc(x_839);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 x_840 = x_695;
} else {
 lean_dec_ref(x_695);
 x_840 = lean_box(0);
}
x_841 = lean_box(0);
if (lean_is_scalar(x_840)) {
 x_842 = lean_alloc_ctor(0, 2, 0);
} else {
 x_842 = x_840;
 lean_ctor_set_tag(x_842, 0);
}
lean_ctor_set(x_842, 0, x_841);
lean_ctor_set(x_842, 1, x_839);
return x_842;
}
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
lean_dec(x_15);
lean_dec(x_9);
x_843 = lean_ctor_get(x_681, 1);
lean_inc(x_843);
lean_dec(x_681);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_844 = l_Lean_Meta_isMonad_x3f(x_668, x_3, x_4, x_5, x_6, x_843);
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_848 = lean_box(0);
if (lean_is_scalar(x_847)) {
 x_849 = lean_alloc_ctor(0, 2, 0);
} else {
 x_849 = x_847;
}
lean_ctor_set(x_849, 0, x_848);
lean_ctor_set(x_849, 1, x_846);
return x_849;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_850 = lean_ctor_get(x_844, 1);
lean_inc(x_850);
lean_dec(x_844);
x_851 = lean_ctor_get(x_845, 0);
lean_inc(x_851);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 x_852 = x_845;
} else {
 lean_dec_ref(x_845);
 x_852 = lean_box(0);
}
if (lean_is_scalar(x_852)) {
 x_853 = lean_alloc_ctor(1, 1, 0);
} else {
 x_853 = x_852;
}
lean_ctor_set(x_853, 0, x_679);
if (lean_is_scalar(x_677)) {
 x_854 = lean_alloc_ctor(1, 1, 0);
} else {
 x_854 = x_677;
}
lean_ctor_set(x_854, 0, x_680);
x_855 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_855, 0, x_669);
x_856 = lean_box(0);
x_857 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_857, 0, x_851);
x_858 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_858, 0, x_1);
x_859 = l_Lean_Meta_coerceMonadLift_x3f___closed__12;
x_860 = lean_array_push(x_859, x_853);
x_861 = lean_array_push(x_860, x_854);
x_862 = lean_array_push(x_861, x_855);
x_863 = lean_array_push(x_862, x_856);
x_864 = lean_array_push(x_863, x_857);
x_865 = lean_array_push(x_864, x_858);
x_866 = l_Lean_Meta_isCoeDecl___closed__25;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_867 = l_Lean_Meta_mkAppOptM(x_866, x_865, x_3, x_4, x_5, x_6, x_850);
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec(x_867);
x_870 = l_Lean_Meta_expandCoe(x_868, x_3, x_4, x_5, x_6, x_869);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_873 = x_870;
} else {
 lean_dec_ref(x_870);
 x_873 = lean_box(0);
}
x_874 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_874, 0, x_871);
if (lean_is_scalar(x_873)) {
 x_875 = lean_alloc_ctor(0, 2, 0);
} else {
 x_875 = x_873;
}
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_872);
return x_875;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_870, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_877 = x_870;
} else {
 lean_dec_ref(x_870);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_878 = x_877;
 lean_ctor_set_tag(x_878, 0);
}
lean_ctor_set(x_878, 0, x_856);
lean_ctor_set(x_878, 1, x_876);
return x_878;
}
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_879 = lean_ctor_get(x_867, 1);
lean_inc(x_879);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_880 = x_867;
} else {
 lean_dec_ref(x_867);
 x_880 = lean_box(0);
}
if (lean_is_scalar(x_880)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_880;
 lean_ctor_set_tag(x_881, 0);
}
lean_ctor_set(x_881, 0, x_856);
lean_ctor_set(x_881, 1, x_879);
return x_881;
}
}
}
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
lean_dec(x_680);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_882 = lean_ctor_get(x_681, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_681, 1);
lean_inc(x_883);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_884 = x_681;
} else {
 lean_dec_ref(x_681);
 x_884 = lean_box(0);
}
if (lean_is_scalar(x_884)) {
 x_885 = lean_alloc_ctor(1, 2, 0);
} else {
 x_885 = x_884;
}
lean_ctor_set(x_885, 0, x_882);
lean_ctor_set(x_885, 1, x_883);
return x_885;
}
}
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_886 = lean_ctor_get(x_670, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_670, 1);
lean_inc(x_887);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 x_888 = x_670;
} else {
 lean_dec_ref(x_670);
 x_888 = lean_box(0);
}
if (lean_is_scalar(x_888)) {
 x_889 = lean_alloc_ctor(1, 2, 0);
} else {
 x_889 = x_888;
}
lean_ctor_set(x_889, 0, x_886);
lean_ctor_set(x_889, 1, x_887);
return x_889;
}
}
}
}
else
{
uint8_t x_890; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_890 = !lean_is_exclusive(x_17);
if (x_890 == 0)
{
return x_17;
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_17, 0);
x_892 = lean_ctor_get(x_17, 1);
lean_inc(x_892);
lean_inc(x_891);
lean_dec(x_17);
x_893 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_893, 0, x_891);
lean_ctor_set(x_893, 1, x_892);
return x_893;
}
}
}
else
{
uint8_t x_894; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_894 = !lean_is_exclusive(x_11);
if (x_894 == 0)
{
return x_11;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_895 = lean_ctor_get(x_11, 0);
x_896 = lean_ctor_get(x_11, 1);
lean_inc(x_896);
lean_inc(x_895);
lean_dec(x_11);
x_897 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_897, 0, x_895);
lean_ctor_set(x_897, 1, x_896);
return x_897;
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
l_Lean_Meta_isCoeDecl___closed__1 = _init_l_Lean_Meta_isCoeDecl___closed__1();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__1);
l_Lean_Meta_isCoeDecl___closed__2 = _init_l_Lean_Meta_isCoeDecl___closed__2();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__2);
l_Lean_Meta_isCoeDecl___closed__3 = _init_l_Lean_Meta_isCoeDecl___closed__3();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__3);
l_Lean_Meta_isCoeDecl___closed__4 = _init_l_Lean_Meta_isCoeDecl___closed__4();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__4);
l_Lean_Meta_isCoeDecl___closed__5 = _init_l_Lean_Meta_isCoeDecl___closed__5();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__5);
l_Lean_Meta_isCoeDecl___closed__6 = _init_l_Lean_Meta_isCoeDecl___closed__6();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__6);
l_Lean_Meta_isCoeDecl___closed__7 = _init_l_Lean_Meta_isCoeDecl___closed__7();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__7);
l_Lean_Meta_isCoeDecl___closed__8 = _init_l_Lean_Meta_isCoeDecl___closed__8();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__8);
l_Lean_Meta_isCoeDecl___closed__9 = _init_l_Lean_Meta_isCoeDecl___closed__9();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__9);
l_Lean_Meta_isCoeDecl___closed__10 = _init_l_Lean_Meta_isCoeDecl___closed__10();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__10);
l_Lean_Meta_isCoeDecl___closed__11 = _init_l_Lean_Meta_isCoeDecl___closed__11();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__11);
l_Lean_Meta_isCoeDecl___closed__12 = _init_l_Lean_Meta_isCoeDecl___closed__12();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__12);
l_Lean_Meta_isCoeDecl___closed__13 = _init_l_Lean_Meta_isCoeDecl___closed__13();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__13);
l_Lean_Meta_isCoeDecl___closed__14 = _init_l_Lean_Meta_isCoeDecl___closed__14();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__14);
l_Lean_Meta_isCoeDecl___closed__15 = _init_l_Lean_Meta_isCoeDecl___closed__15();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__15);
l_Lean_Meta_isCoeDecl___closed__16 = _init_l_Lean_Meta_isCoeDecl___closed__16();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__16);
l_Lean_Meta_isCoeDecl___closed__17 = _init_l_Lean_Meta_isCoeDecl___closed__17();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__17);
l_Lean_Meta_isCoeDecl___closed__18 = _init_l_Lean_Meta_isCoeDecl___closed__18();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__18);
l_Lean_Meta_isCoeDecl___closed__19 = _init_l_Lean_Meta_isCoeDecl___closed__19();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__19);
l_Lean_Meta_isCoeDecl___closed__20 = _init_l_Lean_Meta_isCoeDecl___closed__20();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__20);
l_Lean_Meta_isCoeDecl___closed__21 = _init_l_Lean_Meta_isCoeDecl___closed__21();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__21);
l_Lean_Meta_isCoeDecl___closed__22 = _init_l_Lean_Meta_isCoeDecl___closed__22();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__22);
l_Lean_Meta_isCoeDecl___closed__23 = _init_l_Lean_Meta_isCoeDecl___closed__23();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__23);
l_Lean_Meta_isCoeDecl___closed__24 = _init_l_Lean_Meta_isCoeDecl___closed__24();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__24);
l_Lean_Meta_isCoeDecl___closed__25 = _init_l_Lean_Meta_isCoeDecl___closed__25();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__25);
l_Lean_Meta_expandCoe___lambda__1___closed__1 = _init_l_Lean_Meta_expandCoe___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_expandCoe___lambda__1___closed__1);
l_Lean_Meta_expandCoe___lambda__2___closed__1 = _init_l_Lean_Meta_expandCoe___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_expandCoe___lambda__2___closed__1);
l_Lean_Meta_expandCoe___closed__1 = _init_l_Lean_Meta_expandCoe___closed__1();
lean_mark_persistent(l_Lean_Meta_expandCoe___closed__1);
l_Lean_Meta_expandCoe___closed__2 = _init_l_Lean_Meta_expandCoe___closed__2();
lean_mark_persistent(l_Lean_Meta_expandCoe___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338____closed__7);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_338_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_maxCoeSize = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_maxCoeSize);
lean_dec_ref(res);
}l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377____closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Coe___hyg_377_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_autoLift = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_autoLift);
lean_dec_ref(res);
}l_Lean_Meta_trySynthInstanceForCoe___closed__1 = _init_l_Lean_Meta_trySynthInstanceForCoe___closed__1();
lean_mark_persistent(l_Lean_Meta_trySynthInstanceForCoe___closed__1);
l_Lean_Meta_coerceSimple_x3f___closed__1 = _init_l_Lean_Meta_coerceSimple_x3f___closed__1();
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
l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__1);
l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__2);
l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__3 = _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__3);
l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__4 = _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__4);
l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__5 = _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__5);
l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__6 = _init_l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___lambda__2___closed__6);
l_Lean_Meta_coerceToFunction_x3f___closed__1 = _init_l_Lean_Meta_coerceToFunction_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_coerceToFunction_x3f___closed__1);
l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__1);
l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__2);
l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__3 = _init_l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__3);
l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__4 = _init_l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_coerceToSort_x3f___lambda__1___closed__4);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
