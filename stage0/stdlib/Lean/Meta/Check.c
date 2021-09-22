// Lean compiler output
// Module: Lean.Meta.Check
// Imports: Init Lean.Meta.InferType Lean.Meta.LevelDefEq
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2(lean_object*);
static lean_object* l_Lean_Meta_check___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13;
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__4;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___closed__1;
static lean_object* l_Lean_Meta_check___closed__4;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
lean_object* l_Lean_Meta_throwFunctionExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_check___closed__2;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage(lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2;
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__1;
static lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__4;
static lean_object* l_Lean_Meta_isTypeCorrect___closed__1;
static lean_object* l_Lean_Meta_isTypeCorrect___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10;
static lean_object* l_Lean_Meta_checkApp___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__3;
static lean_object* l_Lean_Meta_check___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__1;
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__5;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2;
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__6;
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__6;
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_1920_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4;
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLevel(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Check");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.throwLetTypeMismatchMessage");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2;
x_2 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3;
x_3 = lean_unsigned_to_nat(25u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid let declaration, term");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nhas type");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nbut is expected to have type");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_local_ctx_find(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
x_10 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_5(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
x_14 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
x_15 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5;
x_16 = lean_panic_fn(x_14, x_15);
x_17 = lean_apply_5(x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_19);
x_20 = lean_infer_type(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_indentExpr(x_19);
x_24 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_indentExpr(x_21);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_18);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg(x_35, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwLetTypeMismatchMessage___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_List_lengthTRAux___rarg(x_2, x_12);
x_14 = l_Lean_ConstantInfo_levelParams(x_10);
lean_dec(x_10);
x_15 = l_List_lengthTRAux___rarg(x_14, x_12);
lean_dec(x_14);
x_16 = lean_nat_dec_eq(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_8);
x_17 = l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_List_lengthTRAux___rarg(x_2, x_21);
x_23 = l_Lean_ConstantInfo_levelParams(x_19);
lean_dec(x_19);
x_24 = l_List_lengthTRAux___rarg(x_23, x_21);
lean_dec(x_23);
x_25 = lean_nat_dec_eq(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = l_Lean_Meta_whnfD(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 7)
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_11, sizeof(void*)*3);
lean_dec(x_11);
x_16 = (uint8_t)((x_15 << 24) >> 61);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_11, sizeof(void*)*3);
lean_dec(x_11);
x_22 = (uint8_t)((x_21 << 24) >> 61);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = l_Lean_Meta_throwFunctionExpected___rarg(x_1, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_nat_dec_le(x_14, x_7);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_6, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_6, x_18);
lean_dec(x_6);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_1, x_7);
x_22 = l_Lean_Expr_fvarId_x21(x_21);
lean_dec(x_21);
lean_inc(x_9);
x_23 = l_Lean_Meta_getLocalDecl(x_22, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_binderInfo(x_24);
lean_dec(x_24);
x_27 = l_Lean_BinderInfo_isExplicit(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_5, 2);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
lean_inc(x_4);
{
lean_object* _tmp_5 = x_19;
lean_object* _tmp_6 = x_29;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_12 = x_25;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_array_get(x_20, x_2, x_7);
x_32 = lean_array_get(x_20, x_3, x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_33 = l_Lean_Meta_isExprDefEq(x_31, x_32, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__2;
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_ctor_get(x_5, 2);
x_44 = lean_nat_add(x_7, x_43);
lean_dec(x_7);
lean_inc(x_4);
{
lean_object* _tmp_5 = x_19;
lean_object* _tmp_6 = x_44;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_12 = x_42;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_23, 0);
x_52 = lean_ctor_get(x_23, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_23);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_13);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_8);
lean_ctor_set(x_55, 1, x_13);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1(x_1, x_2, x_3, x_13, x_12, x_9, x_10, x_13, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__2;
x_19 = lean_box(0);
x_20 = lean_apply_6(x_18, x_19, x_4, x_5, x_6, x_7, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_nat_dec_le(x_10, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_2);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_16, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_19, x_20, x_5, x_6, x_7, x_8, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_array_set(x_17, x_3, x_24);
x_27 = lean_array_set(x_16, x_3, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_nat_add(x_3, x_29);
lean_dec(x_3);
x_2 = x_15;
x_3 = x_30;
x_4 = x_28;
x_9 = x_23;
goto _start;
}
else
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1;
lean_inc(x_1);
x_15 = lean_mk_array(x_1, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_1, x_16);
lean_dec(x_1);
lean_inc(x_2);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_15, x_17);
lean_inc(x_3);
x_19 = lean_mk_array(x_3, x_14);
x_20 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
lean_inc(x_4);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_19, x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_22 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff(x_7, x_18, x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_array_get_size(x_18);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_18);
x_30 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1(x_28, x_26, x_27, x_29, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_mkAppN(x_5, x_34);
x_36 = l_Lean_mkAppN(x_6, x_33);
x_37 = l_Lean_Expr_setAppPPExplicit(x_35);
x_38 = l_Lean_Expr_setAppPPExplicit(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_30);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lean_mkAppN(x_5, x_43);
x_45 = l_Lean_mkAppN(x_6, x_42);
x_46 = l_Lean_Expr_setAppPPExplicit(x_44);
x_47 = l_Lean_Expr_setAppPPExplicit(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_22, 0);
lean_dec(x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_4);
lean_ctor_set(x_22, 0, x_52);
return x_22;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_dec(x_22);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isApp(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isApp(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux(x_1, x_14);
x_16 = l_Lean_Expr_getAppNumArgsAux(x_2, x_14);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Expr_getAppFn(x_1);
x_21 = l_Lean_Expr_getAppFn(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_21);
lean_inc(x_20);
x_22 = l_Lean_Meta_isExprDefEq(x_20, x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_20);
x_32 = lean_infer_type(x_20, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_15);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_15);
lean_inc(x_2);
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___boxed), 13, 6);
lean_closure_set(x_36, 0, x_15);
lean_closure_set(x_36, 1, x_1);
lean_closure_set(x_36, 2, x_16);
lean_closure_set(x_36, 3, x_2);
lean_closure_set(x_36, 4, x_20);
lean_closure_set(x_36, 5, x_21);
x_37 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(x_33, x_35, x_36, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_37, 0);
lean_dec(x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set_tag(x_37, 0);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_dec(x_37);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_32);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_32, 0);
lean_dec(x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_50);
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 1);
lean_inc(x_51);
lean_dec(x_32);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_22);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_22, 0);
lean_dec(x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_56);
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
lean_dec(x_22);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pp");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_addPPExplicitToExposeDiff___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("all");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_addPPExplicitToExposeDiff___closed__2;
x_2 = l_Lean_Meta_addPPExplicitToExposeDiff___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_addPPExplicitToExposeDiff___closed__2;
x_2 = l_Lean_Meta_addPPExplicitToExposeDiff___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = l_Lean_Meta_addPPExplicitToExposeDiff___closed__4;
x_10 = 0;
x_11 = l_Lean_KVMap_getBool(x_8, x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_addPPExplicitToExposeDiff___closed__6;
x_13 = l_Lean_KVMap_getBool(x_8, x_12, x_10);
lean_dec(x_8);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("has type");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_38; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_38 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_41 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_44 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Meta_addPPExplicitToExposeDiff(x_39, x_42, x_3, x_4, x_5, x_6, x_46);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_55 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__4;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_52);
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
x_62 = l_Lean_indentD(x_61);
x_63 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_48);
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_57);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_53);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_55);
x_73 = l_Lean_indentD(x_72);
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_55);
lean_ctor_set(x_49, 0, x_75);
return x_49;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_76 = lean_ctor_get(x_49, 0);
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_49);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_47);
x_81 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__4;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_78);
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
x_88 = l_Lean_indentD(x_87);
x_89 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2;
x_90 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11;
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_48);
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_81);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_83);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_79);
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_81);
x_99 = l_Lean_indentD(x_98);
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_81);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_77);
return x_102;
}
}
else
{
lean_object* x_103; 
lean_dec(x_39);
x_103 = lean_ctor_get(x_41, 1);
lean_inc(x_103);
lean_dec(x_41);
x_8 = x_103;
goto block_37;
}
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_38, 1);
lean_inc(x_104);
lean_dec(x_38);
x_8 = x_104;
goto block_37;
}
block_37:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_indentExpr(x_12);
x_15 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_indentExpr(x_13);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_indentExpr(x_25);
x_28 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_26);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("application type mismatch");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nargument");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_11, x_2, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_indentExpr(x_3);
x_17 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_indentExpr(x_1);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__6;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
x_26 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg(x_27, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_2);
x_14 = l_Lean_mkApp(x_1, x_2);
x_15 = lean_unbox(x_13);
lean_dec(x_13);
x_16 = l_Lean_BinderInfo_isExplicit(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Expr_setAppPPExplicit(x_14);
x_18 = lean_box(0);
x_19 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(x_2, x_12, x_17, x_18, x_4, x_5, x_6, x_7, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(x_2, x_12, x_14, x_20, x_4, x_5, x_6, x_7, x_11);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwAppTypeMismatch___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_checkApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = lean_whnf(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Meta_isExprDefEq(x_14, x_16, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Meta_checkApp___closed__1;
x_23 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_1, x_2, x_22, x_3, x_4, x_5, x_6, x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = l_Lean_mkApp(x_1, x_2);
x_40 = l_Lean_Meta_throwFunctionExpected___rarg(x_39, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_8);
if (x_45 == 0)
{
return x_8;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 == x_3;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_18 = l_Lean_Meta_getFVarLocalDecl(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 3);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_21, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_21, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_12 = x_25;
x_13 = x_26;
goto block_17;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_19, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_19, 4);
lean_inc(x_37);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_38 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_36, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_40 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_36, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_37);
x_42 = lean_infer_type(x_37, x_5, x_6, x_7, x_8, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Meta_isExprDefEq(x_36, x_43, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Expr_fvarId_x21(x_11);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg(x_49, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_52 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_37, x_5, x_6, x_7, x_8, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_12 = x_53;
x_13 = x_54;
goto block_17;
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_50);
if (x_59 == 0)
{
return x_50;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_50, 0);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_50);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_dec(x_45);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_64 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_37, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_12 = x_65;
x_13 = x_66;
goto block_17;
}
else
{
uint8_t x_67; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_45);
if (x_71 == 0)
{
return x_45;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_45, 0);
x_73 = lean_ctor_get(x_45, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_45);
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
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_42);
if (x_75 == 0)
{
return x_42;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_42, 0);
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_42);
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
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_40);
if (x_79 == 0)
{
return x_40;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_40, 0);
x_81 = lean_ctor_get(x_40, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_40);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
else
{
uint8_t x_87; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_18);
if (x_87 == 0)
{
return x_18;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_18, 0);
x_89 = lean_ctor_get(x_18, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_18);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = x_2 + x_14;
x_2 = x_15;
x_4 = x_12;
x_9 = x_13;
goto _start;
}
}
else
{
lean_object* x_91; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_4);
lean_ctor_set(x_91, 1, x_9);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_11 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1(x_1, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_3, x_4, x_5, x_6, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___closed__1;
x_8 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_12 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_14 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_11, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_checkApp(x_10, x_11, x_2, x_3, x_4, x_5, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
case 6:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1), 7, 0);
x_26 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_25, x_2, x_3, x_4, x_5, x_6);
return x_26;
}
case 7:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1), 7, 0);
x_28 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_1, x_27, x_2, x_3, x_4, x_5, x_6);
return x_28;
}
case 8:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1), 7, 0);
x_30 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_29, x_2, x_3, x_4, x_5, x_6);
return x_30;
}
case 10:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_1 = x_31;
goto _start;
}
case 11:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
x_1 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 == x_3;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_12 = l_Lean_Meta_getFVarLocalDecl(x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_LocalDecl_type(x_13);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_16 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_15, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_15, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = x_2 + x_21;
x_2 = x_22;
x_4 = x_19;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_3, x_4, x_5, x_6, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_8, x_8);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_3, x_4, x_5, x_6, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_28 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1(x_1, x_26, x_27, x_28, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_2, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_3, x_4, x_5, x_6, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___closed__1;
x_8 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_check___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_check___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_check___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_check___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("check");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_check___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_check___closed__2;
x_2 = l_Lean_Meta_check___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_413 = lean_st_ref_get(x_5, x_6);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_414, 3);
lean_inc(x_415);
lean_dec(x_414);
x_416 = lean_ctor_get_uint8(x_415, sizeof(void*)*1);
lean_dec(x_415);
if (x_416 == 0)
{
lean_object* x_417; uint8_t x_418; 
x_417 = lean_ctor_get(x_413, 1);
lean_inc(x_417);
lean_dec(x_413);
x_418 = 0;
x_7 = x_418;
x_8 = x_417;
goto block_412;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_419 = lean_ctor_get(x_413, 1);
lean_inc(x_419);
lean_dec(x_413);
x_420 = l_Lean_Meta_check___closed__4;
x_421 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_420, x_2, x_3, x_4, x_5, x_419);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_unbox(x_422);
lean_dec(x_422);
x_7 = x_424;
x_8 = x_423;
goto block_412;
}
block_412:
{
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_5, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 3);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = 0;
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_21);
x_22 = lean_st_ref_set(x_5, x_15, x_17);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
x_28 = 0;
lean_ctor_set_uint8(x_23, 5, x_28);
lean_inc(x_5);
x_29 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_5, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_take(x_5, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 3);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_13);
x_41 = lean_st_ref_set(x_5, x_35, x_37);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_30);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
lean_dec(x_36);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_13);
lean_ctor_set(x_35, 3, x_47);
x_48 = lean_st_ref_set(x_5, x_35, x_37);
lean_dec(x_5);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_30);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
x_54 = lean_ctor_get(x_35, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_55 = lean_ctor_get(x_36, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_56 = x_36;
} else {
 lean_dec_ref(x_36);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 1);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_13);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_54);
lean_ctor_set(x_58, 3, x_57);
x_59 = lean_st_ref_set(x_5, x_58, x_37);
lean_dec(x_5);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_30);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_63 = lean_ctor_get(x_29, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_29, 1);
lean_inc(x_64);
lean_dec(x_29);
x_65 = lean_st_ref_get(x_5, x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_take(x_5, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_68, 3);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_13);
x_74 = lean_st_ref_set(x_5, x_68, x_70);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_63);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_63);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_13);
lean_ctor_set(x_68, 3, x_80);
x_81 = lean_st_ref_set(x_5, x_68, x_70);
lean_dec(x_5);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_63);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_85 = lean_ctor_get(x_68, 0);
x_86 = lean_ctor_get(x_68, 1);
x_87 = lean_ctor_get(x_68, 2);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_68);
x_88 = lean_ctor_get(x_69, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_89 = x_69;
} else {
 lean_dec_ref(x_69);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 1, 1);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_13);
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_86);
lean_ctor_set(x_91, 2, x_87);
lean_ctor_set(x_91, 3, x_90);
x_92 = lean_st_ref_set(x_5, x_91, x_70);
lean_dec(x_5);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_63);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_96 = lean_ctor_get_uint8(x_23, 0);
x_97 = lean_ctor_get_uint8(x_23, 1);
x_98 = lean_ctor_get_uint8(x_23, 2);
x_99 = lean_ctor_get_uint8(x_23, 3);
x_100 = lean_ctor_get_uint8(x_23, 4);
x_101 = lean_ctor_get_uint8(x_23, 6);
x_102 = lean_ctor_get_uint8(x_23, 7);
x_103 = lean_ctor_get_uint8(x_23, 8);
x_104 = lean_ctor_get_uint8(x_23, 9);
x_105 = lean_ctor_get_uint8(x_23, 10);
x_106 = lean_ctor_get_uint8(x_23, 11);
x_107 = lean_ctor_get_uint8(x_23, 12);
lean_dec(x_23);
x_108 = 0;
x_109 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_109, 0, x_96);
lean_ctor_set_uint8(x_109, 1, x_97);
lean_ctor_set_uint8(x_109, 2, x_98);
lean_ctor_set_uint8(x_109, 3, x_99);
lean_ctor_set_uint8(x_109, 4, x_100);
lean_ctor_set_uint8(x_109, 5, x_108);
lean_ctor_set_uint8(x_109, 6, x_101);
lean_ctor_set_uint8(x_109, 7, x_102);
lean_ctor_set_uint8(x_109, 8, x_103);
lean_ctor_set_uint8(x_109, 9, x_104);
lean_ctor_set_uint8(x_109, 10, x_105);
lean_ctor_set_uint8(x_109, 11, x_106);
lean_ctor_set_uint8(x_109, 12, x_107);
lean_ctor_set(x_2, 0, x_109);
lean_inc(x_5);
x_110 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_st_ref_get(x_5, x_112);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_st_ref_take(x_5, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 2);
lean_inc(x_121);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 x_122 = x_116;
} else {
 lean_dec_ref(x_116);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_117, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 1, 1);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 4, 0);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_120);
lean_ctor_set(x_126, 2, x_121);
lean_ctor_set(x_126, 3, x_125);
x_127 = lean_st_ref_set(x_5, x_126, x_118);
lean_dec(x_5);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_111);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_131 = lean_ctor_get(x_110, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_110, 1);
lean_inc(x_132);
lean_dec(x_110);
x_133 = lean_st_ref_get(x_5, x_132);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_take(x_5, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 2);
lean_inc(x_141);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 x_142 = x_136;
} else {
 lean_dec_ref(x_136);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_144 = x_137;
} else {
 lean_dec_ref(x_137);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 1, 1);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(0, 4, 0);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_141);
lean_ctor_set(x_146, 3, x_145);
x_147 = lean_st_ref_set(x_5, x_146, x_138);
lean_dec(x_5);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_131);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_151 = lean_ctor_get(x_2, 1);
x_152 = lean_ctor_get(x_2, 2);
x_153 = lean_ctor_get(x_2, 3);
x_154 = lean_ctor_get(x_2, 4);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_2);
x_155 = lean_ctor_get_uint8(x_23, 0);
x_156 = lean_ctor_get_uint8(x_23, 1);
x_157 = lean_ctor_get_uint8(x_23, 2);
x_158 = lean_ctor_get_uint8(x_23, 3);
x_159 = lean_ctor_get_uint8(x_23, 4);
x_160 = lean_ctor_get_uint8(x_23, 6);
x_161 = lean_ctor_get_uint8(x_23, 7);
x_162 = lean_ctor_get_uint8(x_23, 8);
x_163 = lean_ctor_get_uint8(x_23, 9);
x_164 = lean_ctor_get_uint8(x_23, 10);
x_165 = lean_ctor_get_uint8(x_23, 11);
x_166 = lean_ctor_get_uint8(x_23, 12);
if (lean_is_exclusive(x_23)) {
 x_167 = x_23;
} else {
 lean_dec_ref(x_23);
 x_167 = lean_box(0);
}
x_168 = 0;
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 0, 13);
} else {
 x_169 = x_167;
}
lean_ctor_set_uint8(x_169, 0, x_155);
lean_ctor_set_uint8(x_169, 1, x_156);
lean_ctor_set_uint8(x_169, 2, x_157);
lean_ctor_set_uint8(x_169, 3, x_158);
lean_ctor_set_uint8(x_169, 4, x_159);
lean_ctor_set_uint8(x_169, 5, x_168);
lean_ctor_set_uint8(x_169, 6, x_160);
lean_ctor_set_uint8(x_169, 7, x_161);
lean_ctor_set_uint8(x_169, 8, x_162);
lean_ctor_set_uint8(x_169, 9, x_163);
lean_ctor_set_uint8(x_169, 10, x_164);
lean_ctor_set_uint8(x_169, 11, x_165);
lean_ctor_set_uint8(x_169, 12, x_166);
x_170 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_151);
lean_ctor_set(x_170, 2, x_152);
lean_ctor_set(x_170, 3, x_153);
lean_ctor_set(x_170, 4, x_154);
lean_inc(x_5);
x_171 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_170, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_st_ref_get(x_5, x_173);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_st_ref_take(x_5, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_177, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 2);
lean_inc(x_182);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_183 = x_177;
} else {
 lean_dec_ref(x_177);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_185 = x_178;
} else {
 lean_dec_ref(x_178);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 1, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_183)) {
 x_187 = lean_alloc_ctor(0, 4, 0);
} else {
 x_187 = x_183;
}
lean_ctor_set(x_187, 0, x_180);
lean_ctor_set(x_187, 1, x_181);
lean_ctor_set(x_187, 2, x_182);
lean_ctor_set(x_187, 3, x_186);
x_188 = lean_st_ref_set(x_5, x_187, x_179);
lean_dec(x_5);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_172);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_192 = lean_ctor_get(x_171, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_171, 1);
lean_inc(x_193);
lean_dec(x_171);
x_194 = lean_st_ref_get(x_5, x_193);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_st_ref_take(x_5, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 3);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_197, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 2);
lean_inc(x_202);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 x_203 = x_197;
} else {
 lean_dec_ref(x_197);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_198, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_205 = x_198;
} else {
 lean_dec_ref(x_198);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 1, 1);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set_uint8(x_206, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_203)) {
 x_207 = lean_alloc_ctor(0, 4, 0);
} else {
 x_207 = x_203;
}
lean_ctor_set(x_207, 0, x_200);
lean_ctor_set(x_207, 1, x_201);
lean_ctor_set(x_207, 2, x_202);
lean_ctor_set(x_207, 3, x_206);
x_208 = lean_st_ref_set(x_5, x_207, x_199);
lean_dec(x_5);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_210 = x_208;
} else {
 lean_dec_ref(x_208);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_192);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
else
{
lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_212 = lean_ctor_get(x_16, 0);
lean_inc(x_212);
lean_dec(x_16);
x_213 = 0;
x_214 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_213);
lean_ctor_set(x_15, 3, x_214);
x_215 = lean_st_ref_set(x_5, x_15, x_17);
x_216 = lean_ctor_get(x_2, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_2, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_2, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_2, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_2, 4);
lean_inc(x_221);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_222 = x_2;
} else {
 lean_dec_ref(x_2);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get_uint8(x_216, 0);
x_224 = lean_ctor_get_uint8(x_216, 1);
x_225 = lean_ctor_get_uint8(x_216, 2);
x_226 = lean_ctor_get_uint8(x_216, 3);
x_227 = lean_ctor_get_uint8(x_216, 4);
x_228 = lean_ctor_get_uint8(x_216, 6);
x_229 = lean_ctor_get_uint8(x_216, 7);
x_230 = lean_ctor_get_uint8(x_216, 8);
x_231 = lean_ctor_get_uint8(x_216, 9);
x_232 = lean_ctor_get_uint8(x_216, 10);
x_233 = lean_ctor_get_uint8(x_216, 11);
x_234 = lean_ctor_get_uint8(x_216, 12);
if (lean_is_exclusive(x_216)) {
 x_235 = x_216;
} else {
 lean_dec_ref(x_216);
 x_235 = lean_box(0);
}
x_236 = 0;
if (lean_is_scalar(x_235)) {
 x_237 = lean_alloc_ctor(0, 0, 13);
} else {
 x_237 = x_235;
}
lean_ctor_set_uint8(x_237, 0, x_223);
lean_ctor_set_uint8(x_237, 1, x_224);
lean_ctor_set_uint8(x_237, 2, x_225);
lean_ctor_set_uint8(x_237, 3, x_226);
lean_ctor_set_uint8(x_237, 4, x_227);
lean_ctor_set_uint8(x_237, 5, x_236);
lean_ctor_set_uint8(x_237, 6, x_228);
lean_ctor_set_uint8(x_237, 7, x_229);
lean_ctor_set_uint8(x_237, 8, x_230);
lean_ctor_set_uint8(x_237, 9, x_231);
lean_ctor_set_uint8(x_237, 10, x_232);
lean_ctor_set_uint8(x_237, 11, x_233);
lean_ctor_set_uint8(x_237, 12, x_234);
if (lean_is_scalar(x_222)) {
 x_238 = lean_alloc_ctor(0, 5, 0);
} else {
 x_238 = x_222;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_218);
lean_ctor_set(x_238, 2, x_219);
lean_ctor_set(x_238, 3, x_220);
lean_ctor_set(x_238, 4, x_221);
lean_inc(x_5);
x_239 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_238, x_3, x_4, x_5, x_217);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_st_ref_get(x_5, x_241);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_st_ref_take(x_5, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_245, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_245, 2);
lean_inc(x_250);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 lean_ctor_release(x_245, 2);
 lean_ctor_release(x_245, 3);
 x_251 = x_245;
} else {
 lean_dec_ref(x_245);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_246, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_253 = x_246;
} else {
 lean_dec_ref(x_246);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(0, 1, 1);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set_uint8(x_254, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_251)) {
 x_255 = lean_alloc_ctor(0, 4, 0);
} else {
 x_255 = x_251;
}
lean_ctor_set(x_255, 0, x_248);
lean_ctor_set(x_255, 1, x_249);
lean_ctor_set(x_255, 2, x_250);
lean_ctor_set(x_255, 3, x_254);
x_256 = lean_st_ref_set(x_5, x_255, x_247);
lean_dec(x_5);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_240);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_260 = lean_ctor_get(x_239, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_239, 1);
lean_inc(x_261);
lean_dec(x_239);
x_262 = lean_st_ref_get(x_5, x_261);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_st_ref_take(x_5, x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_265, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_dec(x_264);
x_268 = lean_ctor_get(x_265, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 2);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_266, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_273 = x_266;
} else {
 lean_dec_ref(x_266);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 1, 1);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_271)) {
 x_275 = lean_alloc_ctor(0, 4, 0);
} else {
 x_275 = x_271;
}
lean_ctor_set(x_275, 0, x_268);
lean_ctor_set(x_275, 1, x_269);
lean_ctor_set(x_275, 2, x_270);
lean_ctor_set(x_275, 3, x_274);
x_276 = lean_st_ref_set(x_5, x_275, x_267);
lean_dec(x_5);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_278 = x_276;
} else {
 lean_dec_ref(x_276);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
 lean_ctor_set_tag(x_279, 1);
}
lean_ctor_set(x_279, 0, x_260);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_297; uint8_t x_298; uint8_t x_299; uint8_t x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_280 = lean_ctor_get(x_15, 0);
x_281 = lean_ctor_get(x_15, 1);
x_282 = lean_ctor_get(x_15, 2);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_15);
x_283 = lean_ctor_get(x_16, 0);
lean_inc(x_283);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_284 = x_16;
} else {
 lean_dec_ref(x_16);
 x_284 = lean_box(0);
}
x_285 = 0;
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(0, 1, 1);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set_uint8(x_286, sizeof(void*)*1, x_285);
x_287 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_287, 0, x_280);
lean_ctor_set(x_287, 1, x_281);
lean_ctor_set(x_287, 2, x_282);
lean_ctor_set(x_287, 3, x_286);
x_288 = lean_st_ref_set(x_5, x_287, x_17);
x_289 = lean_ctor_get(x_2, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = lean_ctor_get(x_2, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_2, 2);
lean_inc(x_292);
x_293 = lean_ctor_get(x_2, 3);
lean_inc(x_293);
x_294 = lean_ctor_get(x_2, 4);
lean_inc(x_294);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_295 = x_2;
} else {
 lean_dec_ref(x_2);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get_uint8(x_289, 0);
x_297 = lean_ctor_get_uint8(x_289, 1);
x_298 = lean_ctor_get_uint8(x_289, 2);
x_299 = lean_ctor_get_uint8(x_289, 3);
x_300 = lean_ctor_get_uint8(x_289, 4);
x_301 = lean_ctor_get_uint8(x_289, 6);
x_302 = lean_ctor_get_uint8(x_289, 7);
x_303 = lean_ctor_get_uint8(x_289, 8);
x_304 = lean_ctor_get_uint8(x_289, 9);
x_305 = lean_ctor_get_uint8(x_289, 10);
x_306 = lean_ctor_get_uint8(x_289, 11);
x_307 = lean_ctor_get_uint8(x_289, 12);
if (lean_is_exclusive(x_289)) {
 x_308 = x_289;
} else {
 lean_dec_ref(x_289);
 x_308 = lean_box(0);
}
x_309 = 0;
if (lean_is_scalar(x_308)) {
 x_310 = lean_alloc_ctor(0, 0, 13);
} else {
 x_310 = x_308;
}
lean_ctor_set_uint8(x_310, 0, x_296);
lean_ctor_set_uint8(x_310, 1, x_297);
lean_ctor_set_uint8(x_310, 2, x_298);
lean_ctor_set_uint8(x_310, 3, x_299);
lean_ctor_set_uint8(x_310, 4, x_300);
lean_ctor_set_uint8(x_310, 5, x_309);
lean_ctor_set_uint8(x_310, 6, x_301);
lean_ctor_set_uint8(x_310, 7, x_302);
lean_ctor_set_uint8(x_310, 8, x_303);
lean_ctor_set_uint8(x_310, 9, x_304);
lean_ctor_set_uint8(x_310, 10, x_305);
lean_ctor_set_uint8(x_310, 11, x_306);
lean_ctor_set_uint8(x_310, 12, x_307);
if (lean_is_scalar(x_295)) {
 x_311 = lean_alloc_ctor(0, 5, 0);
} else {
 x_311 = x_295;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_291);
lean_ctor_set(x_311, 2, x_292);
lean_ctor_set(x_311, 3, x_293);
lean_ctor_set(x_311, 4, x_294);
lean_inc(x_5);
x_312 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_311, x_3, x_4, x_5, x_290);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_st_ref_get(x_5, x_314);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_st_ref_take(x_5, x_316);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_318, 3);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_321 = lean_ctor_get(x_318, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_318, 2);
lean_inc(x_323);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 lean_ctor_release(x_318, 2);
 lean_ctor_release(x_318, 3);
 x_324 = x_318;
} else {
 lean_dec_ref(x_318);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_319, 0);
lean_inc(x_325);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 x_326 = x_319;
} else {
 lean_dec_ref(x_319);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(0, 1, 1);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set_uint8(x_327, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_324)) {
 x_328 = lean_alloc_ctor(0, 4, 0);
} else {
 x_328 = x_324;
}
lean_ctor_set(x_328, 0, x_321);
lean_ctor_set(x_328, 1, x_322);
lean_ctor_set(x_328, 2, x_323);
lean_ctor_set(x_328, 3, x_327);
x_329 = lean_st_ref_set(x_5, x_328, x_320);
lean_dec(x_5);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_331 = x_329;
} else {
 lean_dec_ref(x_329);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_313);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_333 = lean_ctor_get(x_312, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_312, 1);
lean_inc(x_334);
lean_dec(x_312);
x_335 = lean_st_ref_get(x_5, x_334);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
lean_dec(x_335);
x_337 = lean_st_ref_take(x_5, x_336);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_338, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
lean_dec(x_337);
x_341 = lean_ctor_get(x_338, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_338, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_338, 2);
lean_inc(x_343);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_344 = x_338;
} else {
 lean_dec_ref(x_338);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_339, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 x_346 = x_339;
} else {
 lean_dec_ref(x_339);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(0, 1, 1);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_344)) {
 x_348 = lean_alloc_ctor(0, 4, 0);
} else {
 x_348 = x_344;
}
lean_ctor_set(x_348, 0, x_341);
lean_ctor_set(x_348, 1, x_342);
lean_ctor_set(x_348, 2, x_343);
lean_ctor_set(x_348, 3, x_347);
x_349 = lean_st_ref_set(x_5, x_348, x_340);
lean_dec(x_5);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_351 = x_349;
} else {
 lean_dec_ref(x_349);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_351;
 lean_ctor_set_tag(x_352, 1);
}
lean_ctor_set(x_352, 0, x_333);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_353 = lean_ctor_get(x_4, 3);
lean_inc(x_353);
x_354 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_5, x_8);
x_355 = lean_ctor_get(x_2, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
lean_dec(x_354);
x_358 = lean_ctor_get(x_2, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_2, 2);
lean_inc(x_359);
x_360 = lean_ctor_get(x_2, 3);
lean_inc(x_360);
x_361 = lean_ctor_get(x_2, 4);
lean_inc(x_361);
x_362 = !lean_is_exclusive(x_355);
if (x_362 == 0)
{
uint8_t x_363; lean_object* x_364; lean_object* x_365; 
x_363 = 0;
lean_ctor_set_uint8(x_355, 5, x_363);
x_364 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_364, 0, x_355);
lean_ctor_set(x_364, 1, x_358);
lean_ctor_set(x_364, 2, x_359);
lean_ctor_set(x_364, 3, x_360);
lean_ctor_set(x_364, 4, x_361);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_365 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_364, x_3, x_4, x_5, x_357);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_Meta_check___closed__4;
x_369 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_356, x_368, x_353, x_2, x_3, x_4, x_5, x_367);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_370 = !lean_is_exclusive(x_369);
if (x_370 == 0)
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_369, 0);
lean_dec(x_371);
lean_ctor_set(x_369, 0, x_366);
return x_369;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
lean_dec(x_369);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_366);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_374 = lean_ctor_get(x_365, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_365, 1);
lean_inc(x_375);
lean_dec(x_365);
x_376 = l_Lean_Meta_check___closed__4;
x_377 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_356, x_376, x_353, x_2, x_3, x_4, x_5, x_375);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 0);
lean_dec(x_379);
lean_ctor_set_tag(x_377, 1);
lean_ctor_set(x_377, 0, x_374);
return x_377;
}
else
{
lean_object* x_380; lean_object* x_381; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
lean_dec(x_377);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_374);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; uint8_t x_383; uint8_t x_384; uint8_t x_385; uint8_t x_386; uint8_t x_387; uint8_t x_388; uint8_t x_389; uint8_t x_390; uint8_t x_391; uint8_t x_392; uint8_t x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_382 = lean_ctor_get_uint8(x_355, 0);
x_383 = lean_ctor_get_uint8(x_355, 1);
x_384 = lean_ctor_get_uint8(x_355, 2);
x_385 = lean_ctor_get_uint8(x_355, 3);
x_386 = lean_ctor_get_uint8(x_355, 4);
x_387 = lean_ctor_get_uint8(x_355, 6);
x_388 = lean_ctor_get_uint8(x_355, 7);
x_389 = lean_ctor_get_uint8(x_355, 8);
x_390 = lean_ctor_get_uint8(x_355, 9);
x_391 = lean_ctor_get_uint8(x_355, 10);
x_392 = lean_ctor_get_uint8(x_355, 11);
x_393 = lean_ctor_get_uint8(x_355, 12);
lean_dec(x_355);
x_394 = 0;
x_395 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_395, 0, x_382);
lean_ctor_set_uint8(x_395, 1, x_383);
lean_ctor_set_uint8(x_395, 2, x_384);
lean_ctor_set_uint8(x_395, 3, x_385);
lean_ctor_set_uint8(x_395, 4, x_386);
lean_ctor_set_uint8(x_395, 5, x_394);
lean_ctor_set_uint8(x_395, 6, x_387);
lean_ctor_set_uint8(x_395, 7, x_388);
lean_ctor_set_uint8(x_395, 8, x_389);
lean_ctor_set_uint8(x_395, 9, x_390);
lean_ctor_set_uint8(x_395, 10, x_391);
lean_ctor_set_uint8(x_395, 11, x_392);
lean_ctor_set_uint8(x_395, 12, x_393);
x_396 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_358);
lean_ctor_set(x_396, 2, x_359);
lean_ctor_set(x_396, 3, x_360);
lean_ctor_set(x_396, 4, x_361);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_397 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_396, x_3, x_4, x_5, x_357);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = l_Lean_Meta_check___closed__4;
x_401 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_356, x_400, x_353, x_2, x_3, x_4, x_5, x_399);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_403 = x_401;
} else {
 lean_dec_ref(x_401);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_398);
lean_ctor_set(x_404, 1, x_402);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_405 = lean_ctor_get(x_397, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_397, 1);
lean_inc(x_406);
lean_dec(x_397);
x_407 = l_Lean_Meta_check___closed__4;
x_408 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__12(x_356, x_407, x_353, x_2, x_3, x_4, x_5, x_406);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_410;
 lean_ctor_set_tag(x_411, 1);
}
lean_ctor_set(x_411, 0, x_405);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_isTypeCorrect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeError");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isTypeCorrect___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_check___closed__2;
x_2 = l_Lean_Meta_isTypeCorrect___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_check(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = 1;
x_11 = lean_box(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_18 = x_7;
} else {
 lean_dec_ref(x_7);
 x_18 = lean_box(0);
}
x_19 = l_Lean_Meta_isTypeCorrect___closed__2;
x_36 = lean_st_ref_get(x_5, x_17);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = 0;
x_20 = x_41;
x_21 = x_40;
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_19, x_2, x_3, x_4, x_5, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_20 = x_46;
x_21 = x_45;
goto block_35;
}
block_35:
{
if (x_20 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = 0;
x_23 = lean_box(x_22);
if (lean_is_scalar(x_18)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_18;
 lean_ctor_set_tag(x_24, 0);
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_18);
x_25 = l_Lean_Exception_toMessageData(x_16);
x_26 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_19, x_25, x_2, x_3, x_4, x_5, x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_1920_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_check___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_isTypeCorrect___closed__2;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_InferType(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Check(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12);
l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13 = _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13();
lean_mark_persistent(l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__13);
l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___spec__1___closed__2);
l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__1 = _init_l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__1();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__1);
l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__2 = _init_l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__2();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff___closed__2);
l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1 = _init_l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1);
l_Lean_Meta_addPPExplicitToExposeDiff___closed__1 = _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__1();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff___closed__1);
l_Lean_Meta_addPPExplicitToExposeDiff___closed__2 = _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__2();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff___closed__2);
l_Lean_Meta_addPPExplicitToExposeDiff___closed__3 = _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__3();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff___closed__3);
l_Lean_Meta_addPPExplicitToExposeDiff___closed__4 = _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__4();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff___closed__4);
l_Lean_Meta_addPPExplicitToExposeDiff___closed__5 = _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__5();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff___closed__5);
l_Lean_Meta_addPPExplicitToExposeDiff___closed__6 = _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__6();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff___closed__6);
l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__1 = _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__1);
l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2 = _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2);
l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3 = _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3);
l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__4 = _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__4();
lean_mark_persistent(l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__4);
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1);
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2);
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3);
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__4 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__4);
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__5 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__5);
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__6 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__6);
l_Lean_Meta_checkApp___closed__1 = _init_l_Lean_Meta_checkApp___closed__1();
lean_mark_persistent(l_Lean_Meta_checkApp___closed__1);
l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___closed__1 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___closed__1);
l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___closed__1 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___closed__1);
l_Lean_Meta_check___closed__1 = _init_l_Lean_Meta_check___closed__1();
lean_mark_persistent(l_Lean_Meta_check___closed__1);
l_Lean_Meta_check___closed__2 = _init_l_Lean_Meta_check___closed__2();
lean_mark_persistent(l_Lean_Meta_check___closed__2);
l_Lean_Meta_check___closed__3 = _init_l_Lean_Meta_check___closed__3();
lean_mark_persistent(l_Lean_Meta_check___closed__3);
l_Lean_Meta_check___closed__4 = _init_l_Lean_Meta_check___closed__4();
lean_mark_persistent(l_Lean_Meta_check___closed__4);
l_Lean_Meta_isTypeCorrect___closed__1 = _init_l_Lean_Meta_isTypeCorrect___closed__1();
lean_mark_persistent(l_Lean_Meta_isTypeCorrect___closed__1);
l_Lean_Meta_isTypeCorrect___closed__2 = _init_l_Lean_Meta_isTypeCorrect___closed__2();
lean_mark_persistent(l_Lean_Meta_isTypeCorrect___closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_1920_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
