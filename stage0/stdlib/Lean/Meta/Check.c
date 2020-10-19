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
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___closed__1;
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_check___closed__1;
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage_match__1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isTypeCorrect___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwFunctionExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__4;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check___closed__2;
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__37;
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_match__1(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__3;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect___closed__1;
lean_object* l_Lean_Meta_isTypeCorrect___closed__2;
lean_object* l_Lean_Meta_inferType___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_inferTypeRef;
extern lean_object* l_Lean_MessageData_nil___closed__1;
lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet_match__1(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isTypeCorrect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
extern lean_object* l_Lean_Meta_Lean_Ref;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___at___private_Lean_Meta_Check_0__Lean_Meta_ensureType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_15__runDefEqM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l_EIO_MonadExceptOf(lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain_match__1(lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__2;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5;
lean_object* l_Lean_addErrorMessageContextDefault___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_MonadExceptOf___rarg(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__6;
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Lean_AddMessageContext;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExceptOf___rarg(lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2;
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isTypeCorrect___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_943_(lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__1;
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___at___private_Lean_Meta_Check_0__Lean_Meta_ensureType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_InferType_4__getLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_InferType_4__getLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
lean_dec(x_5);
x_13 = lean_box(x_12);
x_14 = lean_apply_6(x_2, x_7, x_8, x_9, x_10, x_11, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwLetTypeMismatchMessage_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_4, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_18);
x_19 = l_Lean_Meta_inferTypeRef;
x_20 = lean_st_ref_get(x_19, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_2, x_3, x_4, x_5, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_inferTypeRef;
x_28 = lean_st_ref_get(x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_2, x_3, x_26, x_5, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Check");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.throwLetTypeMismatchMessage");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
x_2 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2;
x_3 = lean_unsigned_to_nat(27u);
x_4 = lean_unsigned_to_nat(7u);
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid let declaration, term");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nhas type");
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
x_1 = lean_mk_string("\nbut is expected to have type");
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
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_local_ctx_find(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_10 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3;
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
x_14 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_15 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3;
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
x_20 = l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_indentExpr(x_19);
x_24 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_indentExpr(x_21);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_18);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(x_35, x_2, x_3, x_4, x_5, x_22);
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
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwLetTypeMismatchMessage___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_17 = lean_box(x_16);
x_18 = lean_apply_6(x_3, x_11, x_12, x_13, x_14, x_15, x_17);
return x_18;
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__4;
x_9 = l_Lean_Meta_getFVarLocalDecl___rarg(x_8, x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_14 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_13, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_6(x_1, x_13, x_3, x_4, x_5, x_6, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_11, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 4);
lean_inc(x_23);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
x_24 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_22, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
x_26 = lean_apply_6(x_1, x_22, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_23);
x_28 = l_Lean_Meta_inferType___rarg(x_8, x_23);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = lean_apply_5(x_28, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_isExprDefEq___rarg(x_8, x_22, x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = lean_apply_5(x_32, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lean_Expr_fvarId_x21(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_38 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg(x_37, x_3, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_apply_6(x_1, x_23, x_3, x_4, x_5, x_6, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_apply_6(x_1, x_23, x_3, x_4, x_5, x_6, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_33);
if (x_47 == 0)
{
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_29);
if (x_51 == 0)
{
return x_29;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_29, 0);
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_29);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_26);
if (x_55 == 0)
{
return x_26;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_26, 0);
x_57 = lean_ctor_get(x_26, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_26);
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
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_24);
if (x_59 == 0)
{
return x_24;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_24, 0);
x_61 = lean_ctor_get(x_24, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_24);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
return x_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__2___boxed), 7, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_forMAux___main___rarg(x_2, x_10, x_3, x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_apply_5(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_6(x_1, x_4, x_5, x_6, x_7, x_8, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__3), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_11 = l_Lean_Meta_lambdaLetTelescope___rarg(x_10, x_8, lean_box(0), x_2, x_9);
x_12 = lean_apply_5(x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__4;
x_9 = l_Lean_Meta_getFVarLocalDecl___rarg(x_8, x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_LocalDecl_type(x_11);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_14 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_13, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_6(x_1, x_13, x_3, x_4, x_5, x_6, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__1___boxed), 7, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_forMAux___main___rarg(x_2, x_10, x_3, x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_apply_5(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_6(x_1, x_4, x_5, x_6, x_7, x_8, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__2), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_11 = l_Lean_Meta_forallTelescope___rarg(x_10, x_8, lean_box(0), x_2, x_9);
x_12 = lean_apply_5(x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_environment_find(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_7);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(x_17, x_2, x_3, x_4, x_5, x_10);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = lean_environment_find(x_22, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(x_28, x_2, x_3, x_4, x_5, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_13 = l_List_lengthAux___main___rarg(x_2, x_12);
x_14 = l_Lean_ConstantInfo_lparams(x_10);
lean_dec(x_10);
x_15 = l_List_lengthAux___main___rarg(x_14, x_12);
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
x_22 = l_List_lengthAux___main___rarg(x_2, x_21);
x_23 = l_Lean_ConstantInfo_lparams(x_19);
lean_dec(x_19);
x_24 = l_List_lengthAux___main___rarg(x_23, x_21);
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
lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_4, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_18);
x_19 = l_Lean_Meta_whnfRef;
x_20 = lean_st_ref_get(x_19, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_2, x_3, x_4, x_5, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_whnfRef;
x_28 = lean_st_ref_get(x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_2, x_3, x_26, x_5, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l_Lean_Meta_whnf___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 6);
x_26 = lean_ctor_get_uint8(x_8, 7);
lean_dec(x_8);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_28, 0, x_20);
lean_ctor_set_uint8(x_28, 1, x_21);
lean_ctor_set_uint8(x_28, 2, x_22);
lean_ctor_set_uint8(x_28, 3, x_23);
lean_ctor_set_uint8(x_28, 4, x_24);
lean_ctor_set_uint8(x_28, 5, x_27);
lean_ctor_set_uint8(x_28, 6, x_25);
lean_ctor_set_uint8(x_28, 7, x_26);
lean_ctor_set(x_2, 0, x_28);
x_29 = l_Lean_Meta_whnf___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_41 = lean_ctor_get_uint8(x_38, 0);
x_42 = lean_ctor_get_uint8(x_38, 1);
x_43 = lean_ctor_get_uint8(x_38, 2);
x_44 = lean_ctor_get_uint8(x_38, 3);
x_45 = lean_ctor_get_uint8(x_38, 4);
x_46 = lean_ctor_get_uint8(x_38, 6);
x_47 = lean_ctor_get_uint8(x_38, 7);
if (lean_is_exclusive(x_38)) {
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
 x_48 = lean_box(0);
}
x_49 = 1;
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 0, 8);
} else {
 x_50 = x_48;
}
lean_ctor_set_uint8(x_50, 0, x_41);
lean_ctor_set_uint8(x_50, 1, x_42);
lean_ctor_set_uint8(x_50, 2, x_43);
lean_ctor_set_uint8(x_50, 3, x_44);
lean_ctor_set_uint8(x_50, 4, x_45);
lean_ctor_set_uint8(x_50, 5, x_49);
lean_ctor_set_uint8(x_50, 6, x_46);
lean_ctor_set_uint8(x_50, 7, x_47);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_39);
lean_ctor_set(x_51, 2, x_40);
x_52 = l_Lean_Meta_whnf___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__2(x_1, x_51, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_10 = l_Lean_Meta_whnfD___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
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
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Meta_throwFunctionExpected___rarg(x_1, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KernelException_toMessageData___closed__37;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nargument");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_10 = l_Lean_indentExpr(x_1);
x_11 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_indentExpr(x_2);
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_indentExpr(x_3);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_9);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = l_Lean_throwError___rarg(x_5, x_6, x_7, x_8, lean_box(0), x_28);
return x_29;
}
}
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain), 6, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_apply_2(x_2, lean_box(0), x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1), 9, 8);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_7);
lean_closure_set(x_14, 6, x_8);
lean_closure_set(x_14, 7, x_9);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_6);
x_9 = l_Lean_mkApp(x_6, x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_5);
x_11 = l_Lean_Meta_inferType___rarg(x_5, x_7);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__2), 11, 10);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_7);
lean_closure_set(x_12, 4, x_8);
lean_closure_set(x_12, 5, x_1);
lean_closure_set(x_12, 6, x_2);
lean_closure_set(x_12, 7, x_3);
lean_closure_set(x_12, 8, x_4);
lean_closure_set(x_12, 9, x_10);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_throwAppTypeMismatch___rarg), 8, 0);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EIO_MonadExceptOf(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__1;
x_2 = l_StateRefT_x27_MonadExceptOf___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__2;
x_2 = l_ReaderT_MonadExceptOf___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__3;
x_2 = l_StateRefT_x27_MonadExceptOf___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__4;
x_2 = l_ReaderT_MonadExceptOf___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Lean_AddMessageContext;
x_2 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_addErrorMessageContextDefault___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__4;
lean_inc(x_2);
x_14 = l_Lean_Meta_inferType___rarg(x_13, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_apply_5(x_14, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_whnf___rarg(x_13, x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = lean_apply_5(x_18, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 7)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_3);
x_23 = l_Lean_Meta_inferType___rarg(x_13, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = lean_apply_5(x_23, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_isExprDefEq___rarg(x_13, x_22, x_25);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = lean_apply_5(x_27, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_33 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__5;
x_34 = l_Lean_Meta_Lean_Ref;
x_35 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__6;
x_36 = l_Lean_MessageData_nil___closed__1;
x_37 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_32, x_33, x_34, x_35, x_13, x_2, x_3, x_36);
x_38 = lean_apply_5(x_37, x_4, x_5, x_6, x_7, x_31);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_28, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_28, 0, x_41);
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
return x_28;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_28, 0);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_28);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_20);
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_dec(x_19);
x_54 = l_Lean_mkApp(x_2, x_3);
x_55 = l_Lean_Meta_throwFunctionExpected___rarg(x_54, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_19, 0);
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_11);
if (x_64 == 0)
{
return x_11;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_11, 0);
x_66 = lean_ctor_get(x_11, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_11);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_9);
if (x_68 == 0)
{
return x_9;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_5, x_10, x_11, x_13);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_6, x_15, x_16, x_18);
return x_19;
}
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_5(x_3, x_1, x_20, x_21, x_22, x_24);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_5(x_2, x_1, x_26, x_27, x_28, x_30);
return x_31;
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_37 = lean_box_uint64(x_36);
x_38 = lean_apply_6(x_4, x_1, x_32, x_33, x_34, x_35, x_37);
return x_38;
}
case 10:
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_3(x_7, x_39, x_40, x_42);
return x_43;
}
case 11:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_48 = lean_box_uint64(x_47);
x_49 = lean_apply_4(x_8, x_44, x_45, x_46, x_48);
return x_49;
}
default: 
{
lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_apply_1(x_9, x_1);
return x_50;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_match__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_236 = lean_st_ref_get(x_6, x_7);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 3);
lean_inc(x_238);
lean_dec(x_237);
x_239 = lean_ctor_get_uint8(x_238, sizeof(void*)*1);
lean_dec(x_238);
if (x_239 == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
lean_dec(x_236);
x_241 = 0;
x_9 = x_241;
x_10 = x_240;
goto block_235;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
lean_dec(x_236);
x_243 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_244 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_243, x_3, x_4, x_5, x_6, x_242);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_unbox(x_245);
lean_dec(x_245);
x_9 = x_247;
x_10 = x_246;
goto block_235;
}
block_235:
{
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_st_ref_get(x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_6, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_60; 
x_23 = 0;
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_23);
x_24 = lean_st_ref_set(x_6, x_17, x_19);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_8, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_61);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_63, 0, x_1);
lean_closure_set(x_63, 1, x_2);
lean_closure_set(x_63, 2, x_61);
x_64 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_65 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_64, x_63, x_3, x_4, x_5, x_6, x_62);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_get(x_6, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_6, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_70, 3);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_15);
x_76 = lean_st_ref_set(x_6, x_70, x_72);
lean_dec(x_6);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_61);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_15);
lean_ctor_set(x_70, 3, x_82);
x_83 = lean_st_ref_set(x_6, x_70, x_72);
lean_dec(x_6);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_61);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = lean_ctor_get(x_70, 0);
x_88 = lean_ctor_get(x_70, 1);
x_89 = lean_ctor_get(x_70, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_70);
x_90 = lean_ctor_get(x_71, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_91 = x_71;
} else {
 lean_dec_ref(x_71);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_15);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_st_ref_set(x_6, x_93, x_72);
lean_dec(x_6);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_61);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_60, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_60, 1);
lean_inc(x_99);
lean_dec(x_60);
x_26 = x_98;
x_27 = x_99;
goto block_59;
}
block_59:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_st_ref_get(x_6, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_take(x_6, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 3);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_15);
x_37 = lean_st_ref_set(x_6, x_31, x_33);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_26);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_15);
lean_ctor_set(x_31, 3, x_43);
x_44 = lean_st_ref_set(x_6, x_31, x_33);
lean_dec(x_6);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
x_50 = lean_ctor_get(x_31, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_51 = lean_ctor_get(x_32, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_52 = x_32;
} else {
 lean_dec_ref(x_32);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 1);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_15);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_ref_set(x_6, x_54, x_33);
lean_dec(x_6);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_126; 
x_100 = lean_ctor_get(x_18, 0);
lean_inc(x_100);
lean_dec(x_18);
x_101 = 0;
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_101);
lean_ctor_set(x_17, 3, x_102);
x_103 = lean_st_ref_set(x_6, x_17, x_19);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_126 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_8, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_127);
x_129 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_129, 0, x_1);
lean_closure_set(x_129, 1, x_2);
lean_closure_set(x_129, 2, x_127);
x_130 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_131 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_130, x_129, x_3, x_4, x_5, x_6, x_128);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_st_ref_get(x_6, x_132);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_take(x_6, x_134);
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
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(0, 4, 0);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_141);
lean_ctor_set(x_146, 3, x_145);
x_147 = lean_st_ref_set(x_6, x_146, x_138);
lean_dec(x_6);
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
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_127);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = lean_ctor_get(x_126, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_126, 1);
lean_inc(x_152);
lean_dec(x_126);
x_105 = x_151;
x_106 = x_152;
goto block_125;
}
block_125:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_107 = lean_st_ref_get(x_6, x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_st_ref_take(x_6, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 2);
lean_inc(x_115);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 x_116 = x_110;
} else {
 lean_dec_ref(x_110);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 1, 1);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 4, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set(x_120, 2, x_115);
lean_ctor_set(x_120, 3, x_119);
x_121 = lean_st_ref_set(x_6, x_120, x_112);
lean_dec(x_6);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_105);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_184; 
x_153 = lean_ctor_get(x_17, 0);
x_154 = lean_ctor_get(x_17, 1);
x_155 = lean_ctor_get(x_17, 2);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_17);
x_156 = lean_ctor_get(x_18, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_157 = x_18;
} else {
 lean_dec_ref(x_18);
 x_157 = lean_box(0);
}
x_158 = 0;
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 1, 1);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_154);
lean_ctor_set(x_160, 2, x_155);
lean_ctor_set(x_160, 3, x_159);
x_161 = lean_st_ref_set(x_6, x_160, x_19);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_184 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_8, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_185);
x_187 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_187, 0, x_1);
lean_closure_set(x_187, 1, x_2);
lean_closure_set(x_187, 2, x_185);
x_188 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_189 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_188, x_187, x_3, x_4, x_5, x_6, x_186);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_st_ref_get(x_6, x_190);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_st_ref_take(x_6, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_194, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_ctor_get(x_194, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 2);
lean_inc(x_199);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_200 = x_194;
} else {
 lean_dec_ref(x_194);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_195, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_202 = x_195;
} else {
 lean_dec_ref(x_195);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 1, 1);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_200)) {
 x_204 = lean_alloc_ctor(0, 4, 0);
} else {
 x_204 = x_200;
}
lean_ctor_set(x_204, 0, x_197);
lean_ctor_set(x_204, 1, x_198);
lean_ctor_set(x_204, 2, x_199);
lean_ctor_set(x_204, 3, x_203);
x_205 = lean_st_ref_set(x_6, x_204, x_196);
lean_dec(x_6);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_185);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_184, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_184, 1);
lean_inc(x_210);
lean_dec(x_184);
x_163 = x_209;
x_164 = x_210;
goto block_183;
}
block_183:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_165 = lean_st_ref_get(x_6, x_164);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_st_ref_take(x_6, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 2);
lean_inc(x_173);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 x_174 = x_168;
} else {
 lean_dec_ref(x_168);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_169, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_176 = x_169;
} else {
 lean_dec_ref(x_169);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 1);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 4, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_171);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_177);
x_179 = lean_st_ref_set(x_6, x_178, x_170);
lean_dec(x_6);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
 lean_ctor_set_tag(x_182, 1);
}
lean_ctor_set(x_182, 0, x_163);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_5, 3);
lean_inc(x_211);
x_212 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_6, x_10);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_215 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_8, x_3, x_4, x_5, x_6, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_inc(x_216);
x_218 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_218, 0, x_1);
lean_closure_set(x_218, 1, x_2);
lean_closure_set(x_218, 2, x_216);
x_219 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_220 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_219, x_218, x_3, x_4, x_5, x_6, x_217);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_213, x_219, x_211, x_3, x_4, x_5, x_6, x_221);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_222, 0);
lean_dec(x_224);
lean_ctor_set(x_222, 0, x_216);
return x_222;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_216);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_ctor_get(x_215, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_215, 1);
lean_inc(x_228);
lean_dec(x_215);
x_229 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_230 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_213, x_229, x_211, x_3, x_4, x_5, x_6, x_228);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_230, 0);
lean_dec(x_232);
lean_ctor_set_tag(x_230, 1);
lean_ctor_set(x_230, 0, x_227);
return x_230;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_227);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
}
}
lean_object* l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_mkApp(x_1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_10 = l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(x_1, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_indentExpr(x_9);
x_17 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_indentExpr(x_2);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_indentExpr(x_11);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_14);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(x_34, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Meta_whnf___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__2(x_13, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 7)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(x_2, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__2(x_18, x_20, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_MessageData_nil___closed__1;
x_27 = l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3(x_1, x_2, x_26, x_3, x_4, x_5, x_6, x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
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
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_16);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_dec(x_15);
x_43 = l_Lean_mkApp(x_1, x_2);
x_44 = l_Lean_Meta_throwFunctionExpected___rarg(x_43, x_3, x_4, x_5, x_6, x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
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
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
return x_12;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_12, 0);
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_10);
if (x_53 == 0)
{
return x_10;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_10, 0);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_10);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_8);
if (x_57 == 0)
{
return x_8;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_8, 0);
x_59 = lean_ctor_get(x_8, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_8);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_fvarId_x21(x_1);
x_8 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
x_13 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5(x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_17 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_16, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_16, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
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
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_14, 4);
lean_inc(x_34);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_35 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_33, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
x_37 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_33, x_3, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_34);
x_39 = l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(x_34, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__2(x_33, x_40, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Lean_Expr_fvarId_x21(x_12);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_47 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg(x_46, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_34, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_2, x_51);
lean_dec(x_2);
x_2 = x_52;
x_7 = x_50;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_12);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_dec(x_42);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_63 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_34, x_3, x_4, x_5, x_6, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_2, x_65);
lean_dec(x_2);
x_2 = x_66;
x_7 = x_64;
goto _start;
}
else
{
uint8_t x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 0);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_42);
if (x_72 == 0)
{
return x_42;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_42, 0);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_42);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_39);
if (x_76 == 0)
{
return x_39;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_39, 0);
x_78 = lean_ctor_get(x_39, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_39);
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
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
return x_37;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_37, 0);
x_82 = lean_ctor_get(x_37, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_37);
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
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_35);
if (x_84 == 0)
{
return x_35;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_35, 0);
x_86 = lean_ctor_get(x_35, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_35);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_13);
if (x_88 == 0)
{
return x_13;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_13, 0);
x_90 = lean_ctor_get(x_13, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_13);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_2, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___closed__1;
x_8 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
x_13 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5(x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_type(x_14);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_17 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_16, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_16, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
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
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__8(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_2, x_3, x_4, x_5, x_6, x_10);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___closed__1;
x_8 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_12 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1(x_10, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
case 6:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1___boxed), 7, 0);
x_14 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
case 7:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___lambda__1___boxed), 7, 0);
x_16 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_1, x_15, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
case 8:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1___boxed), 7, 0);
x_18 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(x_1, x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
case 10:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_1 = x_19;
goto _start;
}
case 11:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_1 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_check___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("check");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_check___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_check___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_380 = lean_st_ref_get(x_5, x_6);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_381, 3);
lean_inc(x_382);
lean_dec(x_381);
x_383 = lean_ctor_get_uint8(x_382, sizeof(void*)*1);
lean_dec(x_382);
if (x_383 == 0)
{
lean_object* x_384; uint8_t x_385; 
x_384 = lean_ctor_get(x_380, 1);
lean_inc(x_384);
lean_dec(x_380);
x_385 = 0;
x_7 = x_385;
x_8 = x_384;
goto block_379;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
x_386 = lean_ctor_get(x_380, 1);
lean_inc(x_386);
lean_dec(x_380);
x_387 = l_Lean_Meta_check___closed__2;
x_388 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_387, x_2, x_3, x_4, x_5, x_386);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_unbox(x_389);
lean_dec(x_389);
x_7 = x_391;
x_8 = x_390;
goto block_379;
}
block_379:
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
uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get_uint8(x_23, 0);
x_97 = lean_ctor_get_uint8(x_23, 1);
x_98 = lean_ctor_get_uint8(x_23, 2);
x_99 = lean_ctor_get_uint8(x_23, 3);
x_100 = lean_ctor_get_uint8(x_23, 4);
x_101 = lean_ctor_get_uint8(x_23, 6);
x_102 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
x_103 = 0;
x_104 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_104, 0, x_96);
lean_ctor_set_uint8(x_104, 1, x_97);
lean_ctor_set_uint8(x_104, 2, x_98);
lean_ctor_set_uint8(x_104, 3, x_99);
lean_ctor_set_uint8(x_104, 4, x_100);
lean_ctor_set_uint8(x_104, 5, x_103);
lean_ctor_set_uint8(x_104, 6, x_101);
lean_ctor_set_uint8(x_104, 7, x_102);
lean_ctor_set(x_2, 0, x_104);
lean_inc(x_5);
x_105 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_get(x_5, x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_st_ref_take(x_5, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 2);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 1, 1);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 4, 0);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_115);
lean_ctor_set(x_121, 2, x_116);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_5, x_121, x_113);
lean_dec(x_5);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_126 = lean_ctor_get(x_105, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_105, 1);
lean_inc(x_127);
lean_dec(x_105);
x_128 = lean_st_ref_get(x_5, x_127);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_5, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 2);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_139 = x_132;
} else {
 lean_dec_ref(x_132);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 1, 1);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_137)) {
 x_141 = lean_alloc_ctor(0, 4, 0);
} else {
 x_141 = x_137;
}
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_135);
lean_ctor_set(x_141, 2, x_136);
lean_ctor_set(x_141, 3, x_140);
x_142 = lean_st_ref_set(x_5, x_141, x_133);
lean_dec(x_5);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
 lean_ctor_set_tag(x_145, 1);
}
lean_ctor_set(x_145, 0, x_126);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_146 = lean_ctor_get(x_2, 1);
x_147 = lean_ctor_get(x_2, 2);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_2);
x_148 = lean_ctor_get_uint8(x_23, 0);
x_149 = lean_ctor_get_uint8(x_23, 1);
x_150 = lean_ctor_get_uint8(x_23, 2);
x_151 = lean_ctor_get_uint8(x_23, 3);
x_152 = lean_ctor_get_uint8(x_23, 4);
x_153 = lean_ctor_get_uint8(x_23, 6);
x_154 = lean_ctor_get_uint8(x_23, 7);
if (lean_is_exclusive(x_23)) {
 x_155 = x_23;
} else {
 lean_dec_ref(x_23);
 x_155 = lean_box(0);
}
x_156 = 0;
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 0, 8);
} else {
 x_157 = x_155;
}
lean_ctor_set_uint8(x_157, 0, x_148);
lean_ctor_set_uint8(x_157, 1, x_149);
lean_ctor_set_uint8(x_157, 2, x_150);
lean_ctor_set_uint8(x_157, 3, x_151);
lean_ctor_set_uint8(x_157, 4, x_152);
lean_ctor_set_uint8(x_157, 5, x_156);
lean_ctor_set_uint8(x_157, 6, x_153);
lean_ctor_set_uint8(x_157, 7, x_154);
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_146);
lean_ctor_set(x_158, 2, x_147);
lean_inc(x_5);
x_159 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_158, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_st_ref_get(x_5, x_161);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_st_ref_take(x_5, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_168 = lean_ctor_get(x_165, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 2);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_166, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_173 = x_166;
} else {
 lean_dec_ref(x_166);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 1, 1);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_171)) {
 x_175 = lean_alloc_ctor(0, 4, 0);
} else {
 x_175 = x_171;
}
lean_ctor_set(x_175, 0, x_168);
lean_ctor_set(x_175, 1, x_169);
lean_ctor_set(x_175, 2, x_170);
lean_ctor_set(x_175, 3, x_174);
x_176 = lean_st_ref_set(x_5, x_175, x_167);
lean_dec(x_5);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_160);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_180 = lean_ctor_get(x_159, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_159, 1);
lean_inc(x_181);
lean_dec(x_159);
x_182 = lean_st_ref_get(x_5, x_181);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_st_ref_take(x_5, x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
lean_dec(x_184);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 2);
lean_inc(x_190);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_191 = x_185;
} else {
 lean_dec_ref(x_185);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_186, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_193 = x_186;
} else {
 lean_dec_ref(x_186);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 1, 1);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(0, 4, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_188);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set(x_195, 2, x_190);
lean_ctor_set(x_195, 3, x_194);
x_196 = lean_st_ref_set(x_5, x_195, x_187);
lean_dec(x_5);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_180);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
else
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_200 = lean_ctor_get(x_16, 0);
lean_inc(x_200);
lean_dec(x_16);
x_201 = 0;
x_202 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*1, x_201);
lean_ctor_set(x_15, 3, x_202);
x_203 = lean_st_ref_set(x_5, x_15, x_17);
x_204 = lean_ctor_get(x_2, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_2, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_2, 2);
lean_inc(x_207);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_208 = x_2;
} else {
 lean_dec_ref(x_2);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get_uint8(x_204, 0);
x_210 = lean_ctor_get_uint8(x_204, 1);
x_211 = lean_ctor_get_uint8(x_204, 2);
x_212 = lean_ctor_get_uint8(x_204, 3);
x_213 = lean_ctor_get_uint8(x_204, 4);
x_214 = lean_ctor_get_uint8(x_204, 6);
x_215 = lean_ctor_get_uint8(x_204, 7);
if (lean_is_exclusive(x_204)) {
 x_216 = x_204;
} else {
 lean_dec_ref(x_204);
 x_216 = lean_box(0);
}
x_217 = 0;
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 0, 8);
} else {
 x_218 = x_216;
}
lean_ctor_set_uint8(x_218, 0, x_209);
lean_ctor_set_uint8(x_218, 1, x_210);
lean_ctor_set_uint8(x_218, 2, x_211);
lean_ctor_set_uint8(x_218, 3, x_212);
lean_ctor_set_uint8(x_218, 4, x_213);
lean_ctor_set_uint8(x_218, 5, x_217);
lean_ctor_set_uint8(x_218, 6, x_214);
lean_ctor_set_uint8(x_218, 7, x_215);
if (lean_is_scalar(x_208)) {
 x_219 = lean_alloc_ctor(0, 3, 0);
} else {
 x_219 = x_208;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_206);
lean_ctor_set(x_219, 2, x_207);
lean_inc(x_5);
x_220 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_219, x_3, x_4, x_5, x_205);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_st_ref_get(x_5, x_222);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_225 = lean_st_ref_take(x_5, x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_226, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = lean_ctor_get(x_226, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_226, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_226, 2);
lean_inc(x_231);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 x_232 = x_226;
} else {
 lean_dec_ref(x_226);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_227, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_234 = x_227;
} else {
 lean_dec_ref(x_227);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(0, 1, 1);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set_uint8(x_235, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_232)) {
 x_236 = lean_alloc_ctor(0, 4, 0);
} else {
 x_236 = x_232;
}
lean_ctor_set(x_236, 0, x_229);
lean_ctor_set(x_236, 1, x_230);
lean_ctor_set(x_236, 2, x_231);
lean_ctor_set(x_236, 3, x_235);
x_237 = lean_st_ref_set(x_5, x_236, x_228);
lean_dec(x_5);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_221);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_241 = lean_ctor_get(x_220, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_220, 1);
lean_inc(x_242);
lean_dec(x_220);
x_243 = lean_st_ref_get(x_5, x_242);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_st_ref_take(x_5, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 3);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_dec(x_245);
x_249 = lean_ctor_get(x_246, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_246, 2);
lean_inc(x_251);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 lean_ctor_release(x_246, 3);
 x_252 = x_246;
} else {
 lean_dec_ref(x_246);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_247, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 1, 1);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set_uint8(x_255, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_252)) {
 x_256 = lean_alloc_ctor(0, 4, 0);
} else {
 x_256 = x_252;
}
lean_ctor_set(x_256, 0, x_249);
lean_ctor_set(x_256, 1, x_250);
lean_ctor_set(x_256, 2, x_251);
lean_ctor_set(x_256, 3, x_255);
x_257 = lean_st_ref_set(x_5, x_256, x_248);
lean_dec(x_5);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
 lean_ctor_set_tag(x_260, 1);
}
lean_ctor_set(x_260, 0, x_241);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_261 = lean_ctor_get(x_15, 0);
x_262 = lean_ctor_get(x_15, 1);
x_263 = lean_ctor_get(x_15, 2);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_15);
x_264 = lean_ctor_get(x_16, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_265 = x_16;
} else {
 lean_dec_ref(x_16);
 x_265 = lean_box(0);
}
x_266 = 0;
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 1, 1);
} else {
 x_267 = x_265;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set_uint8(x_267, sizeof(void*)*1, x_266);
x_268 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_268, 0, x_261);
lean_ctor_set(x_268, 1, x_262);
lean_ctor_set(x_268, 2, x_263);
lean_ctor_set(x_268, 3, x_267);
x_269 = lean_st_ref_set(x_5, x_268, x_17);
x_270 = lean_ctor_get(x_2, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_2, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_2, 2);
lean_inc(x_273);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_274 = x_2;
} else {
 lean_dec_ref(x_2);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get_uint8(x_270, 0);
x_276 = lean_ctor_get_uint8(x_270, 1);
x_277 = lean_ctor_get_uint8(x_270, 2);
x_278 = lean_ctor_get_uint8(x_270, 3);
x_279 = lean_ctor_get_uint8(x_270, 4);
x_280 = lean_ctor_get_uint8(x_270, 6);
x_281 = lean_ctor_get_uint8(x_270, 7);
if (lean_is_exclusive(x_270)) {
 x_282 = x_270;
} else {
 lean_dec_ref(x_270);
 x_282 = lean_box(0);
}
x_283 = 0;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(0, 0, 8);
} else {
 x_284 = x_282;
}
lean_ctor_set_uint8(x_284, 0, x_275);
lean_ctor_set_uint8(x_284, 1, x_276);
lean_ctor_set_uint8(x_284, 2, x_277);
lean_ctor_set_uint8(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, 4, x_279);
lean_ctor_set_uint8(x_284, 5, x_283);
lean_ctor_set_uint8(x_284, 6, x_280);
lean_ctor_set_uint8(x_284, 7, x_281);
if (lean_is_scalar(x_274)) {
 x_285 = lean_alloc_ctor(0, 3, 0);
} else {
 x_285 = x_274;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_272);
lean_ctor_set(x_285, 2, x_273);
lean_inc(x_5);
x_286 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_285, x_3, x_4, x_5, x_271);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_st_ref_get(x_5, x_288);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_st_ref_take(x_5, x_290);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_292, 3);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
x_295 = lean_ctor_get(x_292, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_292, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_292, 2);
lean_inc(x_297);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 lean_ctor_release(x_292, 2);
 lean_ctor_release(x_292, 3);
 x_298 = x_292;
} else {
 lean_dec_ref(x_292);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_293, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 x_300 = x_293;
} else {
 lean_dec_ref(x_293);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(0, 1, 1);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set_uint8(x_301, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_298)) {
 x_302 = lean_alloc_ctor(0, 4, 0);
} else {
 x_302 = x_298;
}
lean_ctor_set(x_302, 0, x_295);
lean_ctor_set(x_302, 1, x_296);
lean_ctor_set(x_302, 2, x_297);
lean_ctor_set(x_302, 3, x_301);
x_303 = lean_st_ref_set(x_5, x_302, x_294);
lean_dec(x_5);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_305 = x_303;
} else {
 lean_dec_ref(x_303);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_287);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_307 = lean_ctor_get(x_286, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_286, 1);
lean_inc(x_308);
lean_dec(x_286);
x_309 = lean_st_ref_get(x_5, x_308);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec(x_309);
x_311 = lean_st_ref_take(x_5, x_310);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 3);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_ctor_get(x_312, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_312, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_312, 2);
lean_inc(x_317);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 lean_ctor_release(x_312, 3);
 x_318 = x_312;
} else {
 lean_dec_ref(x_312);
 x_318 = lean_box(0);
}
x_319 = lean_ctor_get(x_313, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_320 = x_313;
} else {
 lean_dec_ref(x_313);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 1, 1);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set_uint8(x_321, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_318)) {
 x_322 = lean_alloc_ctor(0, 4, 0);
} else {
 x_322 = x_318;
}
lean_ctor_set(x_322, 0, x_315);
lean_ctor_set(x_322, 1, x_316);
lean_ctor_set(x_322, 2, x_317);
lean_ctor_set(x_322, 3, x_321);
x_323 = lean_st_ref_set(x_5, x_322, x_314);
lean_dec(x_5);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
 lean_ctor_set_tag(x_326, 1);
}
lean_ctor_set(x_326, 0, x_307);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_327 = lean_ctor_get(x_4, 3);
lean_inc(x_327);
x_328 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_5, x_8);
x_329 = lean_ctor_get(x_2, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_328, 1);
lean_inc(x_331);
lean_dec(x_328);
x_332 = lean_ctor_get(x_2, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_2, 2);
lean_inc(x_333);
x_334 = !lean_is_exclusive(x_329);
if (x_334 == 0)
{
uint8_t x_335; lean_object* x_336; lean_object* x_337; 
x_335 = 0;
lean_ctor_set_uint8(x_329, 5, x_335);
x_336 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_336, 0, x_329);
lean_ctor_set(x_336, 1, x_332);
lean_ctor_set(x_336, 2, x_333);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_337 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_336, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = l_Lean_Meta_check___closed__2;
x_341 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_330, x_340, x_327, x_2, x_3, x_4, x_5, x_339);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_342 = !lean_is_exclusive(x_341);
if (x_342 == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_341, 0);
lean_dec(x_343);
lean_ctor_set(x_341, 0, x_338);
return x_341;
}
else
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
lean_dec(x_341);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_338);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
x_346 = lean_ctor_get(x_337, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_337, 1);
lean_inc(x_347);
lean_dec(x_337);
x_348 = l_Lean_Meta_check___closed__2;
x_349 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_330, x_348, x_327, x_2, x_3, x_4, x_5, x_347);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_349, 0);
lean_dec(x_351);
lean_ctor_set_tag(x_349, 1);
lean_ctor_set(x_349, 0, x_346);
return x_349;
}
else
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_dec(x_349);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_346);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
else
{
uint8_t x_354; uint8_t x_355; uint8_t x_356; uint8_t x_357; uint8_t x_358; uint8_t x_359; uint8_t x_360; uint8_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_354 = lean_ctor_get_uint8(x_329, 0);
x_355 = lean_ctor_get_uint8(x_329, 1);
x_356 = lean_ctor_get_uint8(x_329, 2);
x_357 = lean_ctor_get_uint8(x_329, 3);
x_358 = lean_ctor_get_uint8(x_329, 4);
x_359 = lean_ctor_get_uint8(x_329, 6);
x_360 = lean_ctor_get_uint8(x_329, 7);
lean_dec(x_329);
x_361 = 0;
x_362 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_362, 0, x_354);
lean_ctor_set_uint8(x_362, 1, x_355);
lean_ctor_set_uint8(x_362, 2, x_356);
lean_ctor_set_uint8(x_362, 3, x_357);
lean_ctor_set_uint8(x_362, 4, x_358);
lean_ctor_set_uint8(x_362, 5, x_361);
lean_ctor_set_uint8(x_362, 6, x_359);
lean_ctor_set_uint8(x_362, 7, x_360);
x_363 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_332);
lean_ctor_set(x_363, 2, x_333);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_364 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_363, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = l_Lean_Meta_check___closed__2;
x_368 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_330, x_367, x_327, x_2, x_3, x_4, x_5, x_366);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_370 = x_368;
} else {
 lean_dec_ref(x_368);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_365);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_372 = lean_ctor_get(x_364, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_364, 1);
lean_inc(x_373);
lean_dec(x_364);
x_374 = l_Lean_Meta_check___closed__2;
x_375 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_330, x_374, x_327, x_2, x_3, x_4, x_5, x_373);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_377 = x_375;
} else {
 lean_dec_ref(x_375);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_377;
 lean_ctor_set_tag(x_378, 1);
}
lean_ctor_set(x_378, 0, x_372);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isTypeCorrect___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_checkTraceOption(x_7, x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_isTypeCorrect___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 3);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_10);
lean_inc(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Std_PersistentArray_push___rarg(x_19, x_21);
lean_ctor_set(x_14, 0, x_22);
x_23 = lean_st_ref_set(x_6, x_13, x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_10);
lean_inc(x_8);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_31, x_33);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_30);
lean_ctor_set(x_13, 3, x_35);
x_36 = lean_st_ref_set(x_6, x_13, x_15);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
x_43 = lean_ctor_get(x_13, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_44 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_46 = x_14;
} else {
 lean_dec_ref(x_14);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_10);
lean_inc(x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_PersistentArray_push___rarg(x_45, x_48);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(0, 1, 1);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_44);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_st_ref_set(x_6, x_51, x_15);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
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
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_isTypeCorrect___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isTypeCorrect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_st_ref_get(x_5, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = l_Lean_Meta_isTypeCorrect___closed__2;
x_32 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isTypeCorrect___spec__1(x_31, x_2, x_3, x_4, x_5, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = 0;
x_38 = lean_box(x_37);
lean_ctor_set(x_32, 0, x_38);
return x_32;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_dec(x_32);
x_44 = l_Lean_Exception_toMessageData(x_16);
x_45 = l_Lean_addTrace___at_Lean_Meta_isTypeCorrect___spec__2(x_31, x_44, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = 0;
x_49 = lean_box(x_48);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = 0;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isTypeCorrect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isTypeCorrect___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_isTypeCorrect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_Meta_isTypeCorrect___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_943_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_check___closed__2;
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
lean_object* initialize_Lean_Meta_Check(lean_object* w) {
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
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1);
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2);
l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3 = _init_l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__1 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__1);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__2 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__2);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__3 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__3);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__4 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__4);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__5 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__5);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__6 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__6);
l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___closed__1 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___closed__1);
l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___closed__1 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__7___closed__1);
l_Lean_Meta_check___closed__1 = _init_l_Lean_Meta_check___closed__1();
lean_mark_persistent(l_Lean_Meta_check___closed__1);
l_Lean_Meta_check___closed__2 = _init_l_Lean_Meta_check___closed__2();
lean_mark_persistent(l_Lean_Meta_check___closed__2);
l_Lean_Meta_isTypeCorrect___closed__1 = _init_l_Lean_Meta_isTypeCorrect___closed__1();
lean_mark_persistent(l_Lean_Meta_isTypeCorrect___closed__1);
l_Lean_Meta_isTypeCorrect___closed__2 = _init_l_Lean_Meta_isTypeCorrect___closed__2();
lean_mark_persistent(l_Lean_Meta_isTypeCorrect___closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_943_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
