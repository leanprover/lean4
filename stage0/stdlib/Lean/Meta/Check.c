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
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_check___closed__1;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage_match__1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__9;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwFunctionExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__4;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check___closed__2;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__8;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__37;
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__3;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2;
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__2;
lean_object* l_Lean_Meta_isTypeCorrect___closed__1;
lean_object* l_Lean_Meta_isTypeCorrect___closed__2;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___closed__1;
lean_object* l_Lean_Meta_inferType___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp_match__1(lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil___closed__1;
lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_check___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__2;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__10;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet_match__1(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__7;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ReaderT_MonadLift___closed__1;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Lean_Exception___instance__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_toArray___rarg(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_Lean_CoreM___instance__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_MonadExceptOf(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___closed__1;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5;
lean_object* l_Lean_addErrorMessageContextDefault___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_MonadExceptOf___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MonadCacheT_Lean_Util_MonadCache___instance__4___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__6;
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_MonadExceptOf___rarg(lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2;
lean_object* l_ReaderT_MonadFunctor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Lean_Meta_Basic___instance__7;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_943_(lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__1;
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_5 = l_Lean_Name_getString_x21___closed__3;
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
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
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
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
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
x_20 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_19, x_2, x_3, x_4, x_5, x_6);
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
x_36 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_35, x_2, x_3, x_4, x_5, x_22);
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
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
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
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___lambda__3), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
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
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
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
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___lambda__2), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
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
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_10 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
lean_closure_set(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_Lean_CoreM___instance__3;
x_2 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__6;
x_3 = l_Lean_MonadCacheT_Lean_Util_MonadCache___instance__4___closed__1;
x_4 = l_Lean_Lean_Exception___instance__2___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
lean_closure_set(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__7;
x_2 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__8;
x_3 = l_ReaderT_MonadLift___closed__1;
x_4 = l_Lean_Lean_Exception___instance__2___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Lean_Meta_Basic___instance__7;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
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
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
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
x_32 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_33 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__5;
x_34 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__9;
x_35 = l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__10;
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
lean_object* l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_10 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
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
x_35 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_34, x_4, x_5, x_6, x_7, x_15);
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
x_12 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_11);
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
x_15 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_13, x_3, x_4, x_5, x_6, x_14);
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
x_19 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_2, x_3, x_4, x_5, x_6, x_17);
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
x_22 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_18, x_20, x_3, x_4, x_5, x_6, x_21);
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
x_27 = l_Lean_Meta_throwAppTypeMismatch___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__2(x_1, x_2, x_26, x_3, x_4, x_5, x_6, x_25);
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
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
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
x_39 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_34, x_3, x_4, x_5, x_6, x_38);
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
x_42 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_33, x_40, x_3, x_4, x_5, x_6, x_41);
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
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
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
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___closed__1;
x_8 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
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
x_13 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___closed__1;
x_8 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__3___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
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
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___lambda__1___boxed), 7, 0);
x_14 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__2___rarg(x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
case 7:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___lambda__1___boxed), 7, 0);
x_16 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__3___rarg(x_1, x_15, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
case 8:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___lambda__1___boxed), 7, 0);
x_18 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__2___rarg(x_1, x_17, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forMAux___main___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
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
lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 3);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = l_Std_PersistentArray_empty___closed__1;
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_st_ref_set(x_1, x_9, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_23 = l_Std_PersistentArray_empty___closed__1;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_22);
lean_ctor_set(x_9, 3, x_24);
x_25 = lean_st_ref_set(x_1, x_9, x_11);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
x_31 = lean_ctor_get(x_9, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_32 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_33 = x_10;
} else {
 lean_dec_ref(x_10);
 x_33 = lean_box(0);
}
x_34 = l_Std_PersistentArray_empty___closed__1;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 1, 1);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_32);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_st_ref_set(x_1, x_36, x_11);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 3);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = l_Std_PersistentArray_isEmpty___rarg(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = l_Std_PersistentArray_toArray___rarg(x_16);
lean_dec(x_16);
x_19 = x_18;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_umapMAux___main___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_20, x_19);
x_22 = x_21;
x_23 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Std_PersistentArray_push___rarg(x_1, x_25);
lean_ctor_set(x_11, 0, x_26);
x_27 = lean_st_ref_set(x_7, x_10, x_12);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_1);
x_34 = lean_st_ref_set(x_7, x_10, x_12);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
lean_dec(x_11);
x_43 = l_Std_PersistentArray_isEmpty___rarg(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = l_Std_PersistentArray_toArray___rarg(x_42);
lean_dec(x_42);
x_45 = x_44;
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_umapMAux___main___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_46, x_45);
x_48 = x_47;
x_49 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Std_PersistentArray_push___rarg(x_1, x_51);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_41);
lean_ctor_set(x_10, 3, x_53);
x_54 = lean_st_ref_set(x_7, x_10, x_12);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_41);
lean_ctor_set(x_10, 3, x_59);
x_60 = lean_st_ref_set(x_7, x_10, x_12);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
x_67 = lean_ctor_get(x_10, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_68 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_69 = lean_ctor_get(x_11, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_70 = x_11;
} else {
 lean_dec_ref(x_11);
 x_70 = lean_box(0);
}
x_71 = l_Std_PersistentArray_isEmpty___rarg(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = l_Std_PersistentArray_toArray___rarg(x_69);
lean_dec(x_69);
x_73 = x_72;
x_74 = lean_unsigned_to_nat(0u);
x_75 = l_Array_umapMAux___main___at___private_Lean_Util_Trace_0__Lean_addNode___spec__1(x_74, x_73);
x_76 = x_75;
x_77 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_78, 0, x_2);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_3);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Std_PersistentArray_push___rarg(x_1, x_79);
if (lean_is_scalar(x_70)) {
 x_81 = lean_alloc_ctor(0, 1, 1);
} else {
 x_81 = x_70;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_68);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_65);
lean_ctor_set(x_82, 1, x_66);
lean_ctor_set(x_82, 2, x_67);
lean_ctor_set(x_82, 3, x_81);
x_83 = lean_st_ref_set(x_7, x_82, x_12);
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
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_69);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_70)) {
 x_88 = lean_alloc_ctor(0, 1, 1);
} else {
 x_88 = x_70;
}
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_68);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_65);
lean_ctor_set(x_89, 1, x_66);
lean_ctor_set(x_89, 2, x_67);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_7, x_89, x_12);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__2;
x_2 = l_Lean_Meta_check___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_384 = lean_st_ref_get(x_5, x_6);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_385, 3);
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_ctor_get_uint8(x_386, sizeof(void*)*1);
lean_dec(x_386);
if (x_387 == 0)
{
lean_object* x_388; uint8_t x_389; 
x_388 = lean_ctor_get(x_384, 1);
lean_inc(x_388);
lean_dec(x_384);
x_389 = 0;
x_7 = x_389;
x_8 = x_388;
goto block_383;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_390 = lean_ctor_get(x_384, 1);
lean_inc(x_390);
lean_dec(x_384);
x_391 = l_Lean_Meta_check___closed__2;
x_392 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_check___spec__3(x_391, x_2, x_3, x_4, x_5, x_390);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = lean_unbox(x_393);
lean_dec(x_393);
x_7 = x_395;
x_8 = x_394;
goto block_383;
}
block_383:
{
uint8_t x_9; 
if (x_7 == 0)
{
uint8_t x_381; 
x_381 = 1;
x_9 = x_381;
goto block_380;
}
else
{
uint8_t x_382; 
x_382 = 0;
x_9 = x_382;
goto block_380;
}
block_380:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___rarg(x_5, x_8);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
lean_ctor_set_uint8(x_12, 5, x_18);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_19, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_check___closed__2;
x_24 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2(x_13, x_23, x_10, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_Meta_check___closed__2;
x_32 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2(x_13, x_31, x_10, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_29);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get_uint8(x_12, 0);
x_38 = lean_ctor_get_uint8(x_12, 1);
x_39 = lean_ctor_get_uint8(x_12, 2);
x_40 = lean_ctor_get_uint8(x_12, 3);
x_41 = lean_ctor_get_uint8(x_12, 4);
x_42 = lean_ctor_get_uint8(x_12, 6);
x_43 = lean_ctor_get_uint8(x_12, 7);
lean_dec(x_12);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_45, 0, x_37);
lean_ctor_set_uint8(x_45, 1, x_38);
lean_ctor_set_uint8(x_45, 2, x_39);
lean_ctor_set_uint8(x_45, 3, x_40);
lean_ctor_set_uint8(x_45, 4, x_41);
lean_ctor_set_uint8(x_45, 5, x_44);
lean_ctor_set_uint8(x_45, 6, x_42);
lean_ctor_set_uint8(x_45, 7, x_43);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_15);
lean_ctor_set(x_46, 2, x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_47 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_46, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_check___closed__2;
x_51 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2(x_13, x_50, x_10, x_2, x_3, x_4, x_5, x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = l_Lean_Meta_check___closed__2;
x_58 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2(x_13, x_57, x_10, x_2, x_3, x_4, x_5, x_56);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_st_ref_get(x_5, x_8);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
x_67 = lean_st_ref_take(x_5, x_65);
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
uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = 0;
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_74);
x_75 = lean_st_ref_set(x_5, x_68, x_70);
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = !lean_is_exclusive(x_2);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_2, 0);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
uint8_t x_81; lean_object* x_82; 
x_81 = 0;
lean_ctor_set_uint8(x_76, 5, x_81);
lean_inc(x_5);
x_82 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_2, x_3, x_4, x_5, x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_get(x_5, x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_st_ref_take(x_5, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_88, 3);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_66);
x_94 = lean_st_ref_set(x_5, x_88, x_90);
lean_dec(x_5);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_83);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_89, 0);
lean_inc(x_99);
lean_dec(x_89);
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_66);
lean_ctor_set(x_88, 3, x_100);
x_101 = lean_st_ref_set(x_5, x_88, x_90);
lean_dec(x_5);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_83);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_88, 0);
x_106 = lean_ctor_get(x_88, 1);
x_107 = lean_ctor_get(x_88, 2);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_88);
x_108 = lean_ctor_get(x_89, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_109 = x_89;
} else {
 lean_dec_ref(x_89);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 1, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_66);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_106);
lean_ctor_set(x_111, 2, x_107);
lean_ctor_set(x_111, 3, x_110);
x_112 = lean_st_ref_set(x_5, x_111, x_90);
lean_dec(x_5);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_83);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_ctor_get(x_82, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_82, 1);
lean_inc(x_117);
lean_dec(x_82);
x_118 = lean_st_ref_get(x_5, x_117);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_st_ref_take(x_5, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = !lean_is_exclusive(x_121);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_121, 3);
lean_dec(x_125);
x_126 = !lean_is_exclusive(x_122);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_66);
x_127 = lean_st_ref_set(x_5, x_121, x_123);
lean_dec(x_5);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 0);
lean_dec(x_129);
lean_ctor_set_tag(x_127, 1);
lean_ctor_set(x_127, 0, x_116);
return x_127;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_122, 0);
lean_inc(x_132);
lean_dec(x_122);
x_133 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_66);
lean_ctor_set(x_121, 3, x_133);
x_134 = lean_st_ref_set(x_5, x_121, x_123);
lean_dec(x_5);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
 lean_ctor_set_tag(x_137, 1);
}
lean_ctor_set(x_137, 0, x_116);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_138 = lean_ctor_get(x_121, 0);
x_139 = lean_ctor_get(x_121, 1);
x_140 = lean_ctor_get(x_121, 2);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_121);
x_141 = lean_ctor_get(x_122, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_142 = x_122;
} else {
 lean_dec_ref(x_122);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 1, 1);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_66);
x_144 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_139);
lean_ctor_set(x_144, 2, x_140);
lean_ctor_set(x_144, 3, x_143);
x_145 = lean_st_ref_set(x_5, x_144, x_123);
lean_dec(x_5);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
 lean_ctor_set_tag(x_148, 1);
}
lean_ctor_set(x_148, 0, x_116);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
else
{
uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; 
x_149 = lean_ctor_get_uint8(x_76, 0);
x_150 = lean_ctor_get_uint8(x_76, 1);
x_151 = lean_ctor_get_uint8(x_76, 2);
x_152 = lean_ctor_get_uint8(x_76, 3);
x_153 = lean_ctor_get_uint8(x_76, 4);
x_154 = lean_ctor_get_uint8(x_76, 6);
x_155 = lean_ctor_get_uint8(x_76, 7);
lean_dec(x_76);
x_156 = 0;
x_157 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_157, 0, x_149);
lean_ctor_set_uint8(x_157, 1, x_150);
lean_ctor_set_uint8(x_157, 2, x_151);
lean_ctor_set_uint8(x_157, 3, x_152);
lean_ctor_set_uint8(x_157, 4, x_153);
lean_ctor_set_uint8(x_157, 5, x_156);
lean_ctor_set_uint8(x_157, 6, x_154);
lean_ctor_set_uint8(x_157, 7, x_155);
lean_ctor_set(x_2, 0, x_157);
lean_inc(x_5);
x_158 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_2, x_3, x_4, x_5, x_77);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_st_ref_get(x_5, x_160);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_st_ref_take(x_5, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_164, 2);
lean_inc(x_169);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 x_170 = x_164;
} else {
 lean_dec_ref(x_164);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_165, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_172 = x_165;
} else {
 lean_dec_ref(x_165);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 1, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_170)) {
 x_174 = lean_alloc_ctor(0, 4, 0);
} else {
 x_174 = x_170;
}
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_168);
lean_ctor_set(x_174, 2, x_169);
lean_ctor_set(x_174, 3, x_173);
x_175 = lean_st_ref_set(x_5, x_174, x_166);
lean_dec(x_5);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_159);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_179 = lean_ctor_get(x_158, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_158, 1);
lean_inc(x_180);
lean_dec(x_158);
x_181 = lean_st_ref_get(x_5, x_180);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_st_ref_take(x_5, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 2);
lean_inc(x_189);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 x_190 = x_184;
} else {
 lean_dec_ref(x_184);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_185, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_192 = x_185;
} else {
 lean_dec_ref(x_185);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 1, 1);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_190)) {
 x_194 = lean_alloc_ctor(0, 4, 0);
} else {
 x_194 = x_190;
}
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_188);
lean_ctor_set(x_194, 2, x_189);
lean_ctor_set(x_194, 3, x_193);
x_195 = lean_st_ref_set(x_5, x_194, x_186);
lean_dec(x_5);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_179);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_199 = lean_ctor_get(x_2, 1);
x_200 = lean_ctor_get(x_2, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_2);
x_201 = lean_ctor_get_uint8(x_76, 0);
x_202 = lean_ctor_get_uint8(x_76, 1);
x_203 = lean_ctor_get_uint8(x_76, 2);
x_204 = lean_ctor_get_uint8(x_76, 3);
x_205 = lean_ctor_get_uint8(x_76, 4);
x_206 = lean_ctor_get_uint8(x_76, 6);
x_207 = lean_ctor_get_uint8(x_76, 7);
if (lean_is_exclusive(x_76)) {
 x_208 = x_76;
} else {
 lean_dec_ref(x_76);
 x_208 = lean_box(0);
}
x_209 = 0;
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 0, 8);
} else {
 x_210 = x_208;
}
lean_ctor_set_uint8(x_210, 0, x_201);
lean_ctor_set_uint8(x_210, 1, x_202);
lean_ctor_set_uint8(x_210, 2, x_203);
lean_ctor_set_uint8(x_210, 3, x_204);
lean_ctor_set_uint8(x_210, 4, x_205);
lean_ctor_set_uint8(x_210, 5, x_209);
lean_ctor_set_uint8(x_210, 6, x_206);
lean_ctor_set_uint8(x_210, 7, x_207);
x_211 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_199);
lean_ctor_set(x_211, 2, x_200);
lean_inc(x_5);
x_212 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_211, x_3, x_4, x_5, x_77);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_st_ref_get(x_5, x_214);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_take(x_5, x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
x_221 = lean_ctor_get(x_218, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_218, 2);
lean_inc(x_223);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 x_224 = x_218;
} else {
 lean_dec_ref(x_218);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_219, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_226 = x_219;
} else {
 lean_dec_ref(x_219);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(0, 1, 1);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set_uint8(x_227, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_224)) {
 x_228 = lean_alloc_ctor(0, 4, 0);
} else {
 x_228 = x_224;
}
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_222);
lean_ctor_set(x_228, 2, x_223);
lean_ctor_set(x_228, 3, x_227);
x_229 = lean_st_ref_set(x_5, x_228, x_220);
lean_dec(x_5);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_213);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_233 = lean_ctor_get(x_212, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_212, 1);
lean_inc(x_234);
lean_dec(x_212);
x_235 = lean_st_ref_get(x_5, x_234);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_st_ref_take(x_5, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_238, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_ctor_get(x_238, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_238, 2);
lean_inc(x_243);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 lean_ctor_release(x_238, 3);
 x_244 = x_238;
} else {
 lean_dec_ref(x_238);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_239, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_246 = x_239;
} else {
 lean_dec_ref(x_239);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(0, 1, 1);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set_uint8(x_247, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_244)) {
 x_248 = lean_alloc_ctor(0, 4, 0);
} else {
 x_248 = x_244;
}
lean_ctor_set(x_248, 0, x_241);
lean_ctor_set(x_248, 1, x_242);
lean_ctor_set(x_248, 2, x_243);
lean_ctor_set(x_248, 3, x_247);
x_249 = lean_st_ref_set(x_5, x_248, x_240);
lean_dec(x_5);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
 lean_ctor_set_tag(x_252, 1);
}
lean_ctor_set(x_252, 0, x_233);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_263; uint8_t x_264; uint8_t x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_253 = lean_ctor_get(x_69, 0);
lean_inc(x_253);
lean_dec(x_69);
x_254 = 0;
x_255 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set_uint8(x_255, sizeof(void*)*1, x_254);
lean_ctor_set(x_68, 3, x_255);
x_256 = lean_st_ref_set(x_5, x_68, x_70);
x_257 = lean_ctor_get(x_2, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_2, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_2, 2);
lean_inc(x_260);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_261 = x_2;
} else {
 lean_dec_ref(x_2);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get_uint8(x_257, 0);
x_263 = lean_ctor_get_uint8(x_257, 1);
x_264 = lean_ctor_get_uint8(x_257, 2);
x_265 = lean_ctor_get_uint8(x_257, 3);
x_266 = lean_ctor_get_uint8(x_257, 4);
x_267 = lean_ctor_get_uint8(x_257, 6);
x_268 = lean_ctor_get_uint8(x_257, 7);
if (lean_is_exclusive(x_257)) {
 x_269 = x_257;
} else {
 lean_dec_ref(x_257);
 x_269 = lean_box(0);
}
x_270 = 0;
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 0, 8);
} else {
 x_271 = x_269;
}
lean_ctor_set_uint8(x_271, 0, x_262);
lean_ctor_set_uint8(x_271, 1, x_263);
lean_ctor_set_uint8(x_271, 2, x_264);
lean_ctor_set_uint8(x_271, 3, x_265);
lean_ctor_set_uint8(x_271, 4, x_266);
lean_ctor_set_uint8(x_271, 5, x_270);
lean_ctor_set_uint8(x_271, 6, x_267);
lean_ctor_set_uint8(x_271, 7, x_268);
if (lean_is_scalar(x_261)) {
 x_272 = lean_alloc_ctor(0, 3, 0);
} else {
 x_272 = x_261;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_259);
lean_ctor_set(x_272, 2, x_260);
lean_inc(x_5);
x_273 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_272, x_3, x_4, x_5, x_258);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_st_ref_get(x_5, x_275);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
x_278 = lean_st_ref_take(x_5, x_277);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_279, 3);
lean_inc(x_280);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
lean_dec(x_278);
x_282 = lean_ctor_get(x_279, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_279, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_279, 2);
lean_inc(x_284);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 x_285 = x_279;
} else {
 lean_dec_ref(x_279);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_280, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_287 = x_280;
} else {
 lean_dec_ref(x_280);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 1, 1);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set_uint8(x_288, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(0, 4, 0);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_282);
lean_ctor_set(x_289, 1, x_283);
lean_ctor_set(x_289, 2, x_284);
lean_ctor_set(x_289, 3, x_288);
x_290 = lean_st_ref_set(x_5, x_289, x_281);
lean_dec(x_5);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_292 = x_290;
} else {
 lean_dec_ref(x_290);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_274);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_294 = lean_ctor_get(x_273, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_273, 1);
lean_inc(x_295);
lean_dec(x_273);
x_296 = lean_st_ref_get(x_5, x_295);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_298 = lean_st_ref_take(x_5, x_297);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_299, 3);
lean_inc(x_300);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_ctor_get(x_299, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_299, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_299, 2);
lean_inc(x_304);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 lean_ctor_release(x_299, 2);
 lean_ctor_release(x_299, 3);
 x_305 = x_299;
} else {
 lean_dec_ref(x_299);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_300, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 x_307 = x_300;
} else {
 lean_dec_ref(x_300);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(0, 1, 1);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_305)) {
 x_309 = lean_alloc_ctor(0, 4, 0);
} else {
 x_309 = x_305;
}
lean_ctor_set(x_309, 0, x_302);
lean_ctor_set(x_309, 1, x_303);
lean_ctor_set(x_309, 2, x_304);
lean_ctor_set(x_309, 3, x_308);
x_310 = lean_st_ref_set(x_5, x_309, x_301);
lean_dec(x_5);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
 lean_ctor_set_tag(x_313, 1);
}
lean_ctor_set(x_313, 0, x_294);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; uint8_t x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; uint8_t x_333; uint8_t x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_314 = lean_ctor_get(x_68, 0);
x_315 = lean_ctor_get(x_68, 1);
x_316 = lean_ctor_get(x_68, 2);
lean_inc(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_68);
x_317 = lean_ctor_get(x_69, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_318 = x_69;
} else {
 lean_dec_ref(x_69);
 x_318 = lean_box(0);
}
x_319 = 0;
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(0, 1, 1);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set_uint8(x_320, sizeof(void*)*1, x_319);
x_321 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_321, 0, x_314);
lean_ctor_set(x_321, 1, x_315);
lean_ctor_set(x_321, 2, x_316);
lean_ctor_set(x_321, 3, x_320);
x_322 = lean_st_ref_set(x_5, x_321, x_70);
x_323 = lean_ctor_get(x_2, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_2, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_2, 2);
lean_inc(x_326);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_327 = x_2;
} else {
 lean_dec_ref(x_2);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get_uint8(x_323, 0);
x_329 = lean_ctor_get_uint8(x_323, 1);
x_330 = lean_ctor_get_uint8(x_323, 2);
x_331 = lean_ctor_get_uint8(x_323, 3);
x_332 = lean_ctor_get_uint8(x_323, 4);
x_333 = lean_ctor_get_uint8(x_323, 6);
x_334 = lean_ctor_get_uint8(x_323, 7);
if (lean_is_exclusive(x_323)) {
 x_335 = x_323;
} else {
 lean_dec_ref(x_323);
 x_335 = lean_box(0);
}
x_336 = 0;
if (lean_is_scalar(x_335)) {
 x_337 = lean_alloc_ctor(0, 0, 8);
} else {
 x_337 = x_335;
}
lean_ctor_set_uint8(x_337, 0, x_328);
lean_ctor_set_uint8(x_337, 1, x_329);
lean_ctor_set_uint8(x_337, 2, x_330);
lean_ctor_set_uint8(x_337, 3, x_331);
lean_ctor_set_uint8(x_337, 4, x_332);
lean_ctor_set_uint8(x_337, 5, x_336);
lean_ctor_set_uint8(x_337, 6, x_333);
lean_ctor_set_uint8(x_337, 7, x_334);
if (lean_is_scalar(x_327)) {
 x_338 = lean_alloc_ctor(0, 3, 0);
} else {
 x_338 = x_327;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_325);
lean_ctor_set(x_338, 2, x_326);
lean_inc(x_5);
x_339 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_338, x_3, x_4, x_5, x_324);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_st_ref_get(x_5, x_341);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
x_344 = lean_st_ref_take(x_5, x_343);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 3);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
lean_dec(x_344);
x_348 = lean_ctor_get(x_345, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_345, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_345, 2);
lean_inc(x_350);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 x_351 = x_345;
} else {
 lean_dec_ref(x_345);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_346, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_353 = x_346;
} else {
 lean_dec_ref(x_346);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(0, 1, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set_uint8(x_354, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_351)) {
 x_355 = lean_alloc_ctor(0, 4, 0);
} else {
 x_355 = x_351;
}
lean_ctor_set(x_355, 0, x_348);
lean_ctor_set(x_355, 1, x_349);
lean_ctor_set(x_355, 2, x_350);
lean_ctor_set(x_355, 3, x_354);
x_356 = lean_st_ref_set(x_5, x_355, x_347);
lean_dec(x_5);
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_358 = x_356;
} else {
 lean_dec_ref(x_356);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_340);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_360 = lean_ctor_get(x_339, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_339, 1);
lean_inc(x_361);
lean_dec(x_339);
x_362 = lean_st_ref_get(x_5, x_361);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
x_364 = lean_st_ref_take(x_5, x_363);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_365, 3);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_ctor_get(x_365, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_365, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_365, 2);
lean_inc(x_370);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 x_371 = x_365;
} else {
 lean_dec_ref(x_365);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_366, 0);
lean_inc(x_372);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_373 = x_366;
} else {
 lean_dec_ref(x_366);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 1, 1);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_371)) {
 x_375 = lean_alloc_ctor(0, 4, 0);
} else {
 x_375 = x_371;
}
lean_ctor_set(x_375, 0, x_368);
lean_ctor_set(x_375, 1, x_369);
lean_ctor_set(x_375, 2, x_370);
lean_ctor_set(x_375, 3, x_374);
x_376 = lean_st_ref_set(x_5, x_375, x_367);
lean_dec(x_5);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
 lean_ctor_set_tag(x_379, 1);
}
lean_ctor_set(x_379, 0, x_360);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_check___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_check___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_check___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__2;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
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
x_19 = x_41;
x_20 = x_40;
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l_Lean_Meta_isTypeCorrect___closed__2;
x_44 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_43, x_2, x_3, x_4, x_5, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_19 = x_47;
x_20 = x_46;
goto block_35;
}
block_35:
{
if (x_19 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = 0;
x_22 = lean_box(x_21);
if (lean_is_scalar(x_18)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_18;
 lean_ctor_set_tag(x_23, 0);
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_18);
x_24 = l_Lean_Exception_toMessageData(x_16);
x_25 = l_Lean_Meta_isTypeCorrect___closed__2;
x_26 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_25, x_24, x_2, x_3, x_4, x_5, x_20);
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
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__7 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__7);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__8 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__8);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__9 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__9);
l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__10 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkApp___closed__10);
l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___closed__1 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkLambdaLet___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__3___closed__1);
l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___closed__1 = _init_l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Check_0__Lean_Meta_checkForall___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__5___closed__1);
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
