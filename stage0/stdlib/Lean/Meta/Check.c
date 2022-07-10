// Lean compiler output
// Module: Lean.Meta.Check
// Imports: Init Lean.Meta.InferType
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
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__4(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2(lean_object*);
static lean_object* l_Lean_Meta_check___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1(lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__4;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___closed__1;
static lean_object* l_Lean_Meta_check___closed__4;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
lean_object* l_Lean_Meta_throwFunctionExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_check___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__8(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Meta_isTypeCorrect___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwLetTypeMismatchMessage(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__4___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__2;
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__1;
static lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__4;
static lean_object* l_Lean_Meta_isTypeCorrect___closed__1;
static lean_object* l_Lean_Meta_isTypeCorrect___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__3;
static lean_object* l_Lean_Meta_check___closed__3;
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__5;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwAppTypeMismatch___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__2(lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___closed__1;
lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__2;
static lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1___closed__6;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__2;
static lean_object* l_Lean_Meta_addPPExplicitToExposeDiff___closed__6;
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_2604_(lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(lean_object*, lean_object*);
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
static lean_object* _init_l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Check", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.throwLetTypeMismatchMessage", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
x_2 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__2;
x_3 = lean_unsigned_to_nat(24u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid let declaration, term", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nhas type", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nbut is expected to have type", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__11;
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
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4;
x_10 = l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_11);
x_12 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__4;
x_13 = l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 4);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_15);
x_16 = lean_infer_type(x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_indentExpr(x_15);
x_20 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__6;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_17);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_indentExpr(x_14);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3___rarg(x_31, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
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
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(62u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_2, x_25);
lean_dec(x_25);
x_27 = lean_array_get_size(x_24);
x_28 = lean_nat_dec_lt(x_2, x_27);
lean_dec(x_27);
if (x_26 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4;
x_30 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_29);
if (x_28 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_31);
lean_inc(x_30);
x_32 = l_Lean_Meta_isExprDefEq(x_30, x_31, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_30, x_31, x_6, x_7, x_8, x_9, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_array_set(x_23, x_2, x_39);
x_42 = lean_array_set(x_24, x_2, x_40);
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_5);
x_16 = x_43;
x_17 = x_38;
goto block_21;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
lean_dec(x_30);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_5);
x_16 = x_45;
x_17 = x_44;
goto block_21;
}
}
else
{
uint8_t x_46; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_32);
if (x_46 == 0)
{
return x_32;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_32, 0);
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_32);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_array_fget(x_24, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_50);
lean_inc(x_30);
x_51 = l_Lean_Meta_isExprDefEq(x_30, x_50, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_30, x_50, x_6, x_7, x_8, x_9, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_array_set(x_23, x_2, x_58);
x_61 = lean_array_set(x_24, x_2, x_59);
lean_ctor_set(x_5, 1, x_61);
lean_ctor_set(x_5, 0, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_5);
x_16 = x_62;
x_17 = x_57;
goto block_21;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_50);
lean_dec(x_30);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_dec(x_51);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_5);
x_16 = x_64;
x_17 = x_63;
goto block_21;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
return x_51;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_51, 0);
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_51);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; 
x_69 = lean_array_fget(x_23, x_2);
if (x_28 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4;
x_71 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_70);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_71);
lean_inc(x_69);
x_72 = l_Lean_Meta_isExprDefEq(x_69, x_71, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_76 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_69, x_71, x_6, x_7, x_8, x_9, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_array_set(x_23, x_2, x_79);
x_82 = lean_array_set(x_24, x_2, x_80);
lean_ctor_set(x_5, 1, x_82);
lean_ctor_set(x_5, 0, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_5);
x_16 = x_83;
x_17 = x_78;
goto block_21;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_71);
lean_dec(x_69);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
lean_dec(x_72);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_5);
x_16 = x_85;
x_17 = x_84;
goto block_21;
}
}
else
{
uint8_t x_86; 
lean_dec(x_71);
lean_dec(x_69);
lean_free_object(x_5);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_72);
if (x_86 == 0)
{
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_72, 0);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_72);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_array_fget(x_24, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_90);
lean_inc(x_69);
x_91 = l_Lean_Meta_isExprDefEq(x_69, x_90, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_95 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_69, x_90, x_6, x_7, x_8, x_9, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_array_set(x_23, x_2, x_98);
x_101 = lean_array_set(x_24, x_2, x_99);
lean_ctor_set(x_5, 1, x_101);
lean_ctor_set(x_5, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_5);
x_16 = x_102;
x_17 = x_97;
goto block_21;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_90);
lean_dec(x_69);
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
lean_dec(x_91);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_5);
x_16 = x_104;
x_17 = x_103;
goto block_21;
}
}
else
{
uint8_t x_105; 
lean_dec(x_90);
lean_dec(x_69);
lean_free_object(x_5);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_91);
if (x_105 == 0)
{
return x_91;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_91, 0);
x_107 = lean_ctor_get(x_91, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_91);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; 
x_109 = lean_ctor_get(x_5, 0);
x_110 = lean_ctor_get(x_5, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_5);
x_111 = lean_array_get_size(x_109);
x_112 = lean_nat_dec_lt(x_2, x_111);
lean_dec(x_111);
x_113 = lean_array_get_size(x_110);
x_114 = lean_nat_dec_lt(x_2, x_113);
lean_dec(x_113);
if (x_112 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4;
x_116 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_115);
if (x_114 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_115);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_117);
lean_inc(x_116);
x_118 = l_Lean_Meta_isExprDefEq(x_116, x_117, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_122 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_116, x_117, x_6, x_7, x_8, x_9, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_array_set(x_109, x_2, x_125);
x_128 = lean_array_set(x_110, x_2, x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_16 = x_130;
x_17 = x_124;
goto block_21;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_117);
lean_dec(x_116);
x_131 = lean_ctor_get(x_118, 1);
lean_inc(x_131);
lean_dec(x_118);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_109);
lean_ctor_set(x_132, 1, x_110);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_16 = x_133;
x_17 = x_131;
goto block_21;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_134 = lean_ctor_get(x_118, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_118, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_136 = x_118;
} else {
 lean_dec_ref(x_118);
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
lean_object* x_138; lean_object* x_139; 
x_138 = lean_array_fget(x_110, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_138);
lean_inc(x_116);
x_139 = l_Lean_Meta_isExprDefEq(x_116, x_138, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_143 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_116, x_138, x_6, x_7, x_8, x_9, x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_array_set(x_109, x_2, x_146);
x_149 = lean_array_set(x_110, x_2, x_147);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_16 = x_151;
x_17 = x_145;
goto block_21;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_138);
lean_dec(x_116);
x_152 = lean_ctor_get(x_139, 1);
lean_inc(x_152);
lean_dec(x_139);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_109);
lean_ctor_set(x_153, 1, x_110);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_16 = x_154;
x_17 = x_152;
goto block_21;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_138);
lean_dec(x_116);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_155 = lean_ctor_get(x_139, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_139, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_157 = x_139;
} else {
 lean_dec_ref(x_139);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
lean_object* x_159; 
x_159 = lean_array_fget(x_109, x_2);
if (x_114 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4;
x_161 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_160);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_161);
lean_inc(x_159);
x_162 = l_Lean_Meta_isExprDefEq(x_159, x_161, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_166 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_159, x_161, x_6, x_7, x_8, x_9, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_array_set(x_109, x_2, x_169);
x_172 = lean_array_set(x_110, x_2, x_170);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_16 = x_174;
x_17 = x_168;
goto block_21;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_161);
lean_dec(x_159);
x_175 = lean_ctor_get(x_162, 1);
lean_inc(x_175);
lean_dec(x_162);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_109);
lean_ctor_set(x_176, 1, x_110);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_16 = x_177;
x_17 = x_175;
goto block_21;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_178 = lean_ctor_get(x_162, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_162, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_180 = x_162;
} else {
 lean_dec_ref(x_162);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_array_fget(x_110, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_182);
lean_inc(x_159);
x_183 = l_Lean_Meta_isExprDefEq(x_159, x_182, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_187 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_159, x_182, x_6, x_7, x_8, x_9, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = lean_array_set(x_109, x_2, x_190);
x_193 = lean_array_set(x_110, x_2, x_191);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_16 = x_195;
x_17 = x_189;
goto block_21;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_182);
lean_dec(x_159);
x_196 = lean_ctor_get(x_183, 1);
lean_inc(x_196);
lean_dec(x_183);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_109);
lean_ctor_set(x_197, 1, x_110);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_16 = x_198;
x_17 = x_196;
goto block_21;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_182);
lean_dec(x_159);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_199 = lean_ctor_get(x_183, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_183, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_201 = x_183;
} else {
 lean_dec_ref(x_183);
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
}
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_19;
x_5 = x_18;
x_10 = x_17;
goto _start;
}
}
else
{
lean_object* x_203; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_5);
lean_ctor_set(x_203, 1, x_10);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_5);
lean_ctor_set(x_204, 1, x_10);
return x_204;
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
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_15, x_17);
lean_inc(x_3);
x_19 = lean_mk_array(x_3, x_14);
x_20 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_19, x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
lean_inc(x_18);
x_22 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f(x_7, x_18, x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_25);
x_28 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1(x_25, x_27, x_25, x_16, x_26, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkAppN(x_5, x_31);
x_34 = l_Lean_mkAppN(x_6, x_32);
x_35 = l_Lean_Expr_setAppPPExplicit(x_33);
x_36 = l_Lean_Expr_setAppPPExplicit(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_28, 0, x_37);
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_mkAppN(x_5, x_40);
x_43 = l_Lean_mkAppN(x_6, x_41);
x_44 = l_Lean_Expr_setAppPPExplicit(x_42);
x_45 = l_Lean_Expr_setAppPPExplicit(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_28);
if (x_48 == 0)
{
return x_28;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
lean_dec(x_23);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_22, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
x_58 = l_Lean_mkAppN(x_5, x_56);
x_59 = l_Lean_mkAppN(x_6, x_57);
lean_ctor_set(x_52, 1, x_59);
lean_ctor_set(x_52, 0, x_58);
lean_ctor_set(x_22, 0, x_52);
return x_22;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = l_Lean_mkAppN(x_5, x_60);
x_63 = l_Lean_mkAppN(x_6, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_22, 0, x_64);
return x_22;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_dec(x_22);
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_68 = x_52;
} else {
 lean_dec_ref(x_52);
 x_68 = lean_box(0);
}
x_69 = l_Lean_mkAppN(x_5, x_66);
x_70 = l_Lean_mkAppN(x_6, x_67);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_73 = !lean_is_exclusive(x_22);
if (x_73 == 0)
{
return x_22;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_22, 0);
x_75 = lean_ctor_get(x_22, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_22);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_8, x_7);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_6, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_29; uint8_t x_155; 
lean_dec(x_10);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_6, x_19);
lean_dec(x_6);
x_155 = lean_nat_dec_lt(x_7, x_4);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4;
x_157 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_156);
x_29 = x_157;
goto block_154;
}
else
{
lean_object* x_158; 
x_158 = lean_array_fget(x_1, x_7);
x_29 = x_158;
goto block_154;
}
block_28:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_20;
x_7 = x_26;
x_10 = x_25;
x_15 = x_22;
goto _start;
}
}
block_154:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Expr_fvarId_x21(x_29);
lean_inc(x_11);
x_31 = l_Lean_Meta_getLocalDecl(x_30, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_71; uint8_t x_72; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_71 = l_Lean_LocalDecl_binderInfo(x_32);
lean_dec(x_32);
x_72 = l_Lean_BinderInfo_isExplicit(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_inc(x_5);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_21 = x_73;
x_22 = x_33;
goto block_28;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_array_get_size(x_2);
x_75 = lean_nat_dec_lt(x_7, x_74);
lean_dec(x_74);
x_76 = lean_array_get_size(x_3);
x_77 = lean_nat_dec_lt(x_7, x_76);
lean_dec(x_76);
if (x_75 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4;
x_79 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_78);
if (x_77 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_78);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_80);
lean_inc(x_79);
x_81 = l_Lean_Meta_isExprDefEq(x_79, x_80, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_85 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_79, x_80, x_11, x_12, x_13, x_14, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_89 = lean_ctor_get(x_86, 0);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_2);
x_91 = lean_array_set(x_2, x_7, x_89);
lean_inc(x_3);
x_92 = lean_array_set(x_3, x_7, x_90);
lean_ctor_set(x_86, 1, x_92);
lean_ctor_set(x_86, 0, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_86);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_21 = x_97;
x_22 = x_87;
goto block_28;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_86, 0);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_86);
lean_inc(x_2);
x_100 = lean_array_set(x_2, x_7, x_98);
lean_inc(x_3);
x_101 = lean_array_set(x_3, x_7, x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_21 = x_107;
x_22 = x_87;
goto block_28;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_80);
lean_dec(x_79);
x_108 = lean_ctor_get(x_81, 1);
lean_inc(x_108);
lean_dec(x_81);
lean_inc(x_5);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_5);
x_21 = x_109;
x_22 = x_108;
goto block_28;
}
}
else
{
uint8_t x_110; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_81);
if (x_110 == 0)
{
return x_81;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_81, 0);
x_112 = lean_ctor_get(x_81, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_81);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
x_34 = x_79;
x_35 = lean_box(0);
goto block_70;
}
}
else
{
lean_object* x_114; 
x_114 = lean_array_fget(x_2, x_7);
if (x_77 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4;
x_116 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_115);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_116);
lean_inc(x_114);
x_117 = l_Lean_Meta_isExprDefEq(x_114, x_116, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_121 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_114, x_116, x_11, x_12, x_13, x_14, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_122, 0);
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_2);
x_127 = lean_array_set(x_2, x_7, x_125);
lean_inc(x_3);
x_128 = lean_array_set(x_3, x_7, x_126);
lean_ctor_set(x_122, 1, x_128);
lean_ctor_set(x_122, 0, x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_122);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_21 = x_133;
x_22 = x_123;
goto block_28;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_122, 0);
x_135 = lean_ctor_get(x_122, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_122);
lean_inc(x_2);
x_136 = lean_array_set(x_2, x_7, x_134);
lean_inc(x_3);
x_137 = lean_array_set(x_3, x_7, x_135);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_21 = x_143;
x_22 = x_123;
goto block_28;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_116);
lean_dec(x_114);
x_144 = lean_ctor_get(x_117, 1);
lean_inc(x_144);
lean_dec(x_117);
lean_inc(x_5);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_5);
x_21 = x_145;
x_22 = x_144;
goto block_28;
}
}
else
{
uint8_t x_146; 
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_117);
if (x_146 == 0)
{
return x_117;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_117, 0);
x_148 = lean_ctor_get(x_117, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_117);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
x_34 = x_114;
x_35 = lean_box(0);
goto block_70;
}
}
}
block_70:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_array_fget(x_3, x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_36);
lean_inc(x_34);
x_37 = l_Lean_Meta_isExprDefEq(x_34, x_36, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_41 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_34, x_36, x_11, x_12, x_13, x_14, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_2);
x_47 = lean_array_set(x_2, x_7, x_45);
lean_inc(x_3);
x_48 = lean_array_set(x_3, x_7, x_46);
lean_ctor_set(x_42, 1, x_48);
lean_ctor_set(x_42, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_42);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_21 = x_53;
x_22 = x_43;
goto block_28;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_42, 0);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_42);
lean_inc(x_2);
x_56 = lean_array_set(x_2, x_7, x_54);
lean_inc(x_3);
x_57 = lean_array_set(x_3, x_7, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_21 = x_63;
x_22 = x_43;
goto block_28;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_36);
lean_dec(x_34);
x_64 = lean_ctor_get(x_37, 1);
lean_inc(x_64);
lean_dec(x_37);
lean_inc(x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_5);
x_21 = x_65;
x_22 = x_64;
goto block_28;
}
}
else
{
uint8_t x_66; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_37);
if (x_66 == 0)
{
return x_37;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_37, 0);
x_68 = lean_ctor_get(x_37, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_37);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_31);
if (x_150 == 0)
{
return x_31;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_31, 0);
x_152 = lean_ctor_get(x_31, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_31);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
lean_object* x_159; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_10);
lean_ctor_set(x_159, 1, x_15);
return x_159;
}
}
else
{
lean_object* x_160; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_10);
lean_ctor_set(x_160, 1, x_15);
return x_160;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_14 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___spec__1(x_1, x_2, x_3, x_9, x_11, x_9, x_12, x_9, x_13, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
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
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_addPPExplicitToExposeDiff___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pp", 2);
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
x_1 = lean_mk_string_from_bytes("all", 3);
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
x_1 = lean_mk_string_from_bytes("explicit", 8);
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
x_8 = lean_ctor_get(x_5, 2);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_addPPExplicitToExposeDiff_visit(x_15, x_18, x_3, x_4, x_5, x_6, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("has type", 8);
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
x_1 = lean_mk_string_from_bytes(" : ", 3);
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
x_55 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
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
x_65 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10;
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
x_81 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
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
x_91 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10;
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
x_17 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_indentExpr(x_13);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
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
x_30 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__10;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_26);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
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
x_7 = lean_ctor_get(x_4, 5);
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
x_1 = lean_mk_string_from_bytes("application type mismatch", 25);
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
x_1 = lean_mk_string_from_bytes("\nargument", 9);
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
x_1 = lean_mk_string_from_bytes("\n", 1);
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
x_26 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__12;
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
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_2);
x_13 = l_Lean_mkApp(x_1, x_2);
x_14 = lean_unbox(x_12);
lean_dec(x_12);
x_15 = l_Lean_BinderInfo_isExplicit(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Expr_setAppPPExplicit(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(x_2, x_11, x_16, x_17, x_3, x_4, x_5, x_6, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Meta_throwAppTypeMismatch___rarg___lambda__1(x_2, x_11, x_13, x_19, x_3, x_4, x_5, x_6, x_10);
return x_20;
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
LEAN_EXPORT lean_object* l_Lean_Meta_throwAppTypeMismatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwAppTypeMismatch___rarg), 7, 0);
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
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_21);
return x_22;
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
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
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
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_12);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = l_Lean_mkApp(x_1, x_2);
x_39 = l_Lean_Meta_throwFunctionExpected___rarg(x_38, x_3, x_4, x_5, x_6, x_37);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
return x_8;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_equal(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_equal(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Expr_hash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__7(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_expr_equal(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_expr_equal(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__8(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__4(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__5(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__8(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Expr_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__4(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__5(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__8(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_1);
x_14 = l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__1(x_12, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_free_object(x_10);
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_6);
x_17 = l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(x_15, x_16, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_6, x_19);
lean_dec(x_6);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_2, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_18);
x_25 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_23, x_1, x_18);
x_26 = lean_st_ref_set(x_2, x_25, x_24);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_18);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_35);
x_37 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_35, x_2, x_3, x_4, x_5, x_6, x_13);
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
lean_inc(x_2);
lean_inc(x_36);
x_39 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_36, x_2, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_6);
x_41 = l_Lean_Meta_checkApp(x_35, x_36, x_3, x_4, x_5, x_6, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_get(x_6, x_43);
lean_dec(x_6);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_take(x_2, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_42);
x_49 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_47, x_1, x_42);
x_50 = lean_st_ref_set(x_2, x_49, x_48);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_42);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
return x_41;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_41, 0);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_41);
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
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_39);
if (x_59 == 0)
{
return x_39;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_39, 0);
x_61 = lean_ctor_get(x_39, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_39);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_37);
if (x_63 == 0)
{
return x_37;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_37, 0);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_37);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
case 6:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1), 8, 0);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg(x_1, x_67, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_st_ref_get(x_6, x_70);
lean_dec(x_6);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_take(x_2, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_69);
x_76 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_74, x_1, x_69);
x_77 = lean_st_ref_set(x_2, x_76, x_75);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_69);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_68);
if (x_82 == 0)
{
return x_68;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_68, 0);
x_84 = lean_ctor_get(x_68, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_68);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
case 7:
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1), 8, 0);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__2___rarg(x_1, x_86, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_6, x_89);
lean_dec(x_6);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_take(x_2, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_88);
x_95 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_93, x_1, x_88);
x_96 = lean_st_ref_set(x_2, x_95, x_94);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_dec(x_98);
lean_ctor_set(x_96, 0, x_88);
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_88);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_87);
if (x_101 == 0)
{
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_87, 0);
x_103 = lean_ctor_get(x_87, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_87);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
case 8:
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1), 8, 0);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_106 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg(x_1, x_105, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_st_ref_get(x_6, x_108);
lean_dec(x_6);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_take(x_2, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_107);
x_114 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_112, x_1, x_107);
x_115 = lean_st_ref_set(x_2, x_114, x_113);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_107);
return x_115;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_106);
if (x_120 == 0)
{
return x_106;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_106, 0);
x_122 = lean_ctor_get(x_106, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_106);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
case 10:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_1, 1);
lean_inc(x_124);
lean_inc(x_6);
lean_inc(x_2);
x_125 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_124, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_st_ref_get(x_6, x_127);
lean_dec(x_6);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_2, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_126);
x_133 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_131, x_1, x_126);
x_134 = lean_st_ref_set(x_2, x_133, x_132);
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_134, 0);
lean_dec(x_136);
lean_ctor_set(x_134, 0, x_126);
return x_134;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_126);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_125);
if (x_139 == 0)
{
return x_125;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_125, 0);
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_125);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
case 11:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_1, 2);
lean_inc(x_143);
lean_inc(x_6);
lean_inc(x_2);
x_144 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_143, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_st_ref_get(x_6, x_146);
lean_dec(x_6);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_st_ref_take(x_2, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_145);
x_152 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_150, x_1, x_145);
x_153 = lean_st_ref_set(x_2, x_152, x_151);
lean_dec(x_2);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
lean_dec(x_155);
lean_ctor_set(x_153, 0, x_145);
return x_153;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
uint8_t x_158; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_144);
if (x_158 == 0)
{
return x_144;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_144, 0);
x_160 = lean_ctor_get(x_144, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_144);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
default: 
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = lean_st_ref_get(x_6, x_13);
lean_dec(x_6);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_st_ref_take(x_2, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_box(0);
x_168 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_165, x_1, x_167);
x_169 = lean_st_ref_set(x_2, x_168, x_166);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_169, 0);
lean_dec(x_171);
lean_ctor_set(x_169, 0, x_167);
return x_169;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_14, 0);
lean_inc(x_174);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_174);
return x_10;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_10, 0);
x_176 = lean_ctor_get(x_10, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_10);
lean_inc(x_1);
x_177 = l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__1(x_175, x_1);
if (lean_obj_tag(x_177) == 0)
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_1, 1);
lean_inc(x_179);
lean_inc(x_6);
x_180 = l___private_Lean_Meta_Check_0__Lean_Meta_checkConstant(x_178, x_179, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_st_ref_get(x_6, x_182);
lean_dec(x_6);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_st_ref_take(x_2, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_181);
x_188 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_186, x_1, x_181);
x_189 = lean_st_ref_set(x_2, x_188, x_187);
lean_dec(x_2);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_181);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_180, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_180, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_195 = x_180;
} else {
 lean_dec_ref(x_180);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
case 5:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_1, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_1, 1);
lean_inc(x_198);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_197);
x_199 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_197, x_2, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_198);
x_201 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_198, x_2, x_3, x_4, x_5, x_6, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
lean_inc(x_6);
x_203 = l_Lean_Meta_checkApp(x_197, x_198, x_3, x_4, x_5, x_6, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_st_ref_get(x_6, x_205);
lean_dec(x_6);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_st_ref_take(x_2, x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_204);
x_211 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_209, x_1, x_204);
x_212 = lean_st_ref_set(x_2, x_211, x_210);
lean_dec(x_2);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_204);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_216 = lean_ctor_get(x_203, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_203, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_218 = x_203;
} else {
 lean_dec_ref(x_203);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_201, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_201, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_222 = x_201;
} else {
 lean_dec_ref(x_201);
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
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = lean_ctor_get(x_199, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_199, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_226 = x_199;
} else {
 lean_dec_ref(x_199);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
case 6:
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1), 8, 0);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_229 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg(x_1, x_228, x_2, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_st_ref_get(x_6, x_231);
lean_dec(x_6);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_st_ref_take(x_2, x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
lean_inc(x_230);
x_237 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_235, x_1, x_230);
x_238 = lean_st_ref_set(x_2, x_237, x_236);
lean_dec(x_2);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_230);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_242 = lean_ctor_get(x_229, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_229, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_244 = x_229;
} else {
 lean_dec_ref(x_229);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
case 7:
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1), 8, 0);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_247 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__2___rarg(x_1, x_246, x_2, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_st_ref_get(x_6, x_249);
lean_dec(x_6);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_st_ref_take(x_2, x_251);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
lean_inc(x_248);
x_255 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_253, x_1, x_248);
x_256 = lean_st_ref_set(x_2, x_255, x_254);
lean_dec(x_2);
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
lean_ctor_set(x_259, 0, x_248);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_260 = lean_ctor_get(x_247, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_247, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_262 = x_247;
} else {
 lean_dec_ref(x_247);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
case 8:
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1), 8, 0);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_265 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg(x_1, x_264, x_2, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_st_ref_get(x_6, x_267);
lean_dec(x_6);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_270 = lean_st_ref_take(x_2, x_269);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
lean_inc(x_266);
x_273 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_271, x_1, x_266);
x_274 = lean_st_ref_set(x_2, x_273, x_272);
lean_dec(x_2);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_266);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_278 = lean_ctor_get(x_265, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_265, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_280 = x_265;
} else {
 lean_dec_ref(x_265);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
case 10:
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_1, 1);
lean_inc(x_282);
lean_inc(x_6);
lean_inc(x_2);
x_283 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_282, x_2, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_st_ref_get(x_6, x_285);
lean_dec(x_6);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
x_288 = lean_st_ref_take(x_2, x_287);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
lean_inc(x_284);
x_291 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_289, x_1, x_284);
x_292 = lean_st_ref_set(x_2, x_291, x_290);
lean_dec(x_2);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_294 = x_292;
} else {
 lean_dec_ref(x_292);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_284);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_296 = lean_ctor_get(x_283, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_283, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_298 = x_283;
} else {
 lean_dec_ref(x_283);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
case 11:
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_1, 2);
lean_inc(x_300);
lean_inc(x_6);
lean_inc(x_2);
x_301 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_300, x_2, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_st_ref_get(x_6, x_303);
lean_dec(x_6);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_306 = lean_st_ref_take(x_2, x_305);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
lean_inc(x_302);
x_309 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_307, x_1, x_302);
x_310 = lean_st_ref_set(x_2, x_309, x_308);
lean_dec(x_2);
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
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_302);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_314 = lean_ctor_get(x_301, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_301, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_316 = x_301;
} else {
 lean_dec_ref(x_301);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
default: 
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_318 = lean_st_ref_get(x_6, x_176);
lean_dec(x_6);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_st_ref_take(x_2, x_319);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_box(0);
x_324 = l_Std_HashMap_insert___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__3(x_321, x_1, x_323);
x_325 = lean_st_ref_set(x_2, x_324, x_322);
lean_dec(x_2);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_323);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
}
else
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_329 = lean_ctor_get(x_177, 0);
lean_inc(x_329);
lean_dec(x_177);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_176);
return x_330;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
lean_inc(x_12);
x_19 = l_Lean_Meta_getFVarLocalDecl(x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 3);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_22);
x_23 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_22, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_22, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_13 = x_26;
x_14 = x_27;
goto block_18;
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
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
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 4);
lean_inc(x_38);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_37);
x_39 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_37, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_37);
x_41 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_37, x_5, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_38);
x_43 = lean_infer_type(x_38, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Meta_isExprDefEq(x_37, x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_Expr_fvarId_x21(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg(x_50, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_38, x_5, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_13 = x_54;
x_14 = x_55;
goto block_18;
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
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
lean_dec(x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
return x_51;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
x_64 = lean_ctor_get(x_46, 1);
lean_inc(x_64);
lean_dec(x_46);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_65 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_38, x_5, x_6, x_7, x_8, x_9, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_13 = x_66;
x_14 = x_67;
goto block_18;
}
else
{
uint8_t x_68; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
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
lean_dec(x_38);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = !lean_is_exclusive(x_46);
if (x_72 == 0)
{
return x_46;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
x_74 = lean_ctor_get(x_46, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_46);
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
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_43);
if (x_76 == 0)
{
return x_43;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_43, 0);
x_78 = lean_ctor_get(x_43, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_43);
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
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_41);
if (x_80 == 0)
{
return x_41;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_41, 0);
x_82 = lean_ctor_get(x_41, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_41);
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
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_39);
if (x_84 == 0)
{
return x_39;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_39, 0);
x_86 = lean_ctor_get(x_39, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_39);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_88 = !lean_is_exclusive(x_19);
if (x_88 == 0)
{
return x_19;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_19, 0);
x_90 = lean_ctor_get(x_19, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_19);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_10 = x_14;
goto _start;
}
}
else
{
lean_object* x_92; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_4);
lean_ctor_set(x_92, 1, x_10);
return x_92;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_3, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = 1;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_17 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1(x_1, x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___lambda__1), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___closed__1;
x_9 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
x_13 = l_Lean_Meta_getFVarLocalDecl(x_12, x_6, x_7, x_8, x_9, x_10);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_17 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_16, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_16, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_2 = x_23;
x_4 = x_20;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_10);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__2___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_box(0);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_11, x_10, x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_12 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_9, x_9);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_29 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1(x_1, x_27, x_28, x_29, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_32 = l___private_Lean_Meta_Check_0__Lean_Meta_ensureType(x_2, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
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
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_30);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___lambda__1), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___closed__1;
x_9 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkLambdaLet___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux_checkForall___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_mkHashMapImp___rarg(x_7);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_mk_ref(x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_12);
x_14 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux_check(x_1, x_12, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_5, x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_12, x_18);
lean_dec(x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at___private_Lean_Meta_Check_0__Lean_Meta_checkAux___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_check___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
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
x_1 = lean_mk_string_from_bytes("check", 5);
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
uint8_t x_7; lean_object* x_8; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_444 = lean_st_ref_get(x_5, x_6);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_445, 3);
lean_inc(x_446);
lean_dec(x_445);
x_447 = lean_ctor_get_uint8(x_446, sizeof(void*)*1);
lean_dec(x_446);
if (x_447 == 0)
{
lean_object* x_448; uint8_t x_449; 
x_448 = lean_ctor_get(x_444, 1);
lean_inc(x_448);
lean_dec(x_444);
x_449 = 0;
x_7 = x_449;
x_8 = x_448;
goto block_443;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_450 = lean_ctor_get(x_444, 1);
lean_inc(x_450);
lean_dec(x_444);
x_451 = l_Lean_Meta_check___closed__4;
x_452 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_451, x_2, x_3, x_4, x_5, x_450);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_unbox(x_453);
lean_dec(x_453);
x_7 = x_455;
x_8 = x_454;
goto block_443;
}
block_443:
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
x_54 = lean_ctor_get(x_35, 2);
x_55 = lean_ctor_get(x_35, 4);
x_56 = lean_ctor_get(x_35, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_57 = lean_ctor_get(x_36, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_58 = x_36;
} else {
 lean_dec_ref(x_36);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 1, 1);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_13);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_55);
lean_ctor_set(x_60, 5, x_56);
x_61 = lean_st_ref_set(x_5, x_60, x_37);
lean_dec(x_5);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_30);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_ctor_get(x_29, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_29, 1);
lean_inc(x_66);
lean_dec(x_29);
x_67 = lean_st_ref_get(x_5, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_5, x_68);
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
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_13);
x_76 = lean_st_ref_set(x_5, x_70, x_72);
lean_dec(x_5);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_65);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_65);
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
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_13);
lean_ctor_set(x_70, 3, x_82);
x_83 = lean_st_ref_set(x_5, x_70, x_72);
lean_dec(x_5);
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
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
 lean_ctor_set_tag(x_86, 1);
}
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_87 = lean_ctor_get(x_70, 0);
x_88 = lean_ctor_get(x_70, 1);
x_89 = lean_ctor_get(x_70, 2);
x_90 = lean_ctor_get(x_70, 4);
x_91 = lean_ctor_get(x_70, 5);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_70);
x_92 = lean_ctor_get(x_71, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_93 = x_71;
} else {
 lean_dec_ref(x_71);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 1, 1);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_13);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_87);
lean_ctor_set(x_95, 1, x_88);
lean_ctor_set(x_95, 2, x_89);
lean_ctor_set(x_95, 3, x_94);
lean_ctor_set(x_95, 4, x_90);
lean_ctor_set(x_95, 5, x_91);
x_96 = lean_st_ref_set(x_5, x_95, x_72);
lean_dec(x_5);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_65);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_100 = lean_ctor_get_uint8(x_23, 0);
x_101 = lean_ctor_get_uint8(x_23, 1);
x_102 = lean_ctor_get_uint8(x_23, 2);
x_103 = lean_ctor_get_uint8(x_23, 3);
x_104 = lean_ctor_get_uint8(x_23, 4);
x_105 = lean_ctor_get_uint8(x_23, 6);
x_106 = lean_ctor_get_uint8(x_23, 7);
x_107 = lean_ctor_get_uint8(x_23, 8);
x_108 = lean_ctor_get_uint8(x_23, 9);
x_109 = lean_ctor_get_uint8(x_23, 10);
x_110 = lean_ctor_get_uint8(x_23, 11);
x_111 = lean_ctor_get_uint8(x_23, 12);
x_112 = lean_ctor_get_uint8(x_23, 13);
lean_dec(x_23);
x_113 = 0;
x_114 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_114, 0, x_100);
lean_ctor_set_uint8(x_114, 1, x_101);
lean_ctor_set_uint8(x_114, 2, x_102);
lean_ctor_set_uint8(x_114, 3, x_103);
lean_ctor_set_uint8(x_114, 4, x_104);
lean_ctor_set_uint8(x_114, 5, x_113);
lean_ctor_set_uint8(x_114, 6, x_105);
lean_ctor_set_uint8(x_114, 7, x_106);
lean_ctor_set_uint8(x_114, 8, x_107);
lean_ctor_set_uint8(x_114, 9, x_108);
lean_ctor_set_uint8(x_114, 10, x_109);
lean_ctor_set_uint8(x_114, 11, x_110);
lean_ctor_set_uint8(x_114, 12, x_111);
lean_ctor_set_uint8(x_114, 13, x_112);
lean_ctor_set(x_2, 0, x_114);
lean_inc(x_5);
x_115 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
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
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_121, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_121, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 5);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 lean_ctor_release(x_121, 5);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_122, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_131 = x_122;
} else {
 lean_dec_ref(x_122);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 1, 1);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_129)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_129;
}
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set(x_133, 4, x_127);
lean_ctor_set(x_133, 5, x_128);
x_134 = lean_st_ref_set(x_5, x_133, x_123);
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
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_116);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_138 = lean_ctor_get(x_115, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_115, 1);
lean_inc(x_139);
lean_dec(x_115);
x_140 = lean_st_ref_get(x_5, x_139);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_take(x_5, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 2);
lean_inc(x_148);
x_149 = lean_ctor_get(x_143, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_143, 5);
lean_inc(x_150);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 lean_ctor_release(x_143, 5);
 x_151 = x_143;
} else {
 lean_dec_ref(x_143);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_144, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_153 = x_144;
} else {
 lean_dec_ref(x_144);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 1, 1);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_151)) {
 x_155 = lean_alloc_ctor(0, 6, 0);
} else {
 x_155 = x_151;
}
lean_ctor_set(x_155, 0, x_146);
lean_ctor_set(x_155, 1, x_147);
lean_ctor_set(x_155, 2, x_148);
lean_ctor_set(x_155, 3, x_154);
lean_ctor_set(x_155, 4, x_149);
lean_ctor_set(x_155, 5, x_150);
x_156 = lean_st_ref_set(x_5, x_155, x_145);
lean_dec(x_5);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_138);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_160 = lean_ctor_get(x_2, 1);
x_161 = lean_ctor_get(x_2, 2);
x_162 = lean_ctor_get(x_2, 3);
x_163 = lean_ctor_get(x_2, 4);
x_164 = lean_ctor_get(x_2, 5);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_2);
x_165 = lean_ctor_get_uint8(x_23, 0);
x_166 = lean_ctor_get_uint8(x_23, 1);
x_167 = lean_ctor_get_uint8(x_23, 2);
x_168 = lean_ctor_get_uint8(x_23, 3);
x_169 = lean_ctor_get_uint8(x_23, 4);
x_170 = lean_ctor_get_uint8(x_23, 6);
x_171 = lean_ctor_get_uint8(x_23, 7);
x_172 = lean_ctor_get_uint8(x_23, 8);
x_173 = lean_ctor_get_uint8(x_23, 9);
x_174 = lean_ctor_get_uint8(x_23, 10);
x_175 = lean_ctor_get_uint8(x_23, 11);
x_176 = lean_ctor_get_uint8(x_23, 12);
x_177 = lean_ctor_get_uint8(x_23, 13);
if (lean_is_exclusive(x_23)) {
 x_178 = x_23;
} else {
 lean_dec_ref(x_23);
 x_178 = lean_box(0);
}
x_179 = 0;
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 0, 14);
} else {
 x_180 = x_178;
}
lean_ctor_set_uint8(x_180, 0, x_165);
lean_ctor_set_uint8(x_180, 1, x_166);
lean_ctor_set_uint8(x_180, 2, x_167);
lean_ctor_set_uint8(x_180, 3, x_168);
lean_ctor_set_uint8(x_180, 4, x_169);
lean_ctor_set_uint8(x_180, 5, x_179);
lean_ctor_set_uint8(x_180, 6, x_170);
lean_ctor_set_uint8(x_180, 7, x_171);
lean_ctor_set_uint8(x_180, 8, x_172);
lean_ctor_set_uint8(x_180, 9, x_173);
lean_ctor_set_uint8(x_180, 10, x_174);
lean_ctor_set_uint8(x_180, 11, x_175);
lean_ctor_set_uint8(x_180, 12, x_176);
lean_ctor_set_uint8(x_180, 13, x_177);
x_181 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_160);
lean_ctor_set(x_181, 2, x_161);
lean_ctor_set(x_181, 3, x_162);
lean_ctor_set(x_181, 4, x_163);
lean_ctor_set(x_181, 5, x_164);
lean_inc(x_5);
x_182 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_181, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_st_ref_get(x_5, x_184);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_st_ref_take(x_5, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_189, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_198 = x_189;
} else {
 lean_dec_ref(x_189);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 1, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_196)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_196;
}
lean_ctor_set(x_200, 0, x_191);
lean_ctor_set(x_200, 1, x_192);
lean_ctor_set(x_200, 2, x_193);
lean_ctor_set(x_200, 3, x_199);
lean_ctor_set(x_200, 4, x_194);
lean_ctor_set(x_200, 5, x_195);
x_201 = lean_st_ref_set(x_5, x_200, x_190);
lean_dec(x_5);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_183);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_205 = lean_ctor_get(x_182, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_182, 1);
lean_inc(x_206);
lean_dec(x_182);
x_207 = lean_st_ref_get(x_5, x_206);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_st_ref_take(x_5, x_208);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_210, 3);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_210, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_210, 4);
lean_inc(x_216);
x_217 = lean_ctor_get(x_210, 5);
lean_inc(x_217);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 lean_ctor_release(x_210, 4);
 lean_ctor_release(x_210, 5);
 x_218 = x_210;
} else {
 lean_dec_ref(x_210);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_211, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_220 = x_211;
} else {
 lean_dec_ref(x_211);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 1, 1);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set_uint8(x_221, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_218)) {
 x_222 = lean_alloc_ctor(0, 6, 0);
} else {
 x_222 = x_218;
}
lean_ctor_set(x_222, 0, x_213);
lean_ctor_set(x_222, 1, x_214);
lean_ctor_set(x_222, 2, x_215);
lean_ctor_set(x_222, 3, x_221);
lean_ctor_set(x_222, 4, x_216);
lean_ctor_set(x_222, 5, x_217);
x_223 = lean_st_ref_set(x_5, x_222, x_212);
lean_dec(x_5);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
 lean_ctor_set_tag(x_226, 1);
}
lean_ctor_set(x_226, 0, x_205);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
else
{
lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_227 = lean_ctor_get(x_16, 0);
lean_inc(x_227);
lean_dec(x_16);
x_228 = 0;
x_229 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*1, x_228);
lean_ctor_set(x_15, 3, x_229);
x_230 = lean_st_ref_set(x_5, x_15, x_17);
x_231 = lean_ctor_get(x_2, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_2, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_2, 2);
lean_inc(x_234);
x_235 = lean_ctor_get(x_2, 3);
lean_inc(x_235);
x_236 = lean_ctor_get(x_2, 4);
lean_inc(x_236);
x_237 = lean_ctor_get(x_2, 5);
lean_inc(x_237);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_238 = x_2;
} else {
 lean_dec_ref(x_2);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get_uint8(x_231, 0);
x_240 = lean_ctor_get_uint8(x_231, 1);
x_241 = lean_ctor_get_uint8(x_231, 2);
x_242 = lean_ctor_get_uint8(x_231, 3);
x_243 = lean_ctor_get_uint8(x_231, 4);
x_244 = lean_ctor_get_uint8(x_231, 6);
x_245 = lean_ctor_get_uint8(x_231, 7);
x_246 = lean_ctor_get_uint8(x_231, 8);
x_247 = lean_ctor_get_uint8(x_231, 9);
x_248 = lean_ctor_get_uint8(x_231, 10);
x_249 = lean_ctor_get_uint8(x_231, 11);
x_250 = lean_ctor_get_uint8(x_231, 12);
x_251 = lean_ctor_get_uint8(x_231, 13);
if (lean_is_exclusive(x_231)) {
 x_252 = x_231;
} else {
 lean_dec_ref(x_231);
 x_252 = lean_box(0);
}
x_253 = 0;
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 0, 14);
} else {
 x_254 = x_252;
}
lean_ctor_set_uint8(x_254, 0, x_239);
lean_ctor_set_uint8(x_254, 1, x_240);
lean_ctor_set_uint8(x_254, 2, x_241);
lean_ctor_set_uint8(x_254, 3, x_242);
lean_ctor_set_uint8(x_254, 4, x_243);
lean_ctor_set_uint8(x_254, 5, x_253);
lean_ctor_set_uint8(x_254, 6, x_244);
lean_ctor_set_uint8(x_254, 7, x_245);
lean_ctor_set_uint8(x_254, 8, x_246);
lean_ctor_set_uint8(x_254, 9, x_247);
lean_ctor_set_uint8(x_254, 10, x_248);
lean_ctor_set_uint8(x_254, 11, x_249);
lean_ctor_set_uint8(x_254, 12, x_250);
lean_ctor_set_uint8(x_254, 13, x_251);
if (lean_is_scalar(x_238)) {
 x_255 = lean_alloc_ctor(0, 6, 0);
} else {
 x_255 = x_238;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_233);
lean_ctor_set(x_255, 2, x_234);
lean_ctor_set(x_255, 3, x_235);
lean_ctor_set(x_255, 4, x_236);
lean_ctor_set(x_255, 5, x_237);
lean_inc(x_5);
x_256 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_255, x_3, x_4, x_5, x_232);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_st_ref_get(x_5, x_258);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_261 = lean_st_ref_take(x_5, x_260);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_262, 3);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_262, 2);
lean_inc(x_267);
x_268 = lean_ctor_get(x_262, 4);
lean_inc(x_268);
x_269 = lean_ctor_get(x_262, 5);
lean_inc(x_269);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 lean_ctor_release(x_262, 3);
 lean_ctor_release(x_262, 4);
 lean_ctor_release(x_262, 5);
 x_270 = x_262;
} else {
 lean_dec_ref(x_262);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_263, 0);
lean_inc(x_271);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_272 = x_263;
} else {
 lean_dec_ref(x_263);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(0, 1, 1);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_270)) {
 x_274 = lean_alloc_ctor(0, 6, 0);
} else {
 x_274 = x_270;
}
lean_ctor_set(x_274, 0, x_265);
lean_ctor_set(x_274, 1, x_266);
lean_ctor_set(x_274, 2, x_267);
lean_ctor_set(x_274, 3, x_273);
lean_ctor_set(x_274, 4, x_268);
lean_ctor_set(x_274, 5, x_269);
x_275 = lean_st_ref_set(x_5, x_274, x_264);
lean_dec(x_5);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_277 = x_275;
} else {
 lean_dec_ref(x_275);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_257);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_279 = lean_ctor_get(x_256, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_256, 1);
lean_inc(x_280);
lean_dec(x_256);
x_281 = lean_st_ref_get(x_5, x_280);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
x_283 = lean_st_ref_take(x_5, x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_284, 3);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_ctor_get(x_284, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_284, 1);
lean_inc(x_288);
x_289 = lean_ctor_get(x_284, 2);
lean_inc(x_289);
x_290 = lean_ctor_get(x_284, 4);
lean_inc(x_290);
x_291 = lean_ctor_get(x_284, 5);
lean_inc(x_291);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 lean_ctor_release(x_284, 2);
 lean_ctor_release(x_284, 3);
 lean_ctor_release(x_284, 4);
 lean_ctor_release(x_284, 5);
 x_292 = x_284;
} else {
 lean_dec_ref(x_284);
 x_292 = lean_box(0);
}
x_293 = lean_ctor_get(x_285, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_294 = x_285;
} else {
 lean_dec_ref(x_285);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(0, 1, 1);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set_uint8(x_295, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_292)) {
 x_296 = lean_alloc_ctor(0, 6, 0);
} else {
 x_296 = x_292;
}
lean_ctor_set(x_296, 0, x_287);
lean_ctor_set(x_296, 1, x_288);
lean_ctor_set(x_296, 2, x_289);
lean_ctor_set(x_296, 3, x_295);
lean_ctor_set(x_296, 4, x_290);
lean_ctor_set(x_296, 5, x_291);
x_297 = lean_st_ref_set(x_5, x_296, x_286);
lean_dec(x_5);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
 lean_ctor_set_tag(x_300, 1);
}
lean_ctor_set(x_300, 0, x_279);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; uint8_t x_321; uint8_t x_322; uint8_t x_323; uint8_t x_324; uint8_t x_325; uint8_t x_326; uint8_t x_327; uint8_t x_328; uint8_t x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_301 = lean_ctor_get(x_15, 0);
x_302 = lean_ctor_get(x_15, 1);
x_303 = lean_ctor_get(x_15, 2);
x_304 = lean_ctor_get(x_15, 4);
x_305 = lean_ctor_get(x_15, 5);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_15);
x_306 = lean_ctor_get(x_16, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_307 = x_16;
} else {
 lean_dec_ref(x_16);
 x_307 = lean_box(0);
}
x_308 = 0;
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 1, 1);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set_uint8(x_309, sizeof(void*)*1, x_308);
x_310 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_310, 0, x_301);
lean_ctor_set(x_310, 1, x_302);
lean_ctor_set(x_310, 2, x_303);
lean_ctor_set(x_310, 3, x_309);
lean_ctor_set(x_310, 4, x_304);
lean_ctor_set(x_310, 5, x_305);
x_311 = lean_st_ref_set(x_5, x_310, x_17);
x_312 = lean_ctor_get(x_2, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_ctor_get(x_2, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_2, 2);
lean_inc(x_315);
x_316 = lean_ctor_get(x_2, 3);
lean_inc(x_316);
x_317 = lean_ctor_get(x_2, 4);
lean_inc(x_317);
x_318 = lean_ctor_get(x_2, 5);
lean_inc(x_318);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_319 = x_2;
} else {
 lean_dec_ref(x_2);
 x_319 = lean_box(0);
}
x_320 = lean_ctor_get_uint8(x_312, 0);
x_321 = lean_ctor_get_uint8(x_312, 1);
x_322 = lean_ctor_get_uint8(x_312, 2);
x_323 = lean_ctor_get_uint8(x_312, 3);
x_324 = lean_ctor_get_uint8(x_312, 4);
x_325 = lean_ctor_get_uint8(x_312, 6);
x_326 = lean_ctor_get_uint8(x_312, 7);
x_327 = lean_ctor_get_uint8(x_312, 8);
x_328 = lean_ctor_get_uint8(x_312, 9);
x_329 = lean_ctor_get_uint8(x_312, 10);
x_330 = lean_ctor_get_uint8(x_312, 11);
x_331 = lean_ctor_get_uint8(x_312, 12);
x_332 = lean_ctor_get_uint8(x_312, 13);
if (lean_is_exclusive(x_312)) {
 x_333 = x_312;
} else {
 lean_dec_ref(x_312);
 x_333 = lean_box(0);
}
x_334 = 0;
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 0, 14);
} else {
 x_335 = x_333;
}
lean_ctor_set_uint8(x_335, 0, x_320);
lean_ctor_set_uint8(x_335, 1, x_321);
lean_ctor_set_uint8(x_335, 2, x_322);
lean_ctor_set_uint8(x_335, 3, x_323);
lean_ctor_set_uint8(x_335, 4, x_324);
lean_ctor_set_uint8(x_335, 5, x_334);
lean_ctor_set_uint8(x_335, 6, x_325);
lean_ctor_set_uint8(x_335, 7, x_326);
lean_ctor_set_uint8(x_335, 8, x_327);
lean_ctor_set_uint8(x_335, 9, x_328);
lean_ctor_set_uint8(x_335, 10, x_329);
lean_ctor_set_uint8(x_335, 11, x_330);
lean_ctor_set_uint8(x_335, 12, x_331);
lean_ctor_set_uint8(x_335, 13, x_332);
if (lean_is_scalar(x_319)) {
 x_336 = lean_alloc_ctor(0, 6, 0);
} else {
 x_336 = x_319;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_314);
lean_ctor_set(x_336, 2, x_315);
lean_ctor_set(x_336, 3, x_316);
lean_ctor_set(x_336, 4, x_317);
lean_ctor_set(x_336, 5, x_318);
lean_inc(x_5);
x_337 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_336, x_3, x_4, x_5, x_313);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_st_ref_get(x_5, x_339);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
x_342 = lean_st_ref_take(x_5, x_341);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_343, 3);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 1);
lean_inc(x_345);
lean_dec(x_342);
x_346 = lean_ctor_get(x_343, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_343, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_343, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_343, 4);
lean_inc(x_349);
x_350 = lean_ctor_get(x_343, 5);
lean_inc(x_350);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 lean_ctor_release(x_343, 4);
 lean_ctor_release(x_343, 5);
 x_351 = x_343;
} else {
 lean_dec_ref(x_343);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_344, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_353 = x_344;
} else {
 lean_dec_ref(x_344);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(0, 1, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set_uint8(x_354, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_351)) {
 x_355 = lean_alloc_ctor(0, 6, 0);
} else {
 x_355 = x_351;
}
lean_ctor_set(x_355, 0, x_346);
lean_ctor_set(x_355, 1, x_347);
lean_ctor_set(x_355, 2, x_348);
lean_ctor_set(x_355, 3, x_354);
lean_ctor_set(x_355, 4, x_349);
lean_ctor_set(x_355, 5, x_350);
x_356 = lean_st_ref_set(x_5, x_355, x_345);
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
lean_ctor_set(x_359, 0, x_338);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_360 = lean_ctor_get(x_337, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_337, 1);
lean_inc(x_361);
lean_dec(x_337);
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
x_371 = lean_ctor_get(x_365, 4);
lean_inc(x_371);
x_372 = lean_ctor_get(x_365, 5);
lean_inc(x_372);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 lean_ctor_release(x_365, 4);
 lean_ctor_release(x_365, 5);
 x_373 = x_365;
} else {
 lean_dec_ref(x_365);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_366, 0);
lean_inc(x_374);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_375 = x_366;
} else {
 lean_dec_ref(x_366);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(0, 1, 1);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_373)) {
 x_377 = lean_alloc_ctor(0, 6, 0);
} else {
 x_377 = x_373;
}
lean_ctor_set(x_377, 0, x_368);
lean_ctor_set(x_377, 1, x_369);
lean_ctor_set(x_377, 2, x_370);
lean_ctor_set(x_377, 3, x_376);
lean_ctor_set(x_377, 4, x_371);
lean_ctor_set(x_377, 5, x_372);
x_378 = lean_st_ref_set(x_5, x_377, x_367);
lean_dec(x_5);
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_380 = x_378;
} else {
 lean_dec_ref(x_378);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
 lean_ctor_set_tag(x_381, 1);
}
lean_ctor_set(x_381, 0, x_360);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_382 = lean_ctor_get(x_4, 5);
lean_inc(x_382);
x_383 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(x_5, x_8);
x_384 = lean_ctor_get(x_2, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
lean_dec(x_383);
x_387 = lean_ctor_get(x_2, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_2, 2);
lean_inc(x_388);
x_389 = lean_ctor_get(x_2, 3);
lean_inc(x_389);
x_390 = lean_ctor_get(x_2, 4);
lean_inc(x_390);
x_391 = lean_ctor_get(x_2, 5);
lean_inc(x_391);
x_392 = !lean_is_exclusive(x_384);
if (x_392 == 0)
{
uint8_t x_393; lean_object* x_394; lean_object* x_395; 
x_393 = 0;
lean_ctor_set_uint8(x_384, 5, x_393);
x_394 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_394, 0, x_384);
lean_ctor_set(x_394, 1, x_387);
lean_ctor_set(x_394, 2, x_388);
lean_ctor_set(x_394, 3, x_389);
lean_ctor_set(x_394, 4, x_390);
lean_ctor_set(x_394, 5, x_391);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_395 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_394, x_3, x_4, x_5, x_386);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = l_Lean_Meta_check___closed__4;
x_399 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_385, x_398, x_382, x_2, x_3, x_4, x_5, x_397);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_400 = !lean_is_exclusive(x_399);
if (x_400 == 0)
{
lean_object* x_401; 
x_401 = lean_ctor_get(x_399, 0);
lean_dec(x_401);
lean_ctor_set(x_399, 0, x_396);
return x_399;
}
else
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
lean_dec(x_399);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_396);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_404 = lean_ctor_get(x_395, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_395, 1);
lean_inc(x_405);
lean_dec(x_395);
x_406 = l_Lean_Meta_check___closed__4;
x_407 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_385, x_406, x_382, x_2, x_3, x_4, x_5, x_405);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_408 = !lean_is_exclusive(x_407);
if (x_408 == 0)
{
lean_object* x_409; 
x_409 = lean_ctor_get(x_407, 0);
lean_dec(x_409);
lean_ctor_set_tag(x_407, 1);
lean_ctor_set(x_407, 0, x_404);
return x_407;
}
else
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec(x_407);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_404);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
else
{
uint8_t x_412; uint8_t x_413; uint8_t x_414; uint8_t x_415; uint8_t x_416; uint8_t x_417; uint8_t x_418; uint8_t x_419; uint8_t x_420; uint8_t x_421; uint8_t x_422; uint8_t x_423; uint8_t x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_412 = lean_ctor_get_uint8(x_384, 0);
x_413 = lean_ctor_get_uint8(x_384, 1);
x_414 = lean_ctor_get_uint8(x_384, 2);
x_415 = lean_ctor_get_uint8(x_384, 3);
x_416 = lean_ctor_get_uint8(x_384, 4);
x_417 = lean_ctor_get_uint8(x_384, 6);
x_418 = lean_ctor_get_uint8(x_384, 7);
x_419 = lean_ctor_get_uint8(x_384, 8);
x_420 = lean_ctor_get_uint8(x_384, 9);
x_421 = lean_ctor_get_uint8(x_384, 10);
x_422 = lean_ctor_get_uint8(x_384, 11);
x_423 = lean_ctor_get_uint8(x_384, 12);
x_424 = lean_ctor_get_uint8(x_384, 13);
lean_dec(x_384);
x_425 = 0;
x_426 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_426, 0, x_412);
lean_ctor_set_uint8(x_426, 1, x_413);
lean_ctor_set_uint8(x_426, 2, x_414);
lean_ctor_set_uint8(x_426, 3, x_415);
lean_ctor_set_uint8(x_426, 4, x_416);
lean_ctor_set_uint8(x_426, 5, x_425);
lean_ctor_set_uint8(x_426, 6, x_417);
lean_ctor_set_uint8(x_426, 7, x_418);
lean_ctor_set_uint8(x_426, 8, x_419);
lean_ctor_set_uint8(x_426, 9, x_420);
lean_ctor_set_uint8(x_426, 10, x_421);
lean_ctor_set_uint8(x_426, 11, x_422);
lean_ctor_set_uint8(x_426, 12, x_423);
lean_ctor_set_uint8(x_426, 13, x_424);
x_427 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_387);
lean_ctor_set(x_427, 2, x_388);
lean_ctor_set(x_427, 3, x_389);
lean_ctor_set(x_427, 4, x_390);
lean_ctor_set(x_427, 5, x_391);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_428 = l___private_Lean_Meta_Check_0__Lean_Meta_checkAux(x_1, x_427, x_3, x_4, x_5, x_386);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = l_Lean_Meta_check___closed__4;
x_432 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_385, x_431, x_382, x_2, x_3, x_4, x_5, x_430);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_434 = x_432;
} else {
 lean_dec_ref(x_432);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_429);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_436 = lean_ctor_get(x_428, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_428, 1);
lean_inc(x_437);
lean_dec(x_428);
x_438 = l_Lean_Meta_check___closed__4;
x_439 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_385, x_438, x_382, x_2, x_3, x_4, x_5, x_437);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_441 = x_439;
} else {
 lean_dec_ref(x_439);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
 lean_ctor_set_tag(x_442, 1);
}
lean_ctor_set(x_442, 0, x_436);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_isTypeCorrect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeError", 9);
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
static lean_object* _init_l_Lean_Meta_isTypeCorrect___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeCorrect___lambda__1___boxed), 6, 0);
return x_1;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = l_Lean_Meta_isTypeCorrect___closed__2;
x_19 = lean_st_ref_get(x_5, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Meta_isTypeCorrect___closed__3;
x_25 = lean_box(0);
x_26 = lean_apply_6(x_24, x_25, x_2, x_3, x_4, x_5, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_18, x_2, x_3, x_4, x_5, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_isTypeCorrect___closed__3;
x_32 = lean_unbox(x_29);
lean_dec(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
x_33 = lean_box(0);
x_34 = lean_apply_6(x_31, x_33, x_2, x_3, x_4, x_5, x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = l_Lean_Exception_toMessageData(x_16);
x_36 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_18, x_35, x_2, x_3, x_4, x_5, x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_apply_6(x_31, x_37, x_2, x_3, x_4, x_5, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeCorrect___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isTypeCorrect___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_2604_(lean_object* x_1) {
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___closed__1 = _init_l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1___rarg___closed__1);
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
l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__2);
l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__3);
l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__1___closed__4);
l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1 = _init_l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff_visit___lambda__1___closed__1);
l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___closed__1 = _init_l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_addPPExplicitToExposeDiff_hasExplicitDiff_x3f___closed__1);
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
l_Lean_Meta_isTypeCorrect___closed__3 = _init_l_Lean_Meta_isTypeCorrect___closed__3();
lean_mark_persistent(l_Lean_Meta_isTypeCorrect___closed__3);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Check___hyg_2604_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
