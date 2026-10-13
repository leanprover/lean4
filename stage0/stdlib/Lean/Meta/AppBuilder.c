// Lean compiler output
// Module: Lean.Meta.AppBuilder
// Imports: public import Lean.Meta.SynthInstance public import Lean.Meta.DecLevel import Lean.Meta.CtorRecognizer public import Lean.Meta.HasAssignableMVar import Lean.Structure import Init.Omega
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_constructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Expr_getNumHeadForalls(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_instExceptToTraceResultExpr___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO___redArg();
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Meta_mkId___closed__0 = (const lean_object*)&l_Lean_Meta_mkId___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkId___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l_Lean_Meta_mkId___closed__1 = (const lean_object*)&l_Lean_Meta_mkId___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHintCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_mkEq___closed__0 = (const lean_object*)&l_Lean_Meta_mkEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_mkEq___closed__1 = (const lean_object*)&l_Lean_Meta_mkEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkHEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_mkHEq___closed__0 = (const lean_object*)&l_Lean_Meta_mkHEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkHEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkHEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_mkHEq___closed__1 = (const lean_object*)&l_Lean_Meta_mkHEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_mkEqRefl___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqRefl___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqRefl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqRefl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqRefl___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_mkEqRefl___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqRefl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_mkHEqRefl___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkHEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l_Lean_Meta_mkHEqRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkHEqRefl___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 202, 227, 45, 204, 223, 127, 41)}};
static const lean_object* l_Lean_Meta_mkHEqRefl___closed__0 = (const lean_object*)&l_Lean_Meta_mkHEqRefl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkAbsurd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "absurd"};
static const lean_object* l_Lean_Meta_mkAbsurd___closed__0 = (const lean_object*)&l_Lean_Meta_mkAbsurd___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkAbsurd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkAbsurd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 22, 196, 124, 199, 219, 238, 136)}};
static const lean_object* l_Lean_Meta_mkAbsurd___closed__1 = (const lean_object*)&l_Lean_Meta_mkAbsurd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkFalseElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_mkFalseElim___closed__0 = (const lean_object*)&l_Lean_Meta_mkFalseElim___closed__0_value;
static const lean_string_object l_Lean_Meta_mkFalseElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_Meta_mkFalseElim___closed__1 = (const lean_object*)&l_Lean_Meta_mkFalseElim___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkFalseElim___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkFalseElim___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l_Lean_Meta_mkFalseElim___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkFalseElim___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkFalseElim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l_Lean_Meta_mkFalseElim___closed__2 = (const lean_object*)&l_Lean_Meta_mkFalseElim___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nhas type"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__0 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "AppBuilder for `"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`, "};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqSymm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l_Lean_Meta_mkEqSymm___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqSymm___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqSymm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqSymm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqSymm___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqSymm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l_Lean_Meta_mkEqSymm___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqSymm___closed__1_value;
static const lean_string_object l_Lean_Meta_mkEqSymm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "equality proof expected"};
static const lean_object* l_Lean_Meta_mkEqSymm___closed__2 = (const lean_object*)&l_Lean_Meta_mkEqSymm___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkEqSymm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqSymm___closed__2_value)}};
static const lean_object* l_Lean_Meta_mkEqSymm___closed__3 = (const lean_object*)&l_Lean_Meta_mkEqSymm___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkEqSymm___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqSymm___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqTransCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_mkEqTransCore___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqTransCore___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqTransCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqTransCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqTransCore___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqTransCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_mkEqTransCore___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqTransCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTransCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkEqTransCoreProp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqTransCoreProp___closed__0;
static lean_once_cell_t l_Lean_Meta_mkEqTransCoreProp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqTransCoreProp___closed__1;
static lean_once_cell_t l_Lean_Meta_mkEqTransCoreProp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqTransCoreProp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTransCoreProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_mkHEqSymm___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkHEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l_Lean_Meta_mkHEqSymm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkHEqSymm___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqSymm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 163, 143, 122, 204, 41, 227, 16)}};
static const lean_object* l_Lean_Meta_mkHEqSymm___closed__0 = (const lean_object*)&l_Lean_Meta_mkHEqSymm___closed__0_value;
static const lean_string_object l_Lean_Meta_mkHEqSymm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "heterogeneous equality proof expected"};
static const lean_object* l_Lean_Meta_mkHEqSymm___closed__1 = (const lean_object*)&l_Lean_Meta_mkHEqSymm___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkHEqSymm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkHEqSymm___closed__1_value)}};
static const lean_object* l_Lean_Meta_mkHEqSymm___closed__2 = (const lean_object*)&l_Lean_Meta_mkHEqSymm___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkHEqSymm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHEqSymm___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_mkHEqTrans___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkHEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l_Lean_Meta_mkHEqTrans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkHEqTrans___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqTransCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 23, 102, 245, 235, 101, 160, 50)}};
static const lean_object* l_Lean_Meta_mkHEqTrans___closed__0 = (const lean_object*)&l_Lean_Meta_mkHEqTrans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqOfHEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_of_heq"};
static const lean_object* l_Lean_Meta_mkEqOfHEq___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqOfHEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqOfHEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEqOfHEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 61, 104, 192, 47, 1, 246, 178)}};
static const lean_object* l_Lean_Meta_mkEqOfHEq___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqOfHEq___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkEqOfHEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__2;
static const lean_string_object l_Lean_Meta_mkEqOfHEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "heterogeneous equality types are not definitionally equal"};
static const lean_object* l_Lean_Meta_mkEqOfHEq___closed__3 = (const lean_object*)&l_Lean_Meta_mkEqOfHEq___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkEqOfHEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__4;
static const lean_string_object l_Lean_Meta_mkEqOfHEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\nis not definitionally equal to"};
static const lean_object* l_Lean_Meta_mkEqOfHEq___closed__5 = (const lean_object*)&l_Lean_Meta_mkEqOfHEq___closed__5_value;
static lean_once_cell_t l_Lean_Meta_mkEqOfHEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkHEqOfEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "heq_of_eq"};
static const lean_object* l_Lean_Meta_mkHEqOfEq___closed__0 = (const lean_object*)&l_Lean_Meta_mkHEqOfEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkHEqOfEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkHEqOfEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 243, 206, 193, 60, 85, 181, 135)}};
static const lean_object* l_Lean_Meta_mkHEqOfEq___closed__1 = (const lean_object*)&l_Lean_Meta_mkHEqOfEq___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkHEqOfEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHEqOfEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f___boxed(lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_congrArg_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_congrArg_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_congrArg_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_congrArg_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_congrArg_x3f___closed__2;
static const lean_string_object l_Lean_Meta_congrArg_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Meta.AppBuilder"};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_congrArg_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.congrArg\?"};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_congrArg_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_congrArg_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_congrArg_x3f___closed__6;
static const lean_string_object l_Lean_Meta_congrArg_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_congrArg_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_congrArg_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Meta_congrArg_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_congrArg_x3f___closed__9;
static lean_once_cell_t l_Lean_Meta_congrArg_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_congrArg_x3f___closed__10;
static const lean_string_object l_Lean_Meta_congrArg_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__11_value;
static const lean_ctor_object l_Lean_Meta_congrArg_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_congrArg_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_congrArg_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_congrArg_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_congrArg_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_congrArg_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_congrArg_x3f___closed__14_value;
static lean_once_cell_t l_Lean_Meta_congrArg_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_congrArg_x3f___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkCongrArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "non-dependent function expected"};
static const lean_object* l_Lean_Meta_mkCongrArg___closed__0 = (const lean_object*)&l_Lean_Meta_mkCongrArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkCongrArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkCongrArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_mkCongrArg___closed__1 = (const lean_object*)&l_Lean_Meta_mkCongrArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkCongrArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkCongrFun___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrFun___closed__0;
static const lean_string_object l_Lean_Meta_mkCongrFun___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "equality proof between functions expected"};
static const lean_object* l_Lean_Meta_mkCongrFun___closed__1 = (const lean_object*)&l_Lean_Meta_mkCongrFun___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkCongrFun___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkCongrFun___closed__1_value)}};
static const lean_object* l_Lean_Meta_mkCongrFun___closed__2 = (const lean_object*)&l_Lean_Meta_mkCongrFun___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkCongrFun___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrFun___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_Lean_Meta_mkCongr___closed__0 = (const lean_object*)&l_Lean_Meta_mkCongr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l_Lean_Meta_mkCongr___closed__1 = (const lean_object*)&l_Lean_Meta_mkCongr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "result contains metavariables"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__0 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkAppM"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 168, 61, 153, 3, 196, 143, 146)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1_value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "too many explicit arguments provided to"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\narguments"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "f: "};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", xs: "};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19_value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "appBuilder"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__20 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__20_value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__21 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(68, 214, 164, 127, 225, 162, 166, 248)}};
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(54, 138, 27, 160, 212, 155, 243, 43)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22_value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__23 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultExpr___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(68, 214, 164, 127, 225, 162, 166, 248)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27_value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__31 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(68, 214, 164, 127, 225, 162, 166, 248)}};
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32_value_aux_1),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__31_value),LEAN_SCALAR_PTR_LITERAL(183, 173, 214, 125, 197, 91, 46, 196)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mkAppOptM"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__0 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 166, 217, 169, 142, 163, 216, 85)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1_value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "too many arguments provided to"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arguments"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqNDRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_Meta_mkEqNDRec___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqNDRec___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqNDRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqNDRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqNDRec___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqNDRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 164, 251, 202, 217, 58, 77, 179)}};
static const lean_object* l_Lean_Meta_mkEqNDRec___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqNDRec___closed__1_value;
static const lean_string_object l_Lean_Meta_mkEqNDRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid motive"};
static const lean_object* l_Lean_Meta_mkEqNDRec___closed__2 = (const lean_object*)&l_Lean_Meta_mkEqNDRec___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkEqNDRec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqNDRec___closed__2_value)}};
static const lean_object* l_Lean_Meta_mkEqNDRec___closed__3 = (const lean_object*)&l_Lean_Meta_mkEqNDRec___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkEqNDRec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqNDRec___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l_Lean_Meta_mkEqRec___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqRec___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqRec___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
static const lean_object* l_Lean_Meta_mkEqRec___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqRec___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqMPCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_mkEqMPCore___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqMPCore___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqMPCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqMPCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqMPCore___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqMPCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_mkEqMPCore___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqMPCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqMPR___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l_Lean_Meta_mkEqMPR___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqMPR___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqMPR___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqMPR___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqMPR___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqMPR___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 109, 21, 40, 70, 113, 251, 6)}};
static const lean_object* l_Lean_Meta_mkEqMPR___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqMPR___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "mkNoConfusion: unexpected equality `"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` as next argument to"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "noConfusion"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__0 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkNoConfusion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNoConfusion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 156, 154, 136, 239, 72, 108, 239)}};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__1 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__1_value;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__2 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkNoConfusion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkNoConfusion___closed__2_value)}};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__3 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__4;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "mkNoConfusion: No manifest constructors in "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__5 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__5_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__6;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__7 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__7_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__8;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "inductive type expected"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__9 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__9_value;
static const lean_ctor_object l_Lean_Meta_mkNoConfusion___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkNoConfusion___closed__9_value)}};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__10 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__10_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__11;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.mkNoConfusion"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__12 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__12_value;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 81, .m_data = "assertion violation: arity ≥ xs.size + fields1.size + fields2.size + 3\n          "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__13 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__13_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__14;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "mkNoConfusion: Missing "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__15 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__15_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__16;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "P"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__17 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__17_value;
static const lean_ctor_object l_Lean_Meta_mkNoConfusion___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNoConfusion___closed__17_value),LEAN_SCALAR_PTR_LITERAL(160, 230, 119, 31, 245, 11, 149, 236)}};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__18 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__18_value;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__19 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__19_value;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "noConfusion_of_Nat"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__20 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__20_value;
static const lean_ctor_object l_Lean_Meta_mkNoConfusion___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNoConfusion___closed__20_value),LEAN_SCALAR_PTR_LITERAL(151, 214, 13, 141, 28, 69, 207, 64)}};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__21 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__21_value;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " or "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__22 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__22_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__23;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l_Lean_Meta_mkPure___closed__0 = (const lean_object*)&l_Lean_Meta_mkPure___closed__0_value;
static const lean_string_object l_Lean_Meta_mkPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Meta_mkPure___closed__1 = (const lean_object*)&l_Lean_Meta_mkPure___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkPure___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 135, 27, 238, 232, 181, 75, 85)}};
static const lean_ctor_object l_Lean_Meta_mkPure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkPure___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkPure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 106, 105, 165, 210, 13, 14, 1)}};
static const lean_object* l_Lean_Meta_mkPure___closed__2 = (const lean_object*)&l_Lean_Meta_mkPure___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_mkProjection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mkProjection"};
static const lean_object* l_Lean_Meta_mkProjection___closed__0 = (const lean_object*)&l_Lean_Meta_mkProjection___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkProjection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkProjection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 195, 245, 38, 210, 93, 144, 108)}};
static const lean_object* l_Lean_Meta_mkProjection___closed__1 = (const lean_object*)&l_Lean_Meta_mkProjection___closed__1_value;
static const lean_string_object l_Lean_Meta_mkProjection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid field name '"};
static const lean_object* l_Lean_Meta_mkProjection___closed__2 = (const lean_object*)&l_Lean_Meta_mkProjection___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkProjection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkProjection___closed__2_value)}};
static const lean_object* l_Lean_Meta_mkProjection___closed__3 = (const lean_object*)&l_Lean_Meta_mkProjection___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkProjection___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjection___closed__4;
static const lean_string_object l_Lean_Meta_mkProjection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "' for"};
static const lean_object* l_Lean_Meta_mkProjection___closed__5 = (const lean_object*)&l_Lean_Meta_mkProjection___closed__5_value;
static const lean_ctor_object l_Lean_Meta_mkProjection___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkProjection___closed__5_value)}};
static const lean_object* l_Lean_Meta_mkProjection___closed__6 = (const lean_object*)&l_Lean_Meta_mkProjection___closed__6_value;
static lean_once_cell_t l_Lean_Meta_mkProjection___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjection___closed__7;
static const lean_string_object l_Lean_Meta_mkProjection___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structure expected"};
static const lean_object* l_Lean_Meta_mkProjection___closed__8 = (const lean_object*)&l_Lean_Meta_mkProjection___closed__8_value;
static const lean_ctor_object l_Lean_Meta_mkProjection___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkProjection___closed__8_value)}};
static const lean_object* l_Lean_Meta_mkProjection___closed__9 = (const lean_object*)&l_Lean_Meta_mkProjection___closed__9_value;
static lean_once_cell_t l_Lean_Meta_mkProjection___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjection___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkListLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_mkListLit___closed__0 = (const lean_object*)&l_Lean_Meta_mkListLit___closed__0_value;
static const lean_string_object l_Lean_Meta_mkListLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Meta_mkListLit___closed__1 = (const lean_object*)&l_Lean_Meta_mkListLit___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkListLit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkListLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkListLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkListLit___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkListLit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Meta_mkListLit___closed__2 = (const lean_object*)&l_Lean_Meta_mkListLit___closed__2_value;
static const lean_string_object l_Lean_Meta_mkListLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Meta_mkListLit___closed__3 = (const lean_object*)&l_Lean_Meta_mkListLit___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkListLit___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkListLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkListLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkListLit___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_mkListLit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Meta_mkListLit___closed__4 = (const lean_object*)&l_Lean_Meta_mkListLit___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkArrayLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Meta_mkArrayLit___closed__0 = (const lean_object*)&l_Lean_Meta_mkArrayLit___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkArrayLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkListLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkArrayLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkArrayLit___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkArrayLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_Meta_mkArrayLit___closed__1 = (const lean_object*)&l_Lean_Meta_mkArrayLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkNone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Meta_mkNone___closed__0 = (const lean_object*)&l_Lean_Meta_mkNone___closed__0_value;
static const lean_string_object l_Lean_Meta_mkNone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Meta_mkNone___closed__1 = (const lean_object*)&l_Lean_Meta_mkNone___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkNone___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNone___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Meta_mkNone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkNone___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkNone___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Meta_mkNone___closed__2 = (const lean_object*)&l_Lean_Meta_mkNone___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSome___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Meta_mkSome___closed__0 = (const lean_object*)&l_Lean_Meta_mkSome___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSome___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNone___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Meta_mkSome___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSome___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkSome___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Meta_mkSome___closed__1 = (const lean_object*)&l_Lean_Meta_mkSome___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Meta_mkDecide___closed__0 = (const lean_object*)&l_Lean_Meta_mkDecide___closed__0_value;
static const lean_string_object l_Lean_Meta_mkDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_mkDecide___closed__1 = (const lean_object*)&l_Lean_Meta_mkDecide___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkDecide___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Meta_mkDecide___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkDecide___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l_Lean_Meta_mkDecide___closed__2 = (const lean_object*)&l_Lean_Meta_mkDecide___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkDecideProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_mkDecideProof___closed__0 = (const lean_object*)&l_Lean_Meta_mkDecideProof___closed__0_value;
static const lean_string_object l_Lean_Meta_mkDecideProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_mkDecideProof___closed__1 = (const lean_object*)&l_Lean_Meta_mkDecideProof___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkDecideProof___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkDecideProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_mkDecideProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkDecideProof___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkDecideProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_mkDecideProof___closed__2 = (const lean_object*)&l_Lean_Meta_mkDecideProof___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkDecideProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkDecideProof___closed__3;
static const lean_string_object l_Lean_Meta_mkDecideProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l_Lean_Meta_mkDecideProof___closed__4 = (const lean_object*)&l_Lean_Meta_mkDecideProof___closed__4_value;
static const lean_ctor_object l_Lean_Meta_mkDecideProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkDecideProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(199, 143, 142, 104, 169, 34, 63, 25)}};
static const lean_object* l_Lean_Meta_mkDecideProof___closed__5 = (const lean_object*)&l_Lean_Meta_mkDecideProof___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_mkLt___closed__0 = (const lean_object*)&l_Lean_Meta_mkLt___closed__0_value;
static const lean_string_object l_Lean_Meta_mkLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_mkLt___closed__1 = (const lean_object*)&l_Lean_Meta_mkLt___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkLt___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_mkLt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkLt___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkLt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_mkLt___closed__2 = (const lean_object*)&l_Lean_Meta_mkLt___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkLe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_mkLe___closed__0 = (const lean_object*)&l_Lean_Meta_mkLe___closed__0_value;
static const lean_string_object l_Lean_Meta_mkLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_mkLe___closed__1 = (const lean_object*)&l_Lean_Meta_mkLe___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkLe___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_mkLe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkLe___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_mkLe___closed__2 = (const lean_object*)&l_Lean_Meta_mkLe___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkDefault___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l_Lean_Meta_mkDefault___closed__0 = (const lean_object*)&l_Lean_Meta_mkDefault___closed__0_value;
static const lean_string_object l_Lean_Meta_mkDefault___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Meta_mkDefault___closed__1 = (const lean_object*)&l_Lean_Meta_mkDefault___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkDefault___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkDefault___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l_Lean_Meta_mkDefault___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkDefault___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkDefault___closed__1_value),LEAN_SCALAR_PTR_LITERAL(174, 152, 115, 107, 166, 56, 116, 8)}};
static const lean_object* l_Lean_Meta_mkDefault___closed__2 = (const lean_object*)&l_Lean_Meta_mkDefault___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkOfNonempty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_Meta_mkOfNonempty___closed__0 = (const lean_object*)&l_Lean_Meta_mkOfNonempty___closed__0_value;
static const lean_string_object l_Lean_Meta_mkOfNonempty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ofNonempty"};
static const lean_object* l_Lean_Meta_mkOfNonempty___closed__1 = (const lean_object*)&l_Lean_Meta_mkOfNonempty___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkOfNonempty___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkOfNonempty___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_Meta_mkOfNonempty___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkOfNonempty___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkOfNonempty___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 41, 144, 91, 215, 43, 73, 12)}};
static const lean_object* l_Lean_Meta_mkOfNonempty___closed__2 = (const lean_object*)&l_Lean_Meta_mkOfNonempty___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkFunExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "funext"};
static const lean_object* l_Lean_Meta_mkFunExt___closed__0 = (const lean_object*)&l_Lean_Meta_mkFunExt___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkFunExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkFunExt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 251, 226, 140, 5, 134, 146, 130)}};
static const lean_object* l_Lean_Meta_mkFunExt___closed__1 = (const lean_object*)&l_Lean_Meta_mkFunExt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkPropExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l_Lean_Meta_mkPropExt___closed__0 = (const lean_object*)&l_Lean_Meta_mkPropExt___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkPropExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkPropExt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l_Lean_Meta_mkPropExt___closed__1 = (const lean_object*)&l_Lean_Meta_mkPropExt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkLetCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "let_congr"};
static const lean_object* l_Lean_Meta_mkLetCongr___closed__0 = (const lean_object*)&l_Lean_Meta_mkLetCongr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkLetCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLetCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 187, 63, 239, 0, 76, 154, 156)}};
static const lean_object* l_Lean_Meta_mkLetCongr___closed__1 = (const lean_object*)&l_Lean_Meta_mkLetCongr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkLetValCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "let_val_congr"};
static const lean_object* l_Lean_Meta_mkLetValCongr___closed__0 = (const lean_object*)&l_Lean_Meta_mkLetValCongr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkLetValCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLetValCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 241, 199, 153, 91, 27, 42, 122)}};
static const lean_object* l_Lean_Meta_mkLetValCongr___closed__1 = (const lean_object*)&l_Lean_Meta_mkLetValCongr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkLetBodyCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "let_body_congr"};
static const lean_object* l_Lean_Meta_mkLetBodyCongr___closed__0 = (const lean_object*)&l_Lean_Meta_mkLetBodyCongr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkLetBodyCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLetBodyCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 115, 150, 132, 106, 100, 45, 219)}};
static const lean_object* l_Lean_Meta_mkLetBodyCongr___closed__1 = (const lean_object*)&l_Lean_Meta_mkLetBodyCongr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkOfEqFalseCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "of_eq_false"};
static const lean_object* l_Lean_Meta_mkOfEqFalseCore___closed__0 = (const lean_object*)&l_Lean_Meta_mkOfEqFalseCore___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkOfEqFalseCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkOfEqFalseCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 110, 142, 77, 120, 210, 227, 9)}};
static const lean_object* l_Lean_Meta_mkOfEqFalseCore___closed__1 = (const lean_object*)&l_Lean_Meta_mkOfEqFalseCore___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkOfEqFalseCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkOfEqFalseCore___closed__2;
static const lean_string_object l_Lean_Meta_mkOfEqFalseCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_false"};
static const lean_object* l_Lean_Meta_mkOfEqFalseCore___closed__3 = (const lean_object*)&l_Lean_Meta_mkOfEqFalseCore___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkOfEqFalseCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkOfEqFalseCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(242, 127, 91, 199, 130, 171, 29, 27)}};
static const lean_object* l_Lean_Meta_mkOfEqFalseCore___closed__4 = (const lean_object*)&l_Lean_Meta_mkOfEqFalseCore___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkOfEqTrueCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_eq_true"};
static const lean_object* l_Lean_Meta_mkOfEqTrueCore___closed__0 = (const lean_object*)&l_Lean_Meta_mkOfEqTrueCore___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkOfEqTrueCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkOfEqTrueCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 216, 190, 52, 49, 30, 207, 178)}};
static const lean_object* l_Lean_Meta_mkOfEqTrueCore___closed__1 = (const lean_object*)&l_Lean_Meta_mkOfEqTrueCore___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkOfEqTrueCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkOfEqTrueCore___closed__2;
static const lean_string_object l_Lean_Meta_mkOfEqTrueCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_true"};
static const lean_object* l_Lean_Meta_mkOfEqTrueCore___closed__3 = (const lean_object*)&l_Lean_Meta_mkOfEqTrueCore___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkOfEqTrueCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkOfEqTrueCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(50, 213, 255, 45, 151, 209, 83, 175)}};
static const lean_object* l_Lean_Meta_mkOfEqTrueCore___closed__4 = (const lean_object*)&l_Lean_Meta_mkOfEqTrueCore___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkEqTrueCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkEqTrueCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkEqFalse_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_false'"};
static const lean_object* l_Lean_Meta_mkEqFalse_x27___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqFalse_x27___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqFalse_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEqFalse_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 24, 186, 138, 47, 9, 234, 218)}};
static const lean_object* l_Lean_Meta_mkEqFalse_x27___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqFalse_x27___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkImpCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "implies_congr"};
static const lean_object* l_Lean_Meta_mkImpCongr___closed__0 = (const lean_object*)&l_Lean_Meta_mkImpCongr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkImpCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkImpCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 71, 54, 187, 9, 73, 178, 153)}};
static const lean_object* l_Lean_Meta_mkImpCongr___closed__1 = (const lean_object*)&l_Lean_Meta_mkImpCongr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkImpCongrCtx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "implies_congr_ctx"};
static const lean_object* l_Lean_Meta_mkImpCongrCtx___closed__0 = (const lean_object*)&l_Lean_Meta_mkImpCongrCtx___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkImpCongrCtx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkImpCongrCtx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 145, 179, 180, 34, 42, 7, 230)}};
static const lean_object* l_Lean_Meta_mkImpCongrCtx___closed__1 = (const lean_object*)&l_Lean_Meta_mkImpCongrCtx___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkImpDepCongrCtx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "implies_dep_congr_ctx"};
static const lean_object* l_Lean_Meta_mkImpDepCongrCtx___closed__0 = (const lean_object*)&l_Lean_Meta_mkImpDepCongrCtx___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkImpDepCongrCtx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkImpDepCongrCtx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 151, 212, 25, 231, 139, 56, 165)}};
static const lean_object* l_Lean_Meta_mkImpDepCongrCtx___closed__1 = (const lean_object*)&l_Lean_Meta_mkImpDepCongrCtx___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkForallCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_congr"};
static const lean_object* l_Lean_Meta_mkForallCongr___closed__0 = (const lean_object*)&l_Lean_Meta_mkForallCongr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkForallCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkForallCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 145, 235, 56, 9, 236, 160, 253)}};
static const lean_object* l_Lean_Meta_mkForallCongr___closed__1 = (const lean_object*)&l_Lean_Meta_mkForallCongr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_isMonad_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Monad"};
static const lean_object* l_Lean_Meta_isMonad_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_isMonad_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_isMonad_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_isMonad_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 218, 3, 131, 37, 173, 20, 218)}};
static const lean_object* l_Lean_Meta_isMonad_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_isMonad_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkNumeral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_mkNumeral___closed__0 = (const lean_object*)&l_Lean_Meta_mkNumeral___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkNumeral___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_mkNumeral___closed__1 = (const lean_object*)&l_Lean_Meta_mkNumeral___closed__1_value;
static const lean_string_object l_Lean_Meta_mkNumeral___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_mkNumeral___closed__2 = (const lean_object*)&l_Lean_Meta_mkNumeral___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkNumeral___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_mkNumeral___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkNumeral___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkNumeral___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_mkNumeral___closed__3 = (const lean_object*)&l_Lean_Meta_mkNumeral___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_mkAdd___closed__0 = (const lean_object*)&l_Lean_Meta_mkAdd___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkAdd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_mkAdd___closed__1 = (const lean_object*)&l_Lean_Meta_mkAdd___closed__1_value;
static const lean_string_object l_Lean_Meta_mkAdd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_mkAdd___closed__2 = (const lean_object*)&l_Lean_Meta_mkAdd___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkAdd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkAdd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_mkAdd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkAdd___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkAdd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_mkAdd___closed__3 = (const lean_object*)&l_Lean_Meta_mkAdd___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_mkSub___closed__0 = (const lean_object*)&l_Lean_Meta_mkSub___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSub___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSub___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l_Lean_Meta_mkSub___closed__1 = (const lean_object*)&l_Lean_Meta_mkSub___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSub___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_mkSub___closed__2 = (const lean_object*)&l_Lean_Meta_mkSub___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkSub___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSub___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_mkSub___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSub___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkSub___closed__2_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_mkSub___closed__3 = (const lean_object*)&l_Lean_Meta_mkSub___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_mkMul___closed__0 = (const lean_object*)&l_Lean_Meta_mkMul___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_mkMul___closed__1 = (const lean_object*)&l_Lean_Meta_mkMul___closed__1_value;
static const lean_string_object l_Lean_Meta_mkMul___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_mkMul___closed__2 = (const lean_object*)&l_Lean_Meta_mkMul___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkMul___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_mkMul___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkMul___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkMul___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_mkMul___closed__3 = (const lean_object*)&l_Lean_Meta_mkMul___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_mkLE___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l_Lean_Meta_mkLE___closed__0 = (const lean_object*)&l_Lean_Meta_mkLE___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_mkLT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l_Lean_Meta_mkLT___closed__0 = (const lean_object*)&l_Lean_Meta_mkLT___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkIffOfEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_Meta_mkIffOfEq___closed__0 = (const lean_object*)&l_Lean_Meta_mkIffOfEq___closed__0_value;
static const lean_string_object l_Lean_Meta_mkIffOfEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_eq"};
static const lean_object* l_Lean_Meta_mkIffOfEq___closed__1 = (const lean_object*)&l_Lean_Meta_mkIffOfEq___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkIffOfEq___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkIffOfEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l_Lean_Meta_mkIffOfEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkIffOfEq___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkIffOfEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 38, 134, 223, 103, 86, 218, 33)}};
static const lean_object* l_Lean_Meta_mkIffOfEq___closed__2 = (const lean_object*)&l_Lean_Meta_mkIffOfEq___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "AppBuilder"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 164, 115, 227, 54, 6, 112, 39)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(214, 146, 209, 37, 149, 211, 154, 41)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 102, 143, 76, 247, 41, 47, 77)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(191, 120, 190, 17, 47, 201, 84, 77)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(222, 189, 61, 101, 32, 207, 72, 138)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 240, 179, 139, 43, 114, 206, 84)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 231, 143, 116, 246, 22, 155, 198)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(230, 198, 81, 198, 42, 113, 83, 229)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 134, 57, 8, 157, 134, 22, 41)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)(((size_t)(902289040) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(58, 214, 141, 107, 23, 160, 250, 49)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(21, 204, 30, 15, 137, 209, 94, 18)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 31, 185, 173, 77, 235, 62, 149)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 243, 103, 192, 162, 97, 60, 190)}};
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkId(lean_object* v_e_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; 
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc_ref(v_e_4_);
v___x_10_ = lean_infer_type(v_e_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_n(v_a_11_, 2);
lean_dec_ref_known(v___x_10_, 1);
v___x_12_ = l_Lean_Meta_getLevel(v_a_11_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_25_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_25_ == 0)
{
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_25_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_25_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_17_ = ((lean_object*)(l_Lean_Meta_mkId___closed__1));
v___x_18_ = lean_box(0);
v___x_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_19_, 0, v_a_13_);
lean_ctor_set(v___x_19_, 1, v___x_18_);
v___x_20_ = l_Lean_mkConst(v___x_17_, v___x_19_);
v___x_21_ = l_Lean_mkAppB(v___x_20_, v_a_11_, v_e_4_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_21_);
v___x_23_ = v___x_15_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec(v_a_11_);
lean_dec_ref(v_e_4_);
v_a_26_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_12_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_12_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
else
{
lean_dec_ref(v_e_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkId___boxed(lean_object* v_e_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_mkId(v_e_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHintCore(lean_object* v_e_41_, lean_object* v_expectedType_42_, lean_object* v_expectedTypeUniv_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_44_ = ((lean_object*)(l_Lean_Meta_mkId___closed__1));
v___x_45_ = lean_box(0);
v___x_46_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_46_, 0, v_expectedTypeUniv_43_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = l_Lean_mkConst(v___x_44_, v___x_46_);
v___x_48_ = l_Lean_mkAppB(v___x_47_, v_expectedType_42_, v_e_41_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object* v_proof_49_, lean_object* v_expectedProp_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_box(0);
v___x_52_ = l_Lean_Meta_mkExpectedTypeHintCore(v_proof_49_, v_expectedProp_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object* v_e_53_, lean_object* v_expectedType_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; 
lean_inc_ref(v_expectedType_54_);
v___x_60_ = l_Lean_Meta_getLevel(v_expectedType_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_69_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_69_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_65_ = l_Lean_Meta_mkExpectedTypeHintCore(v_e_53_, v_expectedType_54_, v_a_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_65_);
v___x_67_ = v___x_63_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
else
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_77_; 
lean_dec_ref(v_expectedType_54_);
lean_dec_ref(v_e_53_);
v_a_70_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_77_ == 0)
{
v___x_72_ = v___x_60_;
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_60_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_a_70_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint___boxed(lean_object* v_e_78_, lean_object* v_expectedType_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Meta_mkExpectedTypeHint(v_e_78_, v_expectedType_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq(lean_object* v_a_89_, lean_object* v_b_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; 
lean_inc(v_a_94_);
lean_inc_ref(v_a_93_);
lean_inc(v_a_92_);
lean_inc_ref(v_a_91_);
lean_inc_ref(v_a_89_);
v___x_96_ = lean_infer_type(v_a_89_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_n(v_a_97_, 2);
lean_dec_ref_known(v___x_96_, 1);
v___x_98_ = l_Lean_Meta_getLevel(v_a_97_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_111_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_111_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_103_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v_a_99_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = l_Lean_mkConst(v___x_103_, v___x_105_);
v___x_107_ = l_Lean_mkApp3(v___x_106_, v_a_97_, v_a_89_, v_b_90_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_107_);
v___x_109_ = v___x_101_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec(v_a_97_);
lean_dec_ref(v_b_90_);
lean_dec_ref(v_a_89_);
v_a_112_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_98_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_98_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_dec_ref(v_b_90_);
lean_dec_ref(v_a_89_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq___boxed(lean_object* v_a_120_, lean_object* v_b_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_mkEq(v_a_120_, v_b_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq(lean_object* v_a_131_, lean_object* v_b_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
lean_inc(v_a_136_);
lean_inc_ref(v_a_135_);
lean_inc(v_a_134_);
lean_inc_ref(v_a_133_);
lean_inc_ref(v_a_131_);
v___x_138_ = lean_infer_type(v_a_131_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
lean_inc(v_a_136_);
lean_inc_ref(v_a_135_);
lean_inc(v_a_134_);
lean_inc_ref(v_a_133_);
lean_inc_ref(v_b_132_);
v___x_140_ = lean_infer_type(v_b_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
lean_inc(v_a_139_);
v___x_142_ = l_Lean_Meta_getLevel(v_a_139_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_155_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_155_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_155_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_155_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_147_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v_a_143_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = l_Lean_mkConst(v___x_147_, v___x_149_);
v___x_151_ = l_Lean_mkApp4(v___x_150_, v_a_139_, v_a_131_, v_a_141_, v_b_132_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_151_);
v___x_153_ = v___x_145_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_a_141_);
lean_dec(v_a_139_);
lean_dec_ref(v_b_132_);
lean_dec_ref(v_a_131_);
v_a_156_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_142_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_142_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_dec(v_a_139_);
lean_dec_ref(v_b_132_);
lean_dec_ref(v_a_131_);
return v___x_140_;
}
}
else
{
lean_dec_ref(v_b_132_);
lean_dec_ref(v_a_131_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq___boxed(lean_object* v_a_164_, lean_object* v_b_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Meta_mkHEq(v_a_164_, v_b_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq(lean_object* v_a_172_, lean_object* v_b_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; 
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
lean_inc_ref(v_a_172_);
v___x_179_ = lean_infer_type(v_a_172_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
lean_inc_ref(v_b_173_);
v___x_181_ = lean_infer_type(v_b_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
lean_inc(v_a_180_);
v___x_183_ = l_Lean_Meta_getLevel(v_a_180_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
lean_inc(v_a_182_);
lean_inc(v_a_180_);
v___x_185_ = l_Lean_Meta_isExprDefEq(v_a_180_, v_a_182_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_207_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_207_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_207_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
uint8_t v___x_190_; 
v___x_190_ = lean_unbox(v_a_186_);
lean_dec(v_a_186_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_191_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_192_ = lean_box(0);
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v_a_184_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = l_Lean_mkConst(v___x_191_, v___x_193_);
v___x_195_ = l_Lean_mkApp4(v___x_194_, v_a_180_, v_a_172_, v_a_182_, v_b_173_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_195_);
v___x_197_ = v___x_188_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec(v_a_182_);
v___x_199_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v_a_184_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l_Lean_mkConst(v___x_199_, v___x_201_);
v___x_203_ = l_Lean_mkApp3(v___x_202_, v_a_180_, v_a_172_, v_b_173_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_203_);
v___x_205_ = v___x_188_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec(v_a_184_);
lean_dec(v_a_182_);
lean_dec(v_a_180_);
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
v_a_208_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_185_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_185_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec(v_a_182_);
lean_dec(v_a_180_);
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
v_a_216_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_183_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_183_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_dec(v_a_180_);
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
return v___x_181_;
}
}
else
{
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq___boxed(lean_object* v_a_224_, lean_object* v_b_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Meta_mkEqHEq(v_a_224_, v_b_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRefl(lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; 
lean_inc(v_a_240_);
lean_inc_ref(v_a_239_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc_ref(v_a_236_);
v___x_242_ = lean_infer_type(v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc_n(v_a_243_, 2);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = l_Lean_Meta_getLevel(v_a_243_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_257_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_257_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_257_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_257_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_249_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v_a_245_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Lean_mkConst(v___x_249_, v___x_251_);
v___x_253_ = l_Lean_mkAppB(v___x_252_, v_a_243_, v_a_236_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_253_);
v___x_255_ = v___x_247_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec(v_a_243_);
lean_dec_ref(v_a_236_);
v_a_258_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_244_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_244_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
else
{
lean_dec_ref(v_a_236_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRefl___boxed(lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_mkEqRefl(v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl(lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_282_; 
lean_inc(v_a_280_);
lean_inc_ref(v_a_279_);
lean_inc(v_a_278_);
lean_inc_ref(v_a_277_);
lean_inc_ref(v_a_276_);
v___x_282_ = lean_infer_type(v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_n(v_a_283_, 2);
lean_dec_ref_known(v___x_282_, 1);
v___x_284_ = l_Lean_Meta_getLevel(v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_297_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_297_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_297_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_297_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_289_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_290_ = lean_box(0);
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v_a_285_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_mkConst(v___x_289_, v___x_291_);
v___x_293_ = l_Lean_mkAppB(v___x_292_, v_a_283_, v_a_276_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_293_);
v___x_295_ = v___x_287_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_a_283_);
lean_dec_ref(v_a_276_);
v_a_298_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_284_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_284_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_dec_ref(v_a_276_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl___boxed(lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Meta_mkHEqRefl(v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd(lean_object* v_e_316_, lean_object* v_hp_317_, lean_object* v_hnp_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc_ref(v_hp_317_);
v___x_324_ = lean_infer_type(v_hp_317_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
lean_inc_ref(v_e_316_);
v___x_326_ = l_Lean_Meta_getLevel(v_e_316_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_339_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_339_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_339_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_339_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_mkAbsurd___closed__1));
v___x_332_ = lean_box(0);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v_a_327_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = l_Lean_mkConst(v___x_331_, v___x_333_);
v___x_335_ = l_Lean_mkApp4(v___x_334_, v_a_325_, v_e_316_, v_hp_317_, v_hnp_318_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_335_);
v___x_337_ = v___x_329_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_325_);
lean_dec_ref(v_hnp_318_);
lean_dec_ref(v_hp_317_);
lean_dec_ref(v_e_316_);
v_a_340_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_326_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_326_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_dec_ref(v_hnp_318_);
lean_dec_ref(v_hp_317_);
lean_dec_ref(v_e_316_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd___boxed(lean_object* v_e_348_, lean_object* v_hp_349_, lean_object* v_hnp_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Meta_mkAbsurd(v_e_348_, v_hp_349_, v_hnp_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim(lean_object* v_e_362_, lean_object* v_h_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
lean_inc_ref(v_e_362_);
v___x_369_ = l_Lean_Meta_getLevel(v_e_362_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_382_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_382_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_374_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_375_ = lean_box(0);
v___x_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_376_, 0, v_a_370_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = l_Lean_mkConst(v___x_374_, v___x_376_);
v___x_378_ = l_Lean_mkAppB(v___x_377_, v_e_362_, v_h_363_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_378_);
v___x_380_ = v___x_372_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec_ref(v_h_363_);
lean_dec_ref(v_e_362_);
v_a_383_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_369_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_369_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim___boxed(lean_object* v_e_391_, lean_object* v_h_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_mkFalseElim(v_e_391_, v_h_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(lean_object* v_h_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; 
lean_inc(v_a_403_);
lean_inc_ref(v_a_402_);
lean_inc(v_a_401_);
lean_inc_ref(v_a_400_);
v___x_405_ = lean_infer_type(v_h_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = l_Lean_Meta_whnfD(v_a_406_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_407_;
}
else
{
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer___boxed(lean_object* v_h_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_414_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__0));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object* v_e_418_, lean_object* v_type_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = l_Lean_indentExpr(v_e_418_);
v___x_421_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_indentExpr(v_type_419_);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(lean_object* v_msgData_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; lean_object* v_env_432_; uint8_t v___x_433_; lean_object* v_env_434_; lean_object* v___x_435_; lean_object* v_toCold_436_; lean_object* v_mctx_437_; lean_object* v_lctx_438_; lean_object* v_options_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_431_ = lean_st_ref_get(v___y_429_);
v_env_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc_ref(v_env_432_);
lean_dec(v___x_431_);
v___x_433_ = 0;
v_env_434_ = l_Lean_Environment_setRecordingDeps(v_env_432_, v___x_433_);
v___x_435_ = lean_st_ref_get(v___y_427_);
v_toCold_436_ = lean_ctor_get(v___y_428_, 0);
v_mctx_437_ = lean_ctor_get(v___x_435_, 0);
lean_inc_ref(v_mctx_437_);
lean_dec(v___x_435_);
v_lctx_438_ = lean_ctor_get(v___y_426_, 2);
v_options_439_ = lean_ctor_get(v_toCold_436_, 2);
lean_inc_ref(v_options_439_);
lean_inc_ref(v_lctx_438_);
v___x_440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_440_, 0, v_env_434_);
lean_ctor_set(v___x_440_, 1, v_mctx_437_);
lean_ctor_set(v___x_440_, 2, v_lctx_438_);
lean_ctor_set(v___x_440_, 3, v_options_439_);
v___x_441_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v_msgData_425_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0___boxed(lean_object* v_msgData_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msgData_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_ref_456_; lean_object* v___x_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_ref_456_ = lean_ctor_get(v___y_453_, 2);
v___x_457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
lean_inc(v_ref_456_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v_ref_456_);
lean_ctor_set(v___x_462_, 1, v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 1);
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg___boxed(lean_object* v_msg_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v_res_473_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__0));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__2));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(lean_object* v_op_480_, lean_object* v_msg_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_487_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1);
v___x_488_ = l_Lean_MessageData_ofName(v_op_480_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_msg_481_);
v___x_493_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_492_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___boxed(lean_object* v_op_494_, lean_object* v_msg_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_op_494_, v_msg_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object* v_00_u03b1_502_, lean_object* v_op_503_, lean_object* v_msg_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_op_503_, v_msg_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___boxed(lean_object* v_00_u03b1_511_, lean_object* v_op_512_, lean_object* v_msg_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(v_00_u03b1_511_, v_op_512_, v_msg_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0(lean_object* v_00_u03b1_520_, lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___boxed(lean_object* v_00_u03b1_528_, lean_object* v_msg_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0(v_00_u03b1_528_, v_msg_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_535_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqSymm___closed__4(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__3));
v___x_544_ = l_Lean_MessageData_ofFormat(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object* v_h_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_552_ = l_Lean_Expr_isAppOf(v_h_545_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_inc_ref(v_h_545_);
v___x_553_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_556_ = lean_unsigned_to_nat(3u);
v___x_557_ = l_Lean_Expr_isAppOfArity(v_a_554_, v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_558_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__1));
v___x_559_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_560_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_545_, v_a_554_);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_558_, v___x_561_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_563_ = l_Lean_Expr_appFn_x21(v_a_554_);
v___x_564_ = l_Lean_Expr_appFn_x21(v___x_563_);
v___x_565_ = l_Lean_Expr_appArg_x21(v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_Lean_Expr_appArg_x21(v___x_563_);
lean_dec_ref(v___x_563_);
v___x_567_ = l_Lean_Expr_appArg_x21(v_a_554_);
lean_dec(v_a_554_);
lean_inc_ref(v___x_565_);
v___x_568_ = l_Lean_Meta_getLevel(v___x_565_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_581_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_581_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_581_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_581_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_573_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__1));
v___x_574_ = lean_box(0);
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v_a_569_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l_Lean_mkConst(v___x_573_, v___x_575_);
v___x_577_ = l_Lean_mkApp4(v___x_576_, v___x_565_, v___x_566_, v___x_567_, v_h_545_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_577_);
v___x_579_ = v___x_571_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v___x_567_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v_h_545_);
v_a_582_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_568_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_568_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_545_);
return v___x_553_;
}
}
else
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v_h_545_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm___boxed(lean_object* v_h_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Meta_mkEqSymm(v_h_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTransCore(lean_object* v_u_602_, lean_object* v_00_u03b1_603_, lean_object* v_a_604_, lean_object* v_b_605_, lean_object* v_c_606_, lean_object* v_h_u2081_607_, lean_object* v_h_u2082_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_609_ = ((lean_object*)(l_Lean_Meta_mkEqTransCore___closed__1));
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_611_, 0, v_u_602_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_mkConst(v___x_609_, v___x_611_);
v___x_613_ = l_Lean_mkApp6(v___x_612_, v_00_u03b1_603_, v_a_604_, v_b_605_, v_c_606_, v_h_u2081_607_, v_h_u2082_608_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTransCoreProp___closed__0(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = l_Lean_Level_ofNat(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTransCoreProp___closed__1(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = l_Lean_Level_ofNat(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTransCoreProp___closed__2(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_obj_once(&l_Lean_Meta_mkEqTransCoreProp___closed__1, &l_Lean_Meta_mkEqTransCoreProp___closed__1_once, _init_l_Lean_Meta_mkEqTransCoreProp___closed__1);
v___x_619_ = l_Lean_mkSort(v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTransCoreProp(lean_object* v_a_620_, lean_object* v_b_621_, lean_object* v_c_622_, lean_object* v_h_u2081_623_, lean_object* v_h_u2082_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_obj_once(&l_Lean_Meta_mkEqTransCoreProp___closed__0, &l_Lean_Meta_mkEqTransCoreProp___closed__0_once, _init_l_Lean_Meta_mkEqTransCoreProp___closed__0);
v___x_626_ = lean_obj_once(&l_Lean_Meta_mkEqTransCoreProp___closed__2, &l_Lean_Meta_mkEqTransCoreProp___closed__2_once, _init_l_Lean_Meta_mkEqTransCoreProp___closed__2);
v___x_627_ = l_Lean_Meta_mkEqTransCore(v___x_625_, v___x_626_, v_a_620_, v_b_621_, v_c_622_, v_h_u2081_623_, v_h_u2082_624_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object* v_h_u2081_628_, lean_object* v_h_u2082_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_636_ = l_Lean_Expr_isAppOf(v_h_u2081_628_, v___x_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; 
v___x_637_ = l_Lean_Expr_isAppOf(v_h_u2082_629_, v___x_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_inc_ref(v_h_u2081_628_);
v___x_638_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_628_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
lean_inc_ref(v_h_u2082_629_);
v___x_640_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_643_ = lean_unsigned_to_nat(3u);
v___x_644_ = l_Lean_Expr_isAppOfArity(v_a_639_, v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_a_641_);
lean_dec_ref(v_h_u2082_629_);
v___x_645_ = ((lean_object*)(l_Lean_Meta_mkEqTransCore___closed__1));
v___x_646_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_647_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_628_, v_a_639_);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_645_, v___x_648_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
return v___x_649_;
}
else
{
uint8_t v___x_650_; 
v___x_650_ = l_Lean_Expr_isAppOfArity(v_a_641_, v___x_642_, v___x_643_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v_a_639_);
lean_dec_ref(v_h_u2081_628_);
v___x_651_ = ((lean_object*)(l_Lean_Meta_mkEqTransCore___closed__1));
v___x_652_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_653_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_629_, v_a_641_);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_651_, v___x_654_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_656_ = l_Lean_Expr_appFn_x21(v_a_639_);
v___x_657_ = l_Lean_Expr_appFn_x21(v___x_656_);
v___x_658_ = l_Lean_Expr_appArg_x21(v___x_657_);
lean_dec_ref(v___x_657_);
v___x_659_ = l_Lean_Expr_appArg_x21(v___x_656_);
lean_dec_ref(v___x_656_);
v___x_660_ = l_Lean_Expr_appArg_x21(v_a_639_);
lean_dec(v_a_639_);
v___x_661_ = l_Lean_Expr_appArg_x21(v_a_641_);
lean_dec(v_a_641_);
lean_inc_ref(v___x_658_);
v___x_662_ = l_Lean_Meta_getLevel(v___x_658_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_Meta_mkEqTransCore(v_a_663_, v___x_658_, v___x_659_, v___x_660_, v___x_661_, v_h_u2081_628_, v_h_u2082_629_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v___x_661_);
lean_dec_ref(v___x_660_);
lean_dec_ref(v___x_659_);
lean_dec_ref(v___x_658_);
lean_dec_ref(v_h_u2082_629_);
lean_dec_ref(v_h_u2081_628_);
v_a_672_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_662_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_662_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
else
{
lean_dec(v_a_639_);
lean_dec_ref(v_h_u2082_629_);
lean_dec_ref(v_h_u2081_628_);
return v___x_640_;
}
}
else
{
lean_dec_ref(v_h_u2082_629_);
lean_dec_ref(v_h_u2081_628_);
return v___x_638_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec_ref(v_h_u2082_629_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v_h_u2081_628_);
return v___x_680_;
}
}
else
{
lean_object* v___x_681_; 
lean_dec_ref(v_h_u2081_628_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v_h_u2082_629_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans___boxed(lean_object* v_h_u2081_682_, lean_object* v_h_u2082_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Meta_mkEqTrans(v_h_u2081_682_, v_h_u2082_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object* v_h_u2081_x3f_690_, lean_object* v_h_u2082_x3f_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_h_698_; 
if (lean_obj_tag(v_h_u2081_x3f_690_) == 0)
{
if (lean_obj_tag(v_h_u2082_x3f_691_) == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v_h_u2082_x3f_691_);
return v___x_701_;
}
else
{
lean_object* v_val_702_; 
v_val_702_ = lean_ctor_get(v_h_u2082_x3f_691_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v_h_u2082_x3f_691_, 1);
v_h_698_ = v_val_702_;
goto v___jp_697_;
}
}
else
{
if (lean_obj_tag(v_h_u2082_x3f_691_) == 0)
{
lean_object* v_val_703_; 
v_val_703_ = lean_ctor_get(v_h_u2081_x3f_690_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_h_u2081_x3f_690_, 1);
v_h_698_ = v_val_703_;
goto v___jp_697_;
}
else
{
lean_object* v_val_704_; lean_object* v_val_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_729_; 
v_val_704_ = lean_ctor_get(v_h_u2081_x3f_690_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v_h_u2081_x3f_690_, 1);
v_val_705_ = lean_ctor_get(v_h_u2082_x3f_691_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_h_u2082_x3f_691_);
if (v_isSharedCheck_729_ == 0)
{
v___x_707_ = v_h_u2082_x3f_691_;
v_isShared_708_ = v_isSharedCheck_729_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_val_705_);
lean_dec(v_h_u2082_x3f_691_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_729_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_mkEqTrans(v_val_704_, v_val_705_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_720_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_720_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_720_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_720_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_a_710_);
v___x_715_ = v___x_707_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_719_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_715_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_del_object(v___x_707_);
v_a_721_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_709_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_709_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v_h_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f___boxed(lean_object* v_h_u2081_x3f_730_, lean_object* v_h_u2082_x3f_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_mkEqTrans_x3f(v_h_u2081_x3f_730_, v_h_u2082_x3f_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
return v_res_737_;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__3(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__2));
v___x_745_ = l_Lean_MessageData_ofFormat(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object* v_h_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_753_ = l_Lean_Expr_isAppOf(v_h_746_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_inc_ref(v_h_746_);
v___x_754_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v___x_756_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_757_ = lean_unsigned_to_nat(4u);
v___x_758_ = l_Lean_Expr_isAppOfArity(v_a_755_, v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_759_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_760_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_761_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_746_, v_a_755_);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_759_, v___x_762_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_763_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_764_ = l_Lean_Expr_appFn_x21(v_a_755_);
v___x_765_ = l_Lean_Expr_appFn_x21(v___x_764_);
v___x_766_ = l_Lean_Expr_appFn_x21(v___x_765_);
v___x_767_ = l_Lean_Expr_appArg_x21(v___x_766_);
lean_dec_ref(v___x_766_);
v___x_768_ = l_Lean_Expr_appArg_x21(v___x_765_);
lean_dec_ref(v___x_765_);
v___x_769_ = l_Lean_Expr_appArg_x21(v___x_764_);
lean_dec_ref(v___x_764_);
v___x_770_ = l_Lean_Expr_appArg_x21(v_a_755_);
lean_dec(v_a_755_);
lean_inc_ref(v___x_767_);
v___x_771_ = l_Lean_Meta_getLevel(v___x_767_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_784_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_784_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_784_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_784_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_776_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v_a_772_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_mkConst(v___x_776_, v___x_778_);
v___x_780_ = l_Lean_mkApp5(v___x_779_, v___x_767_, v___x_769_, v___x_768_, v___x_770_, v_h_746_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_780_);
v___x_782_ = v___x_774_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v___x_768_);
lean_dec_ref(v___x_767_);
lean_dec_ref(v_h_746_);
v_a_785_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_771_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_771_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_746_);
return v___x_754_;
}
}
else
{
lean_object* v___x_793_; 
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_h_746_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm___boxed(lean_object* v_h_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Meta_mkHEqSymm(v_h_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object* v_h_u2081_804_, lean_object* v_h_u2082_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_812_ = l_Lean_Expr_isAppOf(v_h_u2081_804_, v___x_811_);
if (v___x_812_ == 0)
{
uint8_t v___x_813_; 
v___x_813_ = l_Lean_Expr_isAppOf(v_h_u2082_805_, v___x_811_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
lean_inc_ref(v_h_u2081_804_);
v___x_814_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_804_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
lean_inc_ref(v_h_u2082_805_);
v___x_816_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_819_ = lean_unsigned_to_nat(4u);
v___x_820_ = l_Lean_Expr_isAppOfArity(v_a_815_, v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v_a_817_);
lean_dec_ref(v_h_u2082_805_);
v___x_821_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_822_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_823_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_804_, v_a_815_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_821_, v___x_824_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_825_;
}
else
{
uint8_t v___x_826_; 
v___x_826_ = l_Lean_Expr_isAppOfArity(v_a_817_, v___x_818_, v___x_819_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v_a_815_);
lean_dec_ref(v_h_u2081_804_);
v___x_827_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_828_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_829_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_805_, v_a_817_);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_827_, v___x_830_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_832_ = l_Lean_Expr_appFn_x21(v_a_815_);
v___x_833_ = l_Lean_Expr_appFn_x21(v___x_832_);
v___x_834_ = l_Lean_Expr_appFn_x21(v___x_833_);
v___x_835_ = l_Lean_Expr_appArg_x21(v___x_834_);
lean_dec_ref(v___x_834_);
v___x_836_ = l_Lean_Expr_appArg_x21(v___x_833_);
lean_dec_ref(v___x_833_);
v___x_837_ = l_Lean_Expr_appArg_x21(v___x_832_);
lean_dec_ref(v___x_832_);
v___x_838_ = l_Lean_Expr_appArg_x21(v_a_815_);
lean_dec(v_a_815_);
v___x_839_ = l_Lean_Expr_appFn_x21(v_a_817_);
v___x_840_ = l_Lean_Expr_appArg_x21(v___x_839_);
lean_dec_ref(v___x_839_);
v___x_841_ = l_Lean_Expr_appArg_x21(v_a_817_);
lean_dec(v_a_817_);
lean_inc_ref(v___x_835_);
v___x_842_ = l_Lean_Meta_getLevel(v___x_835_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_855_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_855_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_855_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_855_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_847_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v_a_843_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Lean_mkConst(v___x_847_, v___x_849_);
v___x_851_ = l_Lean_mkApp8(v___x_850_, v___x_835_, v___x_837_, v___x_840_, v___x_836_, v___x_838_, v___x_841_, v_h_u2081_804_, v_h_u2082_805_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_851_);
v___x_853_ = v___x_845_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec_ref(v___x_841_);
lean_dec_ref(v___x_840_);
lean_dec_ref(v___x_838_);
lean_dec_ref(v___x_837_);
lean_dec_ref(v___x_836_);
lean_dec_ref(v___x_835_);
lean_dec_ref(v_h_u2082_805_);
lean_dec_ref(v_h_u2081_804_);
v_a_856_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_842_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_842_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
}
else
{
lean_dec(v_a_815_);
lean_dec_ref(v_h_u2082_805_);
lean_dec_ref(v_h_u2081_804_);
return v___x_816_;
}
}
else
{
lean_dec_ref(v_h_u2082_805_);
lean_dec_ref(v_h_u2081_804_);
return v___x_814_;
}
}
else
{
lean_object* v___x_864_; 
lean_dec_ref(v_h_u2082_805_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v_h_u2081_804_);
return v___x_864_;
}
}
else
{
lean_object* v___x_865_; 
lean_dec_ref(v_h_u2081_804_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_h_u2082_805_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans___boxed(lean_object* v_h_u2081_866_, lean_object* v_h_u2082_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_mkHEqTrans(v_h_u2081_866_, v_h_u2082_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
return v_res_873_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__2(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__1));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__4(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__3));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__6(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__5));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object* v_h_885_, uint8_t v_check_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; 
lean_inc_ref(v_h_885_);
v___x_892_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_885_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_895_ = lean_unsigned_to_nat(4u);
v___x_896_ = l_Lean_Expr_isAppOfArity(v_a_893_, v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_a_893_);
v___x_897_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_898_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__2, &l_Lean_Meta_mkEqOfHEq___closed__2_once, _init_l_Lean_Meta_mkEqOfHEq___closed__2);
v___x_899_ = l_Lean_indentExpr(v_h_885_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_897_, v___x_900_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; 
v___x_902_ = l_Lean_Expr_appFn_x21(v_a_893_);
v___x_903_ = l_Lean_Expr_appFn_x21(v___x_902_);
v___x_904_ = l_Lean_Expr_appFn_x21(v___x_903_);
v___x_905_ = l_Lean_Expr_appArg_x21(v___x_904_);
lean_dec_ref(v___x_904_);
v___x_906_ = l_Lean_Expr_appArg_x21(v___x_903_);
lean_dec_ref(v___x_903_);
v___x_907_ = l_Lean_Expr_appArg_x21(v_a_893_);
lean_dec(v_a_893_);
if (v_check_886_ == 0)
{
lean_dec_ref(v___x_902_);
v___y_909_ = v_a_887_;
v___y_910_ = v_a_888_;
v___y_911_ = v_a_889_;
v___y_912_ = v_a_890_;
goto v___jp_908_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = l_Lean_Expr_appArg_x21(v___x_902_);
lean_dec_ref(v___x_902_);
lean_inc_ref(v___x_935_);
lean_inc_ref(v___x_905_);
v___x_936_ = l_Lean_Meta_isExprDefEq(v___x_905_, v___x_935_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; uint8_t v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = lean_unbox(v_a_937_);
lean_dec(v_a_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___x_907_);
lean_dec_ref(v___x_906_);
lean_dec_ref(v_h_885_);
v___x_939_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_940_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__4, &l_Lean_Meta_mkEqOfHEq___closed__4_once, _init_l_Lean_Meta_mkEqOfHEq___closed__4);
v___x_941_ = l_Lean_indentExpr(v___x_905_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__6, &l_Lean_Meta_mkEqOfHEq___closed__6_once, _init_l_Lean_Meta_mkEqOfHEq___closed__6);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Lean_indentExpr(v___x_935_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_939_, v___x_946_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_dec_ref(v___x_935_);
v___y_909_ = v_a_887_;
v___y_910_ = v_a_888_;
v___y_911_ = v_a_889_;
v___y_912_ = v_a_890_;
goto v___jp_908_;
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v___x_906_);
lean_dec_ref(v___x_905_);
lean_dec_ref(v_h_885_);
v_a_956_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_936_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_936_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
v___jp_908_:
{
lean_object* v___x_913_; 
lean_inc_ref(v___x_905_);
v___x_913_ = l_Lean_Meta_getLevel(v___x_905_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_926_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_926_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_918_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v_a_914_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_mkConst(v___x_918_, v___x_920_);
v___x_922_ = l_Lean_mkApp4(v___x_921_, v___x_905_, v___x_906_, v___x_907_, v_h_885_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_922_);
v___x_924_ = v___x_916_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v___x_907_);
lean_dec_ref(v___x_906_);
lean_dec_ref(v___x_905_);
lean_dec_ref(v_h_885_);
v_a_927_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_913_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_913_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_885_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___boxed(lean_object* v_h_964_, lean_object* v_check_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
uint8_t v_check_boxed_971_; lean_object* v_res_972_; 
v_check_boxed_971_ = lean_unbox(v_check_965_);
v_res_972_ = l_Lean_Meta_mkEqOfHEq(v_h_964_, v_check_boxed_971_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqOfEq___closed__2(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__2));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq(lean_object* v_h_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; 
lean_inc_ref(v_h_978_);
v___x_984_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_987_ = lean_unsigned_to_nat(3u);
v___x_988_ = l_Lean_Expr_isAppOfArity(v_a_985_, v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec(v_a_985_);
v___x_989_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_990_ = lean_obj_once(&l_Lean_Meta_mkHEqOfEq___closed__2, &l_Lean_Meta_mkHEqOfEq___closed__2_once, _init_l_Lean_Meta_mkHEqOfEq___closed__2);
v___x_991_ = l_Lean_indentExpr(v_h_978_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_989_, v___x_992_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_994_ = l_Lean_Expr_appFn_x21(v_a_985_);
v___x_995_ = l_Lean_Expr_appFn_x21(v___x_994_);
v___x_996_ = l_Lean_Expr_appArg_x21(v___x_995_);
lean_dec_ref(v___x_995_);
v___x_997_ = l_Lean_Expr_appArg_x21(v___x_994_);
lean_dec_ref(v___x_994_);
v___x_998_ = l_Lean_Expr_appArg_x21(v_a_985_);
lean_dec(v_a_985_);
lean_inc_ref(v___x_996_);
v___x_999_ = l_Lean_Meta_getLevel(v___x_996_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1012_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1004_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_a_1000_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_mkConst(v___x_1004_, v___x_1006_);
v___x_1008_ = l_Lean_mkApp4(v___x_1007_, v___x_996_, v___x_997_, v___x_998_, v_h_978_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1008_);
v___x_1010_ = v___x_1002_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v___x_998_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v___x_996_);
lean_dec_ref(v_h_978_);
v_a_1013_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_999_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_999_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_978_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq___boxed(lean_object* v_h_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Meta_mkHEqOfEq(v_h_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f(lean_object* v_e_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1029_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_1030_ = lean_unsigned_to_nat(2u);
v___x_1031_ = l_Lean_Expr_isAppOfArity(v_e_1028_, v___x_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_box(0);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = l_Lean_Expr_appArg_x21(v_e_1028_);
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f___boxed(lean_object* v_e_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_isRefl_x3f(v_e_1035_);
lean_dec_ref(v_e_1035_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___f_1044_; lean_object* v___x_854__overap_1045_; lean_object* v___x_1046_; 
v___f_1044_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_854__overap_1045_ = lean_panic_fn_borrowed(v___f_1044_, v_msg_1038_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
v___x_1046_ = lean_apply_5(v___x_854__overap_1045_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, lean_box(0));
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___boxed(lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__2(void){
_start:
{
lean_object* v___x_1057_; lean_object* v_dummy_1058_; 
v___x_1057_ = lean_box(0);
v_dummy_1058_ = l_Lean_Expr_sort___override(v___x_1057_);
return v_dummy_1058_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__6(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__5));
v___x_1063_ = lean_unsigned_to_nat(48u);
v___x_1064_ = lean_unsigned_to_nat(212u);
v___x_1065_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__4));
v___x_1066_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_1067_ = l_mkPanicMessageWithDecl(v___x_1066_, v___x_1065_, v___x_1064_, v___x_1063_, v___x_1062_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__9(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = l_Lean_Expr_bvar___override(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__10(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = lean_mk_empty_array_with_capacity(v___x_1074_);
v___x_1076_ = lean_array_push(v___x_1075_, v___x_1073_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__15(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1083_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__5));
v___x_1084_ = lean_unsigned_to_nat(49u);
v___x_1085_ = lean_unsigned_to_nat(209u);
v___x_1086_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__4));
v___x_1087_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_1088_ = l_mkPanicMessageWithDecl(v___x_1087_, v___x_1086_, v___x_1085_, v___x_1084_, v___x_1083_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f(lean_object* v_e_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1145_ = lean_unsigned_to_nat(6u);
v___x_1146_ = l_Lean_Expr_isAppOfArity(v_e_1089_, v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
v___y_1099_ = v_a_1090_;
v___y_1100_ = v_a_1091_;
v___y_1101_ = v_a_1092_;
v___y_1102_ = v_a_1093_;
goto v___jp_1098_;
}
else
{
lean_object* v_dummy_1147_; lean_object* v_nargs_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_dummy_1147_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_1148_ = l_Lean_Expr_getAppNumArgs(v_e_1089_);
lean_inc(v_nargs_1148_);
v___x_1149_ = lean_mk_array(v_nargs_1148_, v_dummy_1147_);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_sub(v_nargs_1148_, v___x_1150_);
lean_dec(v_nargs_1148_);
lean_inc_ref(v_e_1089_);
v___x_1152_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1089_, v___x_1149_, v___x_1151_);
v___x_1153_ = lean_array_get_size(v___x_1152_);
v___x_1154_ = lean_nat_dec_eq(v___x_1153_, v___x_1145_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref(v___x_1152_);
v___x_1155_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__15, &l_Lean_Meta_congrArg_x3f___closed__15_once, _init_l_Lean_Meta_congrArg_x3f___closed__15);
v___x_1156_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v___x_1155_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_dec_ref_known(v___x_1156_, 1);
v___y_1099_ = v_a_1090_;
v___y_1100_ = v_a_1091_;
v___y_1101_ = v_a_1092_;
v___y_1102_ = v_a_1093_;
goto v___jp_1098_;
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v_e_1089_);
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref(v_e_1089_);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = lean_array_fget(v___x_1152_, v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(4u);
v___x_1168_ = lean_array_fget(v___x_1152_, v___x_1167_);
v___x_1169_ = lean_unsigned_to_nat(5u);
v___x_1170_ = lean_array_fget(v___x_1152_, v___x_1169_);
lean_dec_ref(v___x_1152_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1168_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1166_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
v___jp_1095_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
v___jp_1098_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1104_ = lean_unsigned_to_nat(6u);
v___x_1105_ = l_Lean_Expr_isAppOfArity(v_e_1089_, v___x_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v_e_1089_);
goto v___jp_1095_;
}
else
{
lean_object* v_dummy_1106_; lean_object* v_nargs_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_dummy_1106_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_1107_ = l_Lean_Expr_getAppNumArgs(v_e_1089_);
lean_inc(v_nargs_1107_);
v___x_1108_ = lean_mk_array(v_nargs_1107_, v_dummy_1106_);
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_nat_sub(v_nargs_1107_, v___x_1109_);
lean_dec(v_nargs_1107_);
v___x_1111_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1089_, v___x_1108_, v___x_1110_);
v___x_1112_ = lean_array_get_size(v___x_1111_);
v___x_1113_ = lean_nat_dec_eq(v___x_1112_, v___x_1104_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref(v___x_1111_);
v___x_1114_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__6, &l_Lean_Meta_congrArg_x3f___closed__6_once, _init_l_Lean_Meta_congrArg_x3f___closed__6);
v___x_1115_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v___x_1114_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_dec_ref_known(v___x_1115_, 1);
goto v___jp_1095_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v_00_u03b1_x27_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_f_x27_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_array_fget(v___x_1111_, v___x_1124_);
v___x_1126_ = lean_array_fget(v___x_1111_, v___x_1109_);
v___x_1127_ = lean_unsigned_to_nat(4u);
v___x_1128_ = lean_array_fget(v___x_1111_, v___x_1127_);
v___x_1129_ = lean_unsigned_to_nat(5u);
v___x_1130_ = lean_array_fget(v___x_1111_, v___x_1129_);
lean_dec_ref(v___x_1111_);
v___x_1131_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1132_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1133_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__10, &l_Lean_Meta_congrArg_x3f___closed__10_once, _init_l_Lean_Meta_congrArg_x3f___closed__10);
v___x_1134_ = l_Lean_Expr_beta(v___x_1126_, v___x_1133_);
v___x_1135_ = 0;
v_00_u03b1_x27_1136_ = l_Lean_Expr_forallE___override(v___x_1131_, v___x_1125_, v___x_1134_, v___x_1135_);
v___x_1137_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__12));
v___x_1138_ = l_Lean_Expr_app___override(v___x_1132_, v___x_1130_);
lean_inc_ref(v_00_u03b1_x27_1136_);
v_f_x27_1139_ = l_Lean_Expr_lam___override(v___x_1137_, v_00_u03b1_x27_1136_, v___x_1138_, v___x_1135_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_f_x27_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1128_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_00_u03b1_x27_1136_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___boxed(lean_object* v_e_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_congrArg_x3f(v_e_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1181_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__2(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_Meta_mkCongrArg___closed__1));
v___x_1186_ = l_Lean_MessageData_ofFormat(v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object* v_f_1187_, lean_object* v_h_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Meta_isRefl_x3f(v_h_1188_);
if (lean_obj_tag(v___x_1194_) == 1)
{
lean_object* v_val_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec_ref(v_h_1188_);
v_val_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = l_Lean_Expr_app___override(v_f_1187_, v_val_1195_);
v___x_1197_ = l_Lean_Meta_mkEqRefl(v___x_1196_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; 
lean_dec(v___x_1194_);
lean_inc_ref(v_h_1188_);
v___x_1198_ = l_Lean_Meta_congrArg_x3f(v_h_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
if (lean_obj_tag(v_a_1199_) == 1)
{
lean_object* v_val_1200_; lean_object* v_snd_1201_; lean_object* v_fst_1202_; lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v_h_1188_);
v_val_1200_ = lean_ctor_get(v_a_1199_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v_a_1199_, 1);
v_snd_1201_ = lean_ctor_get(v_val_1200_, 1);
lean_inc(v_snd_1201_);
v_fst_1202_ = lean_ctor_get(v_val_1200_, 0);
lean_inc(v_fst_1202_);
lean_dec(v_val_1200_);
v_fst_1203_ = lean_ctor_get(v_snd_1201_, 0);
lean_inc(v_fst_1203_);
v_snd_1204_ = lean_ctor_get(v_snd_1201_, 1);
lean_inc(v_snd_1204_);
lean_dec(v_snd_1201_);
v___x_1205_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_mk_empty_array_with_capacity(v___x_1206_);
v___x_1208_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__10, &l_Lean_Meta_congrArg_x3f___closed__10_once, _init_l_Lean_Meta_congrArg_x3f___closed__10);
v___x_1209_ = l_Lean_Expr_beta(v_fst_1203_, v___x_1208_);
v___x_1210_ = lean_array_push(v___x_1207_, v___x_1209_);
v___x_1211_ = l_Lean_Expr_beta(v_f_1187_, v___x_1210_);
v___x_1212_ = 0;
v___x_1213_ = l_Lean_Expr_lam___override(v___x_1205_, v_fst_1202_, v___x_1211_, v___x_1212_);
v_f_1187_ = v___x_1213_;
v_h_1188_ = v_snd_1204_;
goto _start;
}
else
{
lean_object* v___x_1215_; 
lean_dec(v_a_1199_);
lean_inc_ref(v_h_1188_);
v___x_1215_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
lean_inc_ref(v_f_1187_);
v___x_1217_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_f_1187_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
if (lean_obj_tag(v_a_1218_) == 7)
{
lean_object* v_binderType_1225_; lean_object* v_body_1226_; uint8_t v___x_1227_; 
v_binderType_1225_ = lean_ctor_get(v_a_1218_, 1);
v_body_1226_ = lean_ctor_get(v_a_1218_, 2);
v___x_1227_ = l_Lean_Expr_hasLooseBVars(v_body_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
lean_inc_ref(v_body_1226_);
lean_inc_ref(v_binderType_1225_);
lean_dec_ref_known(v_a_1218_, 3);
v___x_1228_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1229_ = lean_unsigned_to_nat(3u);
v___x_1230_ = l_Lean_Expr_isAppOfArity(v_a_1216_, v___x_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec_ref(v_body_1226_);
lean_dec_ref(v_binderType_1225_);
lean_dec_ref(v_f_1187_);
v___x_1231_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1232_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1233_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1188_, v_a_1216_);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1231_, v___x_1234_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = l_Lean_Expr_appFn_x21(v_a_1216_);
v___x_1237_ = l_Lean_Expr_appArg_x21(v___x_1236_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = l_Lean_Expr_appArg_x21(v_a_1216_);
lean_dec(v_a_1216_);
lean_inc_ref(v_binderType_1225_);
v___x_1239_ = l_Lean_Meta_getLevel(v_binderType_1225_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
lean_inc_ref(v_body_1226_);
v___x_1241_ = l_Lean_Meta_getLevel(v_body_1226_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1255_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1255_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1255_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1246_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1242_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_a_1240_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = l_Lean_mkConst(v___x_1246_, v___x_1249_);
v___x_1251_ = l_Lean_mkApp6(v___x_1250_, v_binderType_1225_, v_body_1226_, v___x_1237_, v___x_1238_, v_f_1187_, v_h_1188_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1251_);
v___x_1253_ = v___x_1244_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_a_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v___x_1237_);
lean_dec_ref(v_body_1226_);
lean_dec_ref(v_binderType_1225_);
lean_dec_ref(v_h_1188_);
lean_dec_ref(v_f_1187_);
v_a_1256_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1241_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1241_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v___x_1238_);
lean_dec_ref(v___x_1237_);
lean_dec_ref(v_body_1226_);
lean_dec_ref(v_binderType_1225_);
lean_dec_ref(v_h_1188_);
lean_dec_ref(v_f_1187_);
v_a_1264_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1239_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1239_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
else
{
lean_dec(v_a_1216_);
lean_dec_ref(v_h_1188_);
goto v___jp_1219_;
}
}
else
{
lean_dec(v_a_1216_);
lean_dec_ref(v_h_1188_);
goto v___jp_1219_;
}
v___jp_1219_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1220_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1221_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1222_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_f_1187_, v_a_1218_);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1220_, v___x_1223_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
return v___x_1224_;
}
}
else
{
lean_dec(v_a_1216_);
lean_dec_ref(v_h_1188_);
lean_dec_ref(v_f_1187_);
return v___x_1217_;
}
}
else
{
lean_dec_ref(v_h_1188_);
lean_dec_ref(v_f_1187_);
return v___x_1215_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_h_1188_);
lean_dec_ref(v_f_1187_);
v_a_1272_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1198_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1198_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___boxed(lean_object* v_f_1280_, lean_object* v_h_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Meta_mkCongrArg(v_f_1280_, v_h_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1287_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__0(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1289_ = lean_unsigned_to_nat(2u);
v___x_1290_ = lean_mk_empty_array_with_capacity(v___x_1289_);
v___x_1291_ = lean_array_push(v___x_1290_, v___x_1288_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__3(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_Meta_mkCongrFun___closed__2));
v___x_1296_ = l_Lean_MessageData_ofFormat(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object* v_h_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Meta_isRefl_x3f(v_h_1297_);
if (lean_obj_tag(v___x_1304_) == 1)
{
lean_object* v_val_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec_ref(v_h_1297_);
v_val_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_val_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = l_Lean_Expr_app___override(v_val_1305_, v_a_1298_);
v___x_1307_ = l_Lean_Meta_mkEqRefl(v___x_1306_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; 
lean_dec(v___x_1304_);
lean_inc_ref(v_h_1297_);
v___x_1308_ = l_Lean_Meta_congrArg_x3f(v_h_1297_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
if (lean_obj_tag(v_a_1309_) == 1)
{
lean_object* v_val_1310_; lean_object* v_snd_1311_; lean_object* v_fst_1312_; lean_object* v_fst_1313_; lean_object* v_snd_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_h_1297_);
v_val_1310_ = lean_ctor_get(v_a_1309_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v_a_1309_, 1);
v_snd_1311_ = lean_ctor_get(v_val_1310_, 1);
lean_inc(v_snd_1311_);
v_fst_1312_ = lean_ctor_get(v_val_1310_, 0);
lean_inc(v_fst_1312_);
lean_dec(v_val_1310_);
v_fst_1313_ = lean_ctor_get(v_snd_1311_, 0);
lean_inc(v_fst_1313_);
v_snd_1314_ = lean_ctor_get(v_snd_1311_, 1);
lean_inc(v_snd_1314_);
lean_dec(v_snd_1311_);
v___x_1315_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1316_ = lean_obj_once(&l_Lean_Meta_mkCongrFun___closed__0, &l_Lean_Meta_mkCongrFun___closed__0_once, _init_l_Lean_Meta_mkCongrFun___closed__0);
v___x_1317_ = lean_array_push(v___x_1316_, v_a_1298_);
v___x_1318_ = l_Lean_Expr_beta(v_fst_1313_, v___x_1317_);
v___x_1319_ = 0;
v___x_1320_ = l_Lean_Expr_lam___override(v___x_1315_, v_fst_1312_, v___x_1318_, v___x_1319_);
v___x_1321_ = l_Lean_Meta_mkCongrArg(v___x_1320_, v_snd_1314_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; 
lean_dec(v_a_1309_);
lean_inc_ref(v_h_1297_);
v___x_1322_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_1297_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1325_ = lean_unsigned_to_nat(3u);
v___x_1326_ = l_Lean_Expr_isAppOfArity(v_a_1323_, v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v_a_1298_);
v___x_1327_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1328_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1329_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1297_, v_a_1323_);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1327_, v___x_1330_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1332_ = l_Lean_Expr_appFn_x21(v_a_1323_);
v___x_1333_ = l_Lean_Expr_appFn_x21(v___x_1332_);
v___x_1334_ = l_Lean_Expr_appArg_x21(v___x_1333_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = l_Lean_Expr_appArg_x21(v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1336_ = l_Lean_Expr_appArg_x21(v_a_1323_);
v___x_1337_ = l_Lean_Meta_whnfD(v___x_1334_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
if (lean_obj_tag(v_a_1338_) == 7)
{
lean_object* v_binderName_1339_; lean_object* v_binderType_1340_; lean_object* v_body_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_a_1323_);
v_binderName_1339_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_binderName_1339_);
v_binderType_1340_ = lean_ctor_get(v_a_1338_, 1);
lean_inc_ref_n(v_binderType_1340_, 3);
v_body_1341_ = lean_ctor_get(v_a_1338_, 2);
lean_inc_ref(v_body_1341_);
lean_dec_ref_known(v_a_1338_, 3);
v___x_1342_ = 0;
v___x_1343_ = l_Lean_mkLambda(v_binderName_1339_, v___x_1342_, v_binderType_1340_, v_body_1341_);
v___x_1344_ = l_Lean_Meta_getLevel(v_binderType_1340_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
lean_inc_ref(v_a_1298_);
lean_inc_ref(v___x_1343_);
v___x_1346_ = l_Lean_Expr_app___override(v___x_1343_, v_a_1298_);
v___x_1347_ = l_Lean_Meta_getLevel(v___x_1346_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1361_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1361_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1361_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1352_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_a_1348_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1345_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_mkConst(v___x_1352_, v___x_1355_);
v___x_1357_ = l_Lean_mkApp6(v___x_1356_, v_binderType_1340_, v___x_1343_, v___x_1335_, v___x_1336_, v_h_1297_, v_a_1298_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1357_);
v___x_1359_ = v___x_1350_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_a_1345_);
lean_dec_ref(v___x_1343_);
lean_dec_ref(v_binderType_1340_);
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1335_);
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_h_1297_);
v_a_1362_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1347_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1347_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v___x_1343_);
lean_dec_ref(v_binderType_1340_);
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1335_);
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_h_1297_);
v_a_1370_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1344_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1344_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec(v_a_1338_);
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1335_);
lean_dec_ref(v_a_1298_);
v___x_1378_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1379_ = lean_obj_once(&l_Lean_Meta_mkCongrFun___closed__3, &l_Lean_Meta_mkCongrFun___closed__3_once, _init_l_Lean_Meta_mkCongrFun___closed__3);
v___x_1380_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1297_, v_a_1323_);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1378_, v___x_1381_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1382_;
}
}
else
{
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1335_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_h_1297_);
return v___x_1337_;
}
}
}
else
{
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_h_1297_);
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_h_1297_);
v_a_1383_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1308_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1308_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___boxed(lean_object* v_h_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Meta_mkCongrFun(v_h_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object* v_h_u2081_1402_, lean_object* v_h_u2082_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_1410_ = l_Lean_Expr_isAppOf(v_h_u2081_1402_, v___x_1409_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = l_Lean_Expr_isAppOf(v_h_u2082_1403_, v___x_1409_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_inc_ref(v_h_u2081_1402_);
v___x_1412_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_1402_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
lean_inc_ref(v_h_u2082_1403_);
v___x_1414_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1417_ = lean_unsigned_to_nat(3u);
v___x_1418_ = l_Lean_Expr_isAppOfArity(v_a_1413_, v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec(v_a_1415_);
lean_dec_ref(v_h_u2082_1403_);
v___x_1419_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1420_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1421_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1402_, v_a_1413_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1419_, v___x_1422_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = l_Lean_Expr_isAppOfArity(v_a_1415_, v___x_1416_, v___x_1417_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec(v_a_1413_);
lean_dec_ref(v_h_u2081_1402_);
v___x_1425_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1426_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1427_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_1403_, v_a_1415_);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1425_, v___x_1428_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1430_ = l_Lean_Expr_appFn_x21(v_a_1413_);
v___x_1431_ = l_Lean_Expr_appFn_x21(v___x_1430_);
v___x_1432_ = l_Lean_Expr_appArg_x21(v___x_1431_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = l_Lean_Expr_appArg_x21(v___x_1430_);
lean_dec_ref(v___x_1430_);
v___x_1434_ = l_Lean_Expr_appArg_x21(v_a_1413_);
v___x_1435_ = l_Lean_Expr_appFn_x21(v_a_1415_);
v___x_1436_ = l_Lean_Expr_appFn_x21(v___x_1435_);
v___x_1437_ = l_Lean_Expr_appArg_x21(v___x_1436_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = l_Lean_Expr_appArg_x21(v___x_1435_);
lean_dec_ref(v___x_1435_);
v___x_1439_ = l_Lean_Expr_appArg_x21(v_a_1415_);
lean_dec(v_a_1415_);
v___x_1440_ = l_Lean_Meta_whnfD(v___x_1432_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
if (lean_obj_tag(v_a_1441_) == 7)
{
lean_object* v_body_1448_; uint8_t v___x_1449_; 
v_body_1448_ = lean_ctor_get(v_a_1441_, 2);
lean_inc_ref(v_body_1448_);
lean_dec_ref_known(v_a_1441_, 3);
v___x_1449_ = l_Lean_Expr_hasLooseBVars(v_body_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec(v_a_1413_);
lean_inc_ref(v___x_1437_);
v___x_1450_ = l_Lean_Meta_getLevel(v___x_1437_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
lean_inc_ref(v_body_1448_);
v___x_1452_ = l_Lean_Meta_getLevel(v_body_1448_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1466_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1457_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1458_ = lean_box(0);
v___x_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_a_1453_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_a_1451_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_mkConst(v___x_1457_, v___x_1460_);
v___x_1462_ = l_Lean_mkApp8(v___x_1461_, v___x_1437_, v_body_1448_, v___x_1433_, v___x_1434_, v___x_1438_, v___x_1439_, v_h_u2081_1402_, v_h_u2082_1403_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1462_);
v___x_1464_ = v___x_1455_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_a_1451_);
lean_dec_ref(v_body_1448_);
lean_dec_ref(v___x_1439_);
lean_dec_ref(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_h_u2082_1403_);
lean_dec_ref(v_h_u2081_1402_);
v_a_1467_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1452_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1452_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v_body_1448_);
lean_dec_ref(v___x_1439_);
lean_dec_ref(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_h_u2082_1403_);
lean_dec_ref(v_h_u2081_1402_);
v_a_1475_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1450_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1450_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_dec_ref(v_body_1448_);
lean_dec_ref(v___x_1439_);
lean_dec_ref(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_h_u2082_1403_);
goto v___jp_1442_;
}
}
else
{
lean_dec(v_a_1441_);
lean_dec_ref(v___x_1439_);
lean_dec_ref(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_h_u2082_1403_);
goto v___jp_1442_;
}
v___jp_1442_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1443_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1444_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1445_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1402_, v_a_1413_);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1443_, v___x_1446_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1447_;
}
}
else
{
lean_dec_ref(v___x_1439_);
lean_dec_ref(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec(v_a_1413_);
lean_dec_ref(v_h_u2082_1403_);
lean_dec_ref(v_h_u2081_1402_);
return v___x_1440_;
}
}
}
}
else
{
lean_dec(v_a_1413_);
lean_dec_ref(v_h_u2082_1403_);
lean_dec_ref(v_h_u2081_1402_);
return v___x_1414_;
}
}
else
{
lean_dec_ref(v_h_u2082_1403_);
lean_dec_ref(v_h_u2081_1402_);
return v___x_1412_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = l_Lean_Expr_appArg_x21(v_h_u2082_1403_);
lean_dec_ref(v_h_u2082_1403_);
v___x_1484_ = l_Lean_Meta_mkCongrFun(v_h_u2081_1402_, v___x_1483_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1484_;
}
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = l_Lean_Expr_appArg_x21(v_h_u2081_1402_);
lean_dec_ref(v_h_u2081_1402_);
v___x_1486_ = l_Lean_Meta_mkCongrArg(v___x_1485_, v_h_u2082_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr___boxed(lean_object* v_h_u2081_1487_, lean_object* v_h_u2082_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Meta_mkCongr(v_h_u2081_1487_, v_h_u2082_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(lean_object* v_e_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lean_Expr_hasMVar(v_e_1495_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_e_1495_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v_mctx_1501_; lean_object* v___x_1502_; lean_object* v_fst_1503_; lean_object* v_snd_1504_; lean_object* v___x_1505_; lean_object* v_cache_1506_; lean_object* v_zetaDeltaFVarIds_1507_; lean_object* v_postponed_1508_; lean_object* v_diag_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1518_; 
v___x_1500_ = lean_st_ref_get(v___y_1496_);
v_mctx_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_ref(v_mctx_1501_);
lean_dec(v___x_1500_);
v___x_1502_ = l_Lean_instantiateMVarsCore(v_mctx_1501_, v_e_1495_);
v_fst_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_fst_1503_);
v_snd_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_snd_1504_);
lean_dec_ref(v___x_1502_);
v___x_1505_ = lean_st_ref_take(v___y_1496_);
v_cache_1506_ = lean_ctor_get(v___x_1505_, 1);
v_zetaDeltaFVarIds_1507_ = lean_ctor_get(v___x_1505_, 2);
v_postponed_1508_ = lean_ctor_get(v___x_1505_, 3);
v_diag_1509_ = lean_ctor_get(v___x_1505_, 4);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; 
v_unused_1519_ = lean_ctor_get(v___x_1505_, 0);
lean_dec(v_unused_1519_);
v___x_1511_ = v___x_1505_;
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_diag_1509_);
lean_inc(v_postponed_1508_);
lean_inc(v_zetaDeltaFVarIds_1507_);
lean_inc(v_cache_1506_);
lean_dec(v___x_1505_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v_snd_1504_);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_snd_1504_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_cache_1506_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_zetaDeltaFVarIds_1507_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_postponed_1508_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_diag_1509_);
v___x_1514_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_st_ref_put(v___y_1496_, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_fst_1503_);
return v___x_1516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg___boxed(lean_object* v_e_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v_e_1520_, v___y_1521_);
lean_dec(v___y_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(lean_object* v_e_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v_e_1524_, v___y_1526_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___boxed(lean_object* v_e_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(v_e_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_, lean_object* v_x_1541_){
_start:
{
lean_object* v_ks_1542_; lean_object* v_vs_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1567_; 
v_ks_1542_ = lean_ctor_get(v_x_1538_, 0);
v_vs_1543_ = lean_ctor_get(v_x_1538_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_x_1538_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1545_ = v_x_1538_;
v_isShared_1546_ = v_isSharedCheck_1567_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_vs_1543_);
lean_inc(v_ks_1542_);
lean_dec(v_x_1538_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1567_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = lean_array_get_size(v_ks_1542_);
v___x_1548_ = lean_nat_dec_lt(v_x_1539_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_dec(v_x_1539_);
v___x_1549_ = lean_array_push(v_ks_1542_, v_x_1540_);
v___x_1550_ = lean_array_push(v_vs_1543_, v_x_1541_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v___x_1550_);
lean_ctor_set(v___x_1545_, 0, v___x_1549_);
v___x_1552_ = v___x_1545_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
else
{
lean_object* v_k_x27_1554_; uint8_t v___x_1555_; 
v_k_x27_1554_ = lean_array_fget_borrowed(v_ks_1542_, v_x_1539_);
v___x_1555_ = l_Lean_instBEqMVarId_beq(v_x_1540_, v_k_x27_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1557_; 
if (v_isShared_1546_ == 0)
{
v___x_1557_ = v___x_1545_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_ks_1542_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_vs_1543_);
v___x_1557_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = lean_nat_add(v_x_1539_, v___x_1558_);
lean_dec(v_x_1539_);
v_x_1538_ = v___x_1557_;
v_x_1539_ = v___x_1559_;
goto _start;
}
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1562_ = lean_array_fset(v_ks_1542_, v_x_1539_, v_x_1540_);
v___x_1563_ = lean_array_fset(v_vs_1543_, v_x_1539_, v_x_1541_);
lean_dec(v_x_1539_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v___x_1563_);
lean_ctor_set(v___x_1545_, 0, v___x_1562_);
v___x_1565_ = v___x_1545_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_1568_, lean_object* v_k_1569_, lean_object* v_v_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_1568_, v___x_1571_, v_k_1569_, v_v_1570_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1574_, size_t v_x_1575_, size_t v_x_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_){
_start:
{
if (lean_obj_tag(v_x_1574_) == 0)
{
lean_object* v_es_1579_; size_t v___x_1580_; size_t v___x_1581_; lean_object* v_j_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_es_1579_ = lean_ctor_get(v_x_1574_, 0);
v___x_1580_ = ((size_t)31ULL);
v___x_1581_ = lean_usize_land(v_x_1575_, v___x_1580_);
v_j_1582_ = lean_usize_to_nat(v___x_1581_);
v___x_1583_ = lean_array_get_size(v_es_1579_);
v___x_1584_ = lean_nat_dec_lt(v_j_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_dec(v_j_1582_);
lean_dec(v_x_1578_);
lean_dec(v_x_1577_);
return v_x_1574_;
}
else
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1623_; 
lean_inc_ref(v_es_1579_);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v_x_1574_, 0);
lean_dec(v_unused_1624_);
v___x_1586_ = v_x_1574_;
v_isShared_1587_ = v_isSharedCheck_1623_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v_x_1574_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1623_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_v_1588_; lean_object* v___x_1589_; lean_object* v_xs_x27_1590_; lean_object* v___y_1592_; 
v_v_1588_ = lean_array_fget(v_es_1579_, v_j_1582_);
v___x_1589_ = lean_box(0);
v_xs_x27_1590_ = lean_array_fset(v_es_1579_, v_j_1582_, v___x_1589_);
switch(lean_obj_tag(v_v_1588_))
{
case 0:
{
lean_object* v_key_1597_; lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1608_; 
v_key_1597_ = lean_ctor_get(v_v_1588_, 0);
v_val_1598_ = lean_ctor_get(v_v_1588_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_v_1588_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1600_ = v_v_1588_;
v_isShared_1601_ = v_isSharedCheck_1608_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_inc(v_key_1597_);
lean_dec(v_v_1588_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1608_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
uint8_t v___x_1602_; 
v___x_1602_ = l_Lean_instBEqMVarId_beq(v_x_1577_, v_key_1597_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_del_object(v___x_1600_);
v___x_1603_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1597_, v_val_1598_, v_x_1577_, v_x_1578_);
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___y_1592_ = v___x_1604_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1606_; 
lean_dec(v_val_1598_);
lean_dec(v_key_1597_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v_x_1578_);
lean_ctor_set(v___x_1600_, 0, v_x_1577_);
v___x_1606_ = v___x_1600_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_x_1577_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_x_1578_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v___y_1592_ = v___x_1606_;
goto v___jp_1591_;
}
}
}
}
case 1:
{
lean_object* v_node_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1621_; 
v_node_1609_ = lean_ctor_get(v_v_1588_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_v_1588_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1611_ = v_v_1588_;
v_isShared_1612_ = v_isSharedCheck_1621_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_node_1609_);
lean_dec(v_v_1588_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1621_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
size_t v___x_1613_; size_t v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1613_ = ((size_t)5ULL);
v___x_1614_ = lean_usize_shift_right(v_x_1575_, v___x_1613_);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_x_1576_, v___x_1615_);
v___x_1617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_node_1609_, v___x_1614_, v___x_1616_, v_x_1577_, v_x_1578_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1617_);
v___x_1619_ = v___x_1611_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
v___y_1592_ = v___x_1619_;
goto v___jp_1591_;
}
}
}
default: 
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v_x_1577_);
lean_ctor_set(v___x_1622_, 1, v_x_1578_);
v___y_1592_ = v___x_1622_;
goto v___jp_1591_;
}
}
v___jp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = lean_array_fset(v_xs_x27_1590_, v_j_1582_, v___y_1592_);
lean_dec(v_j_1582_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1593_);
v___x_1595_ = v___x_1586_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
else
{
lean_object* v_ks_1625_; lean_object* v_vs_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1644_; 
v_ks_1625_ = lean_ctor_get(v_x_1574_, 0);
v_vs_1626_ = lean_ctor_get(v_x_1574_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1628_ = v_x_1574_;
v_isShared_1629_ = v_isSharedCheck_1644_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_vs_1626_);
lean_inc(v_ks_1625_);
lean_dec(v_x_1574_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1644_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_ks_1625_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_vs_1626_);
v___x_1631_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v_newNode_1632_; size_t v___x_1633_; uint8_t v___x_1634_; 
v_newNode_1632_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v___x_1631_, v_x_1577_, v_x_1578_);
v___x_1633_ = ((size_t)7ULL);
v___x_1634_ = lean_usize_dec_le(v___x_1633_, v_x_1576_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1635_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1632_);
v___x_1636_ = lean_unsigned_to_nat(4u);
v___x_1637_ = lean_nat_dec_lt(v___x_1635_, v___x_1636_);
lean_dec(v___x_1635_);
if (v___x_1637_ == 0)
{
lean_object* v_ks_1638_; lean_object* v_vs_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_ks_1638_ = lean_ctor_get(v_newNode_1632_, 0);
lean_inc_ref(v_ks_1638_);
v_vs_1639_ = lean_ctor_get(v_newNode_1632_, 1);
lean_inc_ref(v_vs_1639_);
lean_dec_ref(v_newNode_1632_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_1642_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1576_, v_ks_1638_, v_vs_1639_, v___x_1640_, v___x_1641_);
lean_dec_ref(v_vs_1639_);
lean_dec_ref(v_ks_1638_);
return v___x_1642_;
}
else
{
return v_newNode_1632_;
}
}
else
{
return v_newNode_1632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_1645_, lean_object* v_keys_1646_, lean_object* v_vals_1647_, lean_object* v_i_1648_, lean_object* v_entries_1649_){
_start:
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = lean_array_get_size(v_keys_1646_);
v___x_1651_ = lean_nat_dec_lt(v_i_1648_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec(v_i_1648_);
return v_entries_1649_;
}
else
{
lean_object* v_k_1652_; lean_object* v_v_1653_; uint64_t v___x_1654_; size_t v_h_1655_; size_t v___x_1656_; lean_object* v___x_1657_; size_t v___x_1658_; size_t v___x_1659_; size_t v___x_1660_; size_t v_h_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_k_1652_ = lean_array_fget_borrowed(v_keys_1646_, v_i_1648_);
v_v_1653_ = lean_array_fget_borrowed(v_vals_1647_, v_i_1648_);
v___x_1654_ = l_Lean_instHashableMVarId_hash(v_k_1652_);
v_h_1655_ = lean_uint64_to_usize(v___x_1654_);
v___x_1656_ = ((size_t)5ULL);
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = ((size_t)1ULL);
v___x_1659_ = lean_usize_sub(v_depth_1645_, v___x_1658_);
v___x_1660_ = lean_usize_mul(v___x_1656_, v___x_1659_);
v_h_1661_ = lean_usize_shift_right(v_h_1655_, v___x_1660_);
v___x_1662_ = lean_nat_add(v_i_1648_, v___x_1657_);
lean_dec(v_i_1648_);
lean_inc(v_v_1653_);
lean_inc(v_k_1652_);
v___x_1663_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_entries_1649_, v_h_1661_, v_depth_1645_, v_k_1652_, v_v_1653_);
v_i_1648_ = v___x_1662_;
v_entries_1649_ = v___x_1663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1665_, lean_object* v_keys_1666_, lean_object* v_vals_1667_, lean_object* v_i_1668_, lean_object* v_entries_1669_){
_start:
{
size_t v_depth_boxed_1670_; lean_object* v_res_1671_; 
v_depth_boxed_1670_ = lean_unbox_usize(v_depth_1665_);
lean_dec(v_depth_1665_);
v_res_1671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_1670_, v_keys_1666_, v_vals_1667_, v_i_1668_, v_entries_1669_);
lean_dec_ref(v_vals_1667_);
lean_dec_ref(v_keys_1666_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_){
_start:
{
size_t v_x_1971__boxed_1677_; size_t v_x_1972__boxed_1678_; lean_object* v_res_1679_; 
v_x_1971__boxed_1677_ = lean_unbox_usize(v_x_1673_);
lean_dec(v_x_1673_);
v_x_1972__boxed_1678_ = lean_unbox_usize(v_x_1674_);
lean_dec(v_x_1674_);
v_res_1679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1672_, v_x_1971__boxed_1677_, v_x_1972__boxed_1678_, v_x_1675_, v_x_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
uint64_t v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
v___x_1683_ = l_Lean_instHashableMVarId_hash(v_x_1681_);
v___x_1684_ = lean_uint64_to_usize(v___x_1683_);
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1680_, v___x_1684_, v___x_1685_, v_x_1681_, v_x_1682_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(lean_object* v_mvarId_1687_, lean_object* v_val_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v_mctx_1692_; lean_object* v_cache_1693_; lean_object* v_zetaDeltaFVarIds_1694_; lean_object* v_postponed_1695_; lean_object* v_diag_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1725_; 
v___x_1691_ = lean_st_ref_take(v___y_1689_);
v_mctx_1692_ = lean_ctor_get(v___x_1691_, 0);
v_cache_1693_ = lean_ctor_get(v___x_1691_, 1);
v_zetaDeltaFVarIds_1694_ = lean_ctor_get(v___x_1691_, 2);
v_postponed_1695_ = lean_ctor_get(v___x_1691_, 3);
v_diag_1696_ = lean_ctor_get(v___x_1691_, 4);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1698_ = v___x_1691_;
v_isShared_1699_ = v_isSharedCheck_1725_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_diag_1696_);
lean_inc(v_postponed_1695_);
lean_inc(v_zetaDeltaFVarIds_1694_);
lean_inc(v_cache_1693_);
lean_inc(v_mctx_1692_);
lean_dec(v___x_1691_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1725_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_depth_1700_; lean_object* v_levelAssignDepth_1701_; lean_object* v_lmvarCounter_1702_; lean_object* v_mvarCounter_1703_; lean_object* v_lDecls_1704_; lean_object* v_decls_1705_; lean_object* v_userNames_1706_; lean_object* v_lAssignment_1707_; lean_object* v_eAssignment_1708_; lean_object* v_dAssignment_1709_; lean_object* v_instanceTypedMVars_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1724_; 
v_depth_1700_ = lean_ctor_get(v_mctx_1692_, 0);
v_levelAssignDepth_1701_ = lean_ctor_get(v_mctx_1692_, 1);
v_lmvarCounter_1702_ = lean_ctor_get(v_mctx_1692_, 2);
v_mvarCounter_1703_ = lean_ctor_get(v_mctx_1692_, 3);
v_lDecls_1704_ = lean_ctor_get(v_mctx_1692_, 4);
v_decls_1705_ = lean_ctor_get(v_mctx_1692_, 5);
v_userNames_1706_ = lean_ctor_get(v_mctx_1692_, 6);
v_lAssignment_1707_ = lean_ctor_get(v_mctx_1692_, 7);
v_eAssignment_1708_ = lean_ctor_get(v_mctx_1692_, 8);
v_dAssignment_1709_ = lean_ctor_get(v_mctx_1692_, 9);
v_instanceTypedMVars_1710_ = lean_ctor_get(v_mctx_1692_, 10);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_mctx_1692_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1712_ = v_mctx_1692_;
v_isShared_1713_ = v_isSharedCheck_1724_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_instanceTypedMVars_1710_);
lean_inc(v_dAssignment_1709_);
lean_inc(v_eAssignment_1708_);
lean_inc(v_lAssignment_1707_);
lean_inc(v_userNames_1706_);
lean_inc(v_decls_1705_);
lean_inc(v_lDecls_1704_);
lean_inc(v_mvarCounter_1703_);
lean_inc(v_lmvarCounter_1702_);
lean_inc(v_levelAssignDepth_1701_);
lean_inc(v_depth_1700_);
lean_dec(v_mctx_1692_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1724_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1714_ = lean_box(0);
v___x_1715_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_eAssignment_1708_, v_mvarId_1687_, v_val_1688_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 8, v___x_1715_);
v___x_1717_ = v___x_1712_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_depth_1700_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_levelAssignDepth_1701_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_lmvarCounter_1702_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_mvarCounter_1703_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_lDecls_1704_);
lean_ctor_set(v_reuseFailAlloc_1723_, 5, v_decls_1705_);
lean_ctor_set(v_reuseFailAlloc_1723_, 6, v_userNames_1706_);
lean_ctor_set(v_reuseFailAlloc_1723_, 7, v_lAssignment_1707_);
lean_ctor_set(v_reuseFailAlloc_1723_, 8, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1723_, 9, v_dAssignment_1709_);
lean_ctor_set(v_reuseFailAlloc_1723_, 10, v_instanceTypedMVars_1710_);
v___x_1717_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1717_);
v___x_1719_ = v___x_1698_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_cache_1693_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_zetaDeltaFVarIds_1694_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_postponed_1695_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_diag_1696_);
v___x_1719_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_st_ref_put(v___y_1689_, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1714_);
return v___x_1721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg___boxed(lean_object* v_mvarId_1726_, lean_object* v_val_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1726_, v_val_1727_, v___y_1728_);
lean_dec(v___y_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(lean_object* v_as_1731_, size_t v_i_1732_, size_t v_stop_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_eq(v_i_1732_, v_stop_1733_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_array_uget_borrowed(v_as_1731_, v_i_1732_);
lean_inc(v___x_1741_);
v___x_1742_ = l_Lean_MVarId_getDecl(v___x_1741_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v_type_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v_type_1744_ = lean_ctor_get(v_a_1743_, 2);
lean_inc_ref(v_type_1744_);
lean_dec(v_a_1743_);
v___x_1745_ = lean_box(0);
v___x_1746_ = l_Lean_Meta_synthInstance(v_type_1744_, v___x_1745_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
lean_inc(v___x_1741_);
v___x_1748_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v___x_1741_, v_a_1747_, v___y_1736_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; size_t v___x_1750_; size_t v___x_1751_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1732_, v___x_1750_);
v_i_1732_ = v___x_1751_;
v_b_1734_ = v_a_1749_;
goto _start;
}
else
{
return v___x_1748_;
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
v_a_1753_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1746_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1746_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1742_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1742_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_b_1734_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2___boxed(lean_object* v_as_1770_, lean_object* v_i_1771_, lean_object* v_stop_1772_, lean_object* v_b_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
size_t v_i_boxed_1779_; size_t v_stop_boxed_1780_; lean_object* v_res_1781_; 
v_i_boxed_1779_ = lean_unbox_usize(v_i_1771_);
lean_dec(v_i_1771_);
v_stop_boxed_1780_ = lean_unbox_usize(v_stop_1772_);
lean_dec(v_stop_1772_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_as_1770_, v_i_boxed_1779_, v_stop_boxed_1780_, v_b_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v_as_1770_);
return v_res_1781_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1));
v___x_1786_ = l_Lean_MessageData_ofFormat(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object* v_methodName_1787_, lean_object* v_f_1788_, lean_object* v_args_1789_, lean_object* v_instMVars_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v___y_1831_; lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_array_get_size(v_instMVars_1790_);
v___x_1842_ = lean_nat_dec_lt(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
goto v___jp_1796_;
}
else
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_nat_dec_le(v___x_1841_, v___x_1841_);
if (v___x_1844_ == 0)
{
if (v___x_1842_ == 0)
{
goto v___jp_1796_;
}
else
{
size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = ((size_t)0ULL);
v___x_1846_ = lean_usize_of_nat(v___x_1841_);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1790_, v___x_1845_, v___x_1846_, v___x_1843_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
v___y_1831_ = v___x_1847_;
goto v___jp_1830_;
}
}
else
{
size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = ((size_t)0ULL);
v___x_1849_ = lean_usize_of_nat(v___x_1841_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1790_, v___x_1848_, v___x_1849_, v___x_1843_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
v___y_1831_ = v___x_1850_;
goto v___jp_1830_;
}
}
v___jp_1796_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_a_1799_; lean_object* v___x_1800_; 
v___x_1797_ = l_Lean_mkAppN(v_f_1788_, v_args_1789_);
v___x_1798_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v___x_1797_, v_a_1792_);
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc_n(v_a_1799_, 2);
lean_dec_ref(v___x_1798_);
v___x_1800_ = l_Lean_Meta_hasAssignableMVar(v_a_1799_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1821_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1821_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1821_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_unbox(v_a_1801_);
lean_dec(v_a_1801_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1807_; 
lean_dec(v_methodName_1787_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v_a_1799_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1799_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_del_object(v___x_1803_);
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2);
v___x_1810_ = l_Lean_indentExpr(v_a_1799_);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_methodName_1787_, v___x_1811_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_a_1799_);
lean_dec(v_methodName_1787_);
v_a_1822_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1800_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1800_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
v___jp_1830_:
{
if (lean_obj_tag(v___y_1831_) == 0)
{
lean_dec_ref_known(v___y_1831_, 1);
goto v___jp_1796_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v_f_1788_);
lean_dec(v_methodName_1787_);
v_a_1832_ = lean_ctor_get(v___y_1831_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___y_1831_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___y_1831_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___y_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* v_methodName_1851_, lean_object* v_f_1852_, lean_object* v_args_1853_, lean_object* v_instMVars_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v_methodName_1851_, v_f_1852_, v_args_1853_, v_instMVars_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec_ref(v_instMVars_1854_);
lean_dec_ref(v_args_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object* v_mvarId_1861_, lean_object* v_val_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1861_, v_val_1862_, v___y_1864_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object* v_mvarId_1869_, lean_object* v_val_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(v_mvarId_1869_, v_val_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_x_1878_, v_x_1879_, v_x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1882_, lean_object* v_x_1883_, size_t v_x_1884_, size_t v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1883_, v_x_1884_, v_x_1885_, v_x_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
size_t v_x_2411__boxed_1895_; size_t v_x_2412__boxed_1896_; lean_object* v_res_1897_; 
v_x_2411__boxed_1895_ = lean_unbox_usize(v_x_1891_);
lean_dec(v_x_1891_);
v_x_2412__boxed_1896_ = lean_unbox_usize(v_x_1892_);
lean_dec(v_x_1892_);
v_res_1897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1889_, v_x_1890_, v_x_2411__boxed_1895_, v_x_2412__boxed_1896_, v_x_1893_, v_x_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1898_, lean_object* v_n_1899_, lean_object* v_k_1900_, lean_object* v_v_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1899_, v_k_1900_, v_v_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1903_, size_t v_depth_1904_, lean_object* v_keys_1905_, lean_object* v_vals_1906_, lean_object* v_heq_1907_, lean_object* v_i_1908_, lean_object* v_entries_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1904_, v_keys_1905_, v_vals_1906_, v_i_1908_, v_entries_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1911_, lean_object* v_depth_1912_, lean_object* v_keys_1913_, lean_object* v_vals_1914_, lean_object* v_heq_1915_, lean_object* v_i_1916_, lean_object* v_entries_1917_){
_start:
{
size_t v_depth_boxed_1918_; lean_object* v_res_1919_; 
v_depth_boxed_1918_ = lean_unbox_usize(v_depth_1912_);
lean_dec(v_depth_1912_);
v_res_1919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1911_, v_depth_boxed_1918_, v_keys_1913_, v_vals_1914_, v_heq_1915_, v_i_1916_, v_entries_1917_);
lean_dec_ref(v_vals_1914_);
lean_dec_ref(v_keys_1913_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1921_, v_x_1922_, v_x_1923_, v_x_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2));
v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
return v___x_1931_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7));
v___x_1939_ = l_Lean_MessageData_ofFormat(v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* v_f_1940_, lean_object* v_xs_1941_, lean_object* v_type_1942_, lean_object* v_i_1943_, lean_object* v_j_1944_, lean_object* v_args_1945_, lean_object* v_instMVars_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = lean_array_get_size(v_xs_1941_);
v___x_1953_ = lean_nat_dec_le(v___x_1952_, v_i_1943_);
if (v___x_1953_ == 0)
{
if (lean_obj_tag(v_type_1942_) == 7)
{
lean_object* v_binderName_1954_; lean_object* v_binderType_1955_; lean_object* v_body_1956_; uint8_t v_binderInfo_1957_; lean_object* v___x_1958_; lean_object* v_d_1959_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; 
v_binderName_1954_ = lean_ctor_get(v_type_1942_, 0);
lean_inc(v_binderName_1954_);
v_binderType_1955_ = lean_ctor_get(v_type_1942_, 1);
lean_inc_ref(v_binderType_1955_);
v_body_1956_ = lean_ctor_get(v_type_1942_, 2);
lean_inc_ref(v_body_1956_);
v_binderInfo_1957_ = lean_ctor_get_uint8(v_type_1942_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1942_, 3);
v___x_1958_ = lean_array_get_size(v_args_1945_);
v_d_1959_ = lean_expr_instantiate_rev_range(v_binderType_1955_, v_j_1944_, v___x_1958_, v_args_1945_);
lean_dec_ref(v_binderType_1955_);
switch(v_binderInfo_1957_)
{
case 1:
{
v___y_1961_ = v_a_1947_;
v___y_1962_ = v_a_1948_;
v___y_1963_ = v_a_1949_;
v___y_1964_ = v_a_1950_;
goto v___jp_1960_;
}
case 2:
{
v___y_1961_ = v_a_1947_;
v___y_1962_ = v_a_1948_;
v___y_1963_ = v_a_1949_;
v___y_1964_ = v_a_1950_;
goto v___jp_1960_;
}
case 3:
{
lean_object* v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_d_1959_);
v___x_1972_ = 1;
v___x_1973_ = l_Lean_Meta_mkFreshExprMVar(v___x_1971_, v___x_1972_, v_binderName_1954_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc_n(v_a_1974_, 2);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = lean_array_push(v_args_1945_, v_a_1974_);
v___x_1976_ = l_Lean_Expr_mvarId_x21(v_a_1974_);
lean_dec(v_a_1974_);
v___x_1977_ = lean_array_push(v_instMVars_1946_, v___x_1976_);
v_type_1942_ = v_body_1956_;
v_args_1945_ = v___x_1975_;
v_instMVars_1946_ = v___x_1977_;
goto _start;
}
else
{
lean_dec_ref(v_body_1956_);
lean_dec_ref(v_instMVars_1946_);
lean_dec_ref(v_args_1945_);
lean_dec(v_j_1944_);
lean_dec(v_i_1943_);
lean_dec_ref(v_f_1940_);
return v___x_1973_;
}
}
default: 
{
lean_object* v_x_1979_; lean_object* v___y_1981_; lean_object* v___x_1998_; 
lean_dec(v_binderName_1954_);
v_x_1979_ = lean_array_fget_borrowed(v_xs_1941_, v_i_1943_);
lean_inc(v_a_1950_);
lean_inc_ref(v_a_1949_);
lean_inc(v_a_1948_);
lean_inc_ref(v_a_1947_);
lean_inc(v_x_1979_);
v___x_1998_ = lean_infer_type(v_x_1979_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; uint8_t v_transparency_2001_; uint8_t v___x_2002_; uint8_t v___x_2003_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = l_Lean_Meta_Context_config(v_a_1947_);
v_transparency_2001_ = lean_ctor_get_uint8(v___x_2000_, 9);
lean_dec_ref(v___x_2000_);
v___x_2002_ = 1;
v___x_2003_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Meta_isExprDefEq(v_d_1959_, v_a_1999_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
v___y_1981_ = v___x_2004_;
goto v___jp_1980_;
}
else
{
lean_object* v_keyedConfig_2005_; uint8_t v_trackZetaDelta_2006_; lean_object* v_zetaDeltaSet_2007_; lean_object* v_lctx_2008_; lean_object* v_localInstances_2009_; lean_object* v_defEqCtx_x3f_2010_; lean_object* v_synthPendingDepth_2011_; lean_object* v_customCanUnfoldPredicate_x3f_2012_; uint8_t v_univApprox_2013_; uint8_t v_inTypeClassResolution_2014_; uint8_t v_cacheInferType_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_keyedConfig_2005_ = lean_ctor_get(v_a_1947_, 0);
v_trackZetaDelta_2006_ = lean_ctor_get_uint8(v_a_1947_, sizeof(void*)*7);
v_zetaDeltaSet_2007_ = lean_ctor_get(v_a_1947_, 1);
v_lctx_2008_ = lean_ctor_get(v_a_1947_, 2);
v_localInstances_2009_ = lean_ctor_get(v_a_1947_, 3);
v_defEqCtx_x3f_2010_ = lean_ctor_get(v_a_1947_, 4);
v_synthPendingDepth_2011_ = lean_ctor_get(v_a_1947_, 5);
v_customCanUnfoldPredicate_x3f_2012_ = lean_ctor_get(v_a_1947_, 6);
v_univApprox_2013_ = lean_ctor_get_uint8(v_a_1947_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2014_ = lean_ctor_get_uint8(v_a_1947_, sizeof(void*)*7 + 2);
v_cacheInferType_2015_ = lean_ctor_get_uint8(v_a_1947_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2005_);
v___x_2016_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2002_, v_keyedConfig_2005_);
lean_inc(v_customCanUnfoldPredicate_x3f_2012_);
lean_inc(v_synthPendingDepth_2011_);
lean_inc(v_defEqCtx_x3f_2010_);
lean_inc_ref(v_localInstances_2009_);
lean_inc_ref(v_lctx_2008_);
lean_inc(v_zetaDeltaSet_2007_);
v___x_2017_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v_zetaDeltaSet_2007_);
lean_ctor_set(v___x_2017_, 2, v_lctx_2008_);
lean_ctor_set(v___x_2017_, 3, v_localInstances_2009_);
lean_ctor_set(v___x_2017_, 4, v_defEqCtx_x3f_2010_);
lean_ctor_set(v___x_2017_, 5, v_synthPendingDepth_2011_);
lean_ctor_set(v___x_2017_, 6, v_customCanUnfoldPredicate_x3f_2012_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*7, v_trackZetaDelta_2006_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*7 + 1, v_univApprox_2013_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2014_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*7 + 3, v_cacheInferType_2015_);
v___x_2018_ = l_Lean_Meta_isExprDefEq(v_d_1959_, v_a_1999_, v___x_2017_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec_ref_known(v___x_2017_, 7);
v___y_1981_ = v___x_2018_;
goto v___jp_1980_;
}
}
else
{
lean_dec_ref(v_d_1959_);
lean_dec_ref(v_body_1956_);
lean_dec_ref(v_instMVars_1946_);
lean_dec_ref(v_args_1945_);
lean_dec(v_j_1944_);
lean_dec(v_i_1943_);
lean_dec_ref(v_f_1940_);
return v___x_1998_;
}
v___jp_1980_:
{
if (lean_obj_tag(v___y_1981_) == 0)
{
lean_object* v_a_1982_; uint8_t v___x_1983_; 
v_a_1982_ = lean_ctor_get(v___y_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___y_1981_, 1);
v___x_1983_ = lean_unbox(v_a_1982_);
lean_dec(v_a_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v_body_1956_);
lean_dec_ref(v_instMVars_1946_);
lean_dec(v_j_1944_);
lean_dec(v_i_1943_);
v___x_1984_ = l_Lean_mkAppN(v_f_1940_, v_args_1945_);
lean_dec_ref(v_args_1945_);
lean_inc(v_x_1979_);
v___x_1985_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1984_, v_x_1979_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_add(v_i_1943_, v___x_1986_);
lean_dec(v_i_1943_);
lean_inc(v_x_1979_);
v___x_1988_ = lean_array_push(v_args_1945_, v_x_1979_);
v_type_1942_ = v_body_1956_;
v_i_1943_ = v___x_1987_;
v_args_1945_ = v___x_1988_;
goto _start;
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec_ref(v_body_1956_);
lean_dec_ref(v_instMVars_1946_);
lean_dec_ref(v_args_1945_);
lean_dec(v_j_1944_);
lean_dec(v_i_1943_);
lean_dec_ref(v_f_1940_);
v_a_1990_ = lean_ctor_get(v___y_1981_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___y_1981_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___y_1981_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___y_1981_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
v___jp_1960_:
{
lean_object* v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_d_1959_);
v___x_1966_ = 0;
v___x_1967_ = l_Lean_Meta_mkFreshExprMVar(v___x_1965_, v___x_1966_, v_binderName_1954_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = lean_array_push(v_args_1945_, v_a_1968_);
v_type_1942_ = v_body_1956_;
v_args_1945_ = v___x_1969_;
v_a_1947_ = v___y_1961_;
v_a_1948_ = v___y_1962_;
v_a_1949_ = v___y_1963_;
v_a_1950_ = v___y_1964_;
goto _start;
}
else
{
lean_dec_ref(v_body_1956_);
lean_dec_ref(v_instMVars_1946_);
lean_dec_ref(v_args_1945_);
lean_dec(v_j_1944_);
lean_dec(v_i_1943_);
lean_dec_ref(v_f_1940_);
return v___x_1967_;
}
}
}
else
{
lean_object* v___x_2019_; lean_object* v_type_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_array_get_size(v_args_1945_);
v_type_2020_ = lean_expr_instantiate_rev_range(v_type_1942_, v_j_1944_, v___x_2019_, v_args_1945_);
lean_dec(v_j_1944_);
lean_dec_ref(v_type_1942_);
v___x_2021_ = l_Lean_Meta_whnfD(v_type_2020_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; uint8_t v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = l_Lean_Expr_isForall(v_a_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_a_2022_);
lean_dec_ref(v_instMVars_1946_);
lean_dec_ref(v_args_1945_);
lean_dec(v_i_1943_);
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2025_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2026_ = l_Lean_indentExpr(v_f_1940_);
v___x_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_unsigned_to_nat(0u);
v___x_2031_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2032_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1941_, v___x_2030_, v___x_2031_);
v___x_2033_ = l_Lean_indentD(v___x_2032_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2029_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_2024_, v___x_2034_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_2035_;
}
else
{
v_type_1942_ = v_a_2022_;
v_j_1944_ = v___x_2019_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1946_);
lean_dec_ref(v_args_1945_);
lean_dec(v_i_1943_);
lean_dec_ref(v_f_1940_);
return v___x_2021_;
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec(v_j_1944_);
lean_dec(v_i_1943_);
lean_dec_ref(v_type_1942_);
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2038_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2037_, v_f_1940_, v_args_1945_, v_instMVars_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec_ref(v_instMVars_1946_);
lean_dec_ref(v_args_1945_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* v_f_2039_, lean_object* v_xs_2040_, lean_object* v_type_2041_, lean_object* v_i_2042_, lean_object* v_j_2043_, lean_object* v_args_2044_, lean_object* v_instMVars_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2039_, v_xs_2040_, v_type_2041_, v_i_2042_, v_j_2043_, v_args_2044_, v_instMVars_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec_ref(v_xs_2040_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* v_f_2054_, lean_object* v_fType_2055_, lean_object* v_xs_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_2064_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2054_, v_xs_2056_, v_fType_2055_, v___x_2062_, v___x_2062_, v___x_2063_, v___x_2063_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* v_f_2065_, lean_object* v_fType_2066_, lean_object* v_xs_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_f_2065_, v_fType_2066_, v_xs_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec_ref(v_xs_2067_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object* v_x_2074_, lean_object* v_x_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
if (lean_obj_tag(v_x_2074_) == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = l_List_reverse___redArg(v_x_2075_);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
else
{
lean_object* v_tail_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2101_; 
v_tail_2083_ = lean_ctor_get(v_x_2074_, 1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_x_2074_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v_x_2074_, 0);
lean_dec(v_unused_2102_);
v___x_2085_ = v_x_2074_;
v_isShared_2086_ = v_isSharedCheck_2101_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_tail_2083_);
lean_dec(v_x_2074_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2101_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Meta_mkFreshLevelMVar(v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 1, v_x_2075_);
lean_ctor_set(v___x_2085_, 0, v_a_2088_);
v___x_2090_ = v___x_2085_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2088_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_x_2075_);
v___x_2090_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
v_x_2074_ = v_tail_2083_;
v_x_2075_ = v___x_2090_;
goto _start;
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_del_object(v___x_2085_);
lean_dec(v_tail_2083_);
lean_dec(v_x_2075_);
v_a_2093_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2087_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2087_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_x_2103_, v_x_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
lean_ctor_set(v___x_2116_, 2, v___x_2115_);
lean_ctor_set(v___x_2116_, 3, v___x_2115_);
lean_ctor_set(v___x_2116_, 4, v___x_2114_);
lean_ctor_set(v___x_2116_, 5, v___x_2114_);
lean_ctor_set(v___x_2116_, 6, v___x_2114_);
lean_ctor_set(v___x_2116_, 7, v___x_2114_);
lean_ctor_set(v___x_2116_, 8, v___x_2114_);
lean_ctor_set(v___x_2116_, 9, v___x_2114_);
lean_ctor_set(v___x_2116_, 10, v___x_2114_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_unsigned_to_nat(32u);
v___x_2118_ = lean_mk_empty_array_with_capacity(v___x_2117_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2120_ = ((size_t)5ULL);
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = lean_unsigned_to_nat(32u);
v___x_2123_ = lean_mk_empty_array_with_capacity(v___x_2122_);
v___x_2124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2125_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2123_);
lean_ctor_set(v___x_2125_, 2, v___x_2121_);
lean_ctor_set(v___x_2125_, 3, v___x_2121_);
lean_ctor_set_usize(v___x_2125_, 4, v___x_2120_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2126_ = lean_box(1);
v___x_2127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2127_);
lean_ctor_set(v___x_2129_, 2, v___x_2126_);
return v___x_2129_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2132_ = l_Lean_stringToMessageData(v___x_2131_);
return v___x_2132_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
return v___x_2144_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
return v___x_2147_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2150_ = l_Lean_stringToMessageData(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2151_, lean_object* v_declHint_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v_env_2157_; uint8_t v___x_2158_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = lean_st_ref_get(v___y_2153_);
v_env_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc_ref(v_env_2157_);
lean_dec(v___x_2156_);
v___x_2158_ = l_Lean_Name_isAnonymous(v_declHint_2152_);
if (v___x_2158_ == 0)
{
uint8_t v_isExporting_2159_; 
v_isExporting_2159_ = lean_ctor_get_uint8(v_env_2157_, sizeof(void*)*13);
if (v_isExporting_2159_ == 0)
{
lean_object* v___x_2160_; 
lean_dec_ref(v_env_2157_);
lean_dec(v_declHint_2152_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v_msg_2151_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
lean_inc_ref(v_env_2157_);
v___x_2161_ = l_Lean_Environment_setExporting(v_env_2157_, v___x_2158_);
lean_inc(v_declHint_2152_);
lean_inc_ref(v___x_2161_);
v___x_2162_ = l_Lean_Environment_contains(v___x_2161_, v_declHint_2152_, v_isExporting_2159_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
lean_dec_ref(v___x_2161_);
lean_dec_ref(v_env_2157_);
lean_dec(v_declHint_2152_);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_msg_2151_);
return v___x_2163_;
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_c_2169_; lean_object* v___x_2170_; 
v___x_2164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2166_ = l_Lean_Options_empty;
v___x_2167_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2161_);
lean_ctor_set(v___x_2167_, 1, v___x_2164_);
lean_ctor_set(v___x_2167_, 2, v___x_2165_);
lean_ctor_set(v___x_2167_, 3, v___x_2166_);
lean_inc(v_declHint_2152_);
v___x_2168_ = l_Lean_MessageData_ofConstName(v_declHint_2152_, v___x_2158_);
v_c_2169_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2169_, 0, v___x_2167_);
lean_ctor_set(v_c_2169_, 1, v___x_2168_);
v___x_2170_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2157_, v_declHint_2152_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v_env_2157_);
lean_dec(v_declHint_2152_);
v___x_2171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v_c_2169_);
v___x_2173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = l_Lean_MessageData_note(v___x_2174_);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v_msg_2151_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
else
{
lean_object* v_val_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2212_; 
v_val_2178_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2180_ = v___x_2170_;
v_isShared_2181_ = v_isSharedCheck_2212_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_val_2178_);
lean_dec(v___x_2170_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2212_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v_mod_2184_; uint8_t v___x_2185_; 
v___x_2182_ = l_Lean_Environment_header(v_env_2157_);
lean_dec_ref(v_env_2157_);
v___x_2183_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2182_);
v_mod_2184_ = lean_array_get(v___x_2155_, v___x_2183_, v_val_2178_);
lean_dec(v_val_2178_);
lean_dec_ref(v___x_2183_);
v___x_2185_ = l_Lean_isPrivateName(v_declHint_2152_);
lean_dec(v_declHint_2152_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v_c_2169_);
v___x_2188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_MessageData_ofName(v_mod_2184_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = l_Lean_MessageData_note(v___x_2193_);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_msg_2151_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set_tag(v___x_2180_, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2195_);
v___x_2197_ = v___x_2180_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v_c_2169_);
v___x_2201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = l_Lean_MessageData_ofName(v_mod_2184_);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = l_Lean_MessageData_note(v___x_2206_);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_msg_2151_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set_tag(v___x_2180_, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2208_);
v___x_2210_ = v___x_2180_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2213_; 
lean_dec_ref(v_env_2157_);
lean_dec(v_declHint_2152_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_msg_2151_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2214_, lean_object* v_declHint_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2214_, v_declHint_2215_, v___y_2216_);
lean_dec(v___y_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_2219_, lean_object* v_declHint_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2236_; 
v___x_2226_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2219_, v_declHint_2220_, v___y_2224_);
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2231_ = l_Lean_unknownIdentifierMessageTag;
v___x_2232_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v_a_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_2237_, lean_object* v_declHint_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2237_, v_declHint_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_2245_, lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_toCold_2252_; lean_object* v_currRecDepth_2253_; lean_object* v_ref_2254_; uint16_t v_optionFlags_2255_; uint8_t v_suppressElabErrors_2256_; uint8_t v_isRecordingDeps_2257_; lean_object* v_ref_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_toCold_2252_ = lean_ctor_get(v___y_2249_, 0);
v_currRecDepth_2253_ = lean_ctor_get(v___y_2249_, 1);
v_ref_2254_ = lean_ctor_get(v___y_2249_, 2);
v_optionFlags_2255_ = lean_ctor_get_uint16(v___y_2249_, sizeof(void*)*3);
v_suppressElabErrors_2256_ = lean_ctor_get_uint8(v___y_2249_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2257_ = lean_ctor_get_uint8(v___y_2249_, sizeof(void*)*3 + 3);
v_ref_2258_ = l_Lean_replaceRef(v_ref_2245_, v_ref_2254_);
lean_inc(v_currRecDepth_2253_);
lean_inc_ref(v_toCold_2252_);
v___x_2259_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2259_, 0, v_toCold_2252_);
lean_ctor_set(v___x_2259_, 1, v_currRecDepth_2253_);
lean_ctor_set(v___x_2259_, 2, v_ref_2258_);
lean_ctor_set_uint16(v___x_2259_, sizeof(void*)*3, v_optionFlags_2255_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*3 + 2, v_suppressElabErrors_2256_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*3 + 3, v_isRecordingDeps_2257_);
v___x_2260_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2246_, v___y_2247_, v___y_2248_, v___x_2259_, v___y_2250_);
lean_dec_ref_known(v___x_2259_, 3);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2261_, lean_object* v_msg_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2261_, v_msg_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v_ref_2261_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2269_, lean_object* v_msg_2270_, lean_object* v_declHint_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v___x_2277_; lean_object* v_a_2278_; lean_object* v___x_2279_; 
v___x_2277_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2270_, v_declHint_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref(v___x_2277_);
v___x_2279_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2269_, v_a_2278_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2280_, lean_object* v_msg_2281_, lean_object* v_declHint_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2280_, v_msg_2281_, v_declHint_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v_ref_2280_);
return v_res_2288_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2291_ = l_Lean_stringToMessageData(v___x_2290_);
return v___x_2291_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2294_ = l_Lean_stringToMessageData(v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2295_, lean_object* v_constName_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2302_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2303_ = 0;
lean_inc(v_constName_2296_);
v___x_2304_ = l_Lean_MessageData_ofConstName(v_constName_2296_, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2302_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2295_, v___x_2307_, v_constName_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2309_, lean_object* v_constName_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2309_, v_constName_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v_ref_2309_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_ref_2323_; lean_object* v___x_2324_; 
v_ref_2323_ = lean_ctor_get(v___y_2320_, 2);
v___x_2324_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2323_, v_constName_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v_env_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; 
v___x_2338_ = lean_st_ref_get(v___y_2336_);
v_env_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc_ref(v_env_2339_);
lean_dec(v___x_2338_);
v___x_2340_ = 0;
lean_inc(v_constName_2332_);
v___x_2341_ = l_Lean_Environment_findConstVal_x3f(v_env_2339_, v_constName_2332_, v___x_2340_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
return v___x_2342_;
}
else
{
lean_object* v_val_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_constName_2332_);
v_val_2343_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2341_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_val_2343_);
lean_dec(v___x_2341_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set_tag(v___x_2345_, 0);
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_val_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2364_; 
lean_inc(v_constName_2358_);
v___x_2364_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v_levelParams_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v_levelParams_2366_ = lean_ctor_get(v_a_2365_, 1);
v___x_2367_ = lean_box(0);
lean_inc(v_levelParams_2366_);
v___x_2368_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2366_, v___x_2367_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc_n(v_a_2369_, 2);
lean_dec_ref_known(v___x_2368_, 1);
v___x_2370_ = l_Lean_mkConst(v_constName_2358_, v_a_2369_);
v___x_2371_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2365_, v_a_2369_, v_a_2362_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2380_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2370_);
lean_ctor_set(v___x_2376_, 1, v_a_2372_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2376_);
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v___x_2370_);
v_a_2381_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2371_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2371_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_a_2365_);
lean_dec(v_constName_2358_);
v_a_2389_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2368_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2368_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_constName_2358_);
v_a_2397_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2364_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2364_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2412_, lean_object* v_constName_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2420_, lean_object* v_constName_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2420_, v_constName_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2428_, lean_object* v_ref_2429_, lean_object* v_constName_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2429_, v_constName_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2437_, lean_object* v_ref_2438_, lean_object* v_constName_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2437_, v_ref_2438_, v_constName_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v_ref_2438_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2446_, lean_object* v_ref_2447_, lean_object* v_msg_2448_, lean_object* v_declHint_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2447_, v_msg_2448_, v_declHint_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2456_, lean_object* v_ref_2457_, lean_object* v_msg_2458_, lean_object* v_declHint_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2456_, v_ref_2457_, v_msg_2458_, v_declHint_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v_ref_2457_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2466_, lean_object* v_declHint_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2466_, v_declHint_2467_, v___y_2471_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2474_, lean_object* v_declHint_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2474_, v_declHint_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2482_, lean_object* v_ref_2483_, lean_object* v_msg_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2483_, v_msg_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2491_, lean_object* v_ref_2492_, lean_object* v_msg_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2491_, v_ref_2492_, v_msg_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v_ref_2492_);
return v_res_2499_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2502_ = l_Lean_stringToMessageData(v___x_2501_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2505_ = l_Lean_stringToMessageData(v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2506_, lean_object* v_f_2507_, lean_object* v_inst_2508_, lean_object* v_xs_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2516_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2517_ = lean_apply_1(v_inst_2506_, v_f_2507_);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_apply_1(v_inst_2508_, v_xs_2509_);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2524_, lean_object* v_f_2525_, lean_object* v_inst_2526_, lean_object* v_xs_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2524_, v_f_2525_, v_inst_2526_, v_xs_2527_, v_x_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v_x_2528_);
return v_res_2534_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_instMonadEIO___redArg();
return v___x_2535_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2537_ = l_StateRefT_x27_instMonad___redArg(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2545_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2546_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2545_, v___x_2544_);
return v___x_2546_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___f_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2548_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2549_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2548_, v___x_2547_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2552_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2553_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2554_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2555_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2554_, v___x_2553_, v___x_2552_);
return v___x_2555_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___f_2557_; lean_object* v___f_2558_; lean_object* v___x_2559_; 
v___x_2556_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2557_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2558_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2559_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2558_, v___f_2557_, v___x_2556_);
return v___x_2559_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_instMonadExceptOfEIO___redArg();
return v___x_2560_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2562_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2561_);
return v___x_2562_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2564_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2563_);
return v___x_2564_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2566_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2565_);
return v___x_2566_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2568_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2567_);
return v___x_2568_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2580_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2581_ = l_Lean_Name_append(v___x_2580_, v___x_2579_);
return v___x_2581_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2588_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2589_ = l_Lean_Name_append(v___x_2588_, v___x_2587_);
return v___x_2589_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2590_; double v___x_2591_; 
v___x_2590_ = lean_unsigned_to_nat(1000000000u);
v___x_2591_ = lean_float_of_nat(v___x_2590_);
return v___x_2591_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2598_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2599_ = l_Lean_Name_append(v___x_2598_, v___x_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2600_, lean_object* v_inst_2601_, lean_object* v_f_2602_, lean_object* v_xs_2603_, lean_object* v_k_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; lean_object* v_toApplicative_2611_; lean_object* v_toFunctor_2612_; lean_object* v_toSeq_2613_; lean_object* v_toSeqLeft_2614_; lean_object* v_toSeqRight_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___f_2621_; lean_object* v___f_2622_; lean_object* v___f_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v_toApplicative_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2866_; 
v___x_2610_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2611_ = lean_ctor_get(v___x_2610_, 0);
v_toFunctor_2612_ = lean_ctor_get(v_toApplicative_2611_, 0);
v_toSeq_2613_ = lean_ctor_get(v_toApplicative_2611_, 2);
v_toSeqLeft_2614_ = lean_ctor_get(v_toApplicative_2611_, 3);
v_toSeqRight_2615_ = lean_ctor_get(v_toApplicative_2611_, 4);
v___f_2616_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2617_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2612_, 2);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toFunctor_2612_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toFunctor_2612_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___f_2618_);
lean_ctor_set(v___x_2620_, 1, v___f_2619_);
lean_inc(v_toSeqRight_2615_);
v___f_2621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2621_, 0, v_toSeqRight_2615_);
lean_inc(v_toSeqLeft_2614_);
v___f_2622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2622_, 0, v_toSeqLeft_2614_);
lean_inc(v_toSeq_2613_);
v___f_2623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2623_, 0, v_toSeq_2613_);
v___x_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2620_);
lean_ctor_set(v___x_2624_, 1, v___f_2616_);
lean_ctor_set(v___x_2624_, 2, v___f_2623_);
lean_ctor_set(v___x_2624_, 3, v___f_2622_);
lean_ctor_set(v___x_2624_, 4, v___f_2621_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
lean_ctor_set(v___x_2625_, 1, v___f_2617_);
v___x_2626_ = l_StateRefT_x27_instMonad___redArg(v___x_2625_);
v_toApplicative_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2866_ == 0)
{
lean_object* v_unused_2867_; 
v_unused_2867_ = lean_ctor_get(v___x_2626_, 1);
lean_dec(v_unused_2867_);
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2866_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_toApplicative_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2866_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_toFunctor_2631_; lean_object* v_toSeq_2632_; lean_object* v_toSeqLeft_2633_; lean_object* v_toSeqRight_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2864_; 
v_toFunctor_2631_ = lean_ctor_get(v_toApplicative_2627_, 0);
v_toSeq_2632_ = lean_ctor_get(v_toApplicative_2627_, 2);
v_toSeqLeft_2633_ = lean_ctor_get(v_toApplicative_2627_, 3);
v_toSeqRight_2634_ = lean_ctor_get(v_toApplicative_2627_, 4);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_toApplicative_2627_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; 
v_unused_2865_ = lean_ctor_get(v_toApplicative_2627_, 1);
lean_dec(v_unused_2865_);
v___x_2636_ = v_toApplicative_2627_;
v_isShared_2637_ = v_isSharedCheck_2864_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_toSeqRight_2634_);
lean_inc(v_toSeqLeft_2633_);
lean_inc(v_toSeq_2632_);
lean_inc(v_toFunctor_2631_);
lean_dec(v_toApplicative_2627_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2864_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___f_2638_; lean_object* v___f_2639_; lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___x_2642_; lean_object* v___f_2643_; lean_object* v___f_2644_; lean_object* v___f_2645_; lean_object* v___x_2647_; 
v___f_2638_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2639_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2631_);
v___f_2640_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2640_, 0, v_toFunctor_2631_);
v___f_2641_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2641_, 0, v_toFunctor_2631_);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___f_2640_);
lean_ctor_set(v___x_2642_, 1, v___f_2641_);
v___f_2643_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2643_, 0, v_toSeqRight_2634_);
v___f_2644_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2644_, 0, v_toSeqLeft_2633_);
v___f_2645_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2645_, 0, v_toSeq_2632_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 4, v___f_2643_);
lean_ctor_set(v___x_2636_, 3, v___f_2644_);
lean_ctor_set(v___x_2636_, 2, v___f_2645_);
lean_ctor_set(v___x_2636_, 1, v___f_2638_);
lean_ctor_set(v___x_2636_, 0, v___x_2642_);
v___x_2647_ = v___x_2636_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v___f_2638_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v___f_2645_);
lean_ctor_set(v_reuseFailAlloc_2863_, 3, v___f_2644_);
lean_ctor_set(v_reuseFailAlloc_2863_, 4, v___f_2643_);
v___x_2647_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2649_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v___f_2639_);
lean_ctor_set(v___x_2629_, 0, v___x_2647_);
v___x_2649_ = v___x_2629_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___f_2639_);
v___x_2649_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v_toMonadRef_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v_toCold_2655_; lean_object* v_options_2656_; uint8_t v_hasTrace_2657_; 
v___x_2650_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2651_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2652_ = lean_ctor_get(v___x_2651_, 0);
v___x_2653_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2654_ = l_Lean_KVMap_instValueBool;
v_toCold_2655_ = lean_ctor_get(v_a_2607_, 0);
v_options_2656_ = lean_ctor_get(v_toCold_2655_, 2);
v_hasTrace_2657_ = lean_ctor_get_uint8(v_options_2656_, sizeof(void*)*1);
if (v_hasTrace_2657_ == 0)
{
lean_object* v___x_2658_; 
lean_dec_ref(v___x_2649_);
lean_dec(v_xs_2603_);
lean_dec(v_f_2602_);
lean_dec_ref(v_inst_2601_);
lean_dec_ref(v_inst_2600_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2658_ = lean_apply_5(v_k_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2658_) == 0)
{
return v___x_2658_;
}
else
{
lean_object* v_a_2659_; uint8_t v___y_2661_; uint8_t v___x_2670_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
v___x_2670_ = l_Lean_Exception_isInterrupt(v_a_2659_);
if (v___x_2670_ == 0)
{
uint8_t v___x_2671_; 
lean_inc(v_a_2659_);
v___x_2671_ = l_Lean_Exception_isRuntime(v_a_2659_);
v___y_2661_ = v___x_2671_;
goto v___jp_2660_;
}
else
{
v___y_2661_ = v___x_2670_;
goto v___jp_2660_;
}
v___jp_2660_:
{
if (v___y_2661_ == 0)
{
lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; 
v_unused_2669_ = lean_ctor_get(v___x_2658_, 0);
lean_dec(v_unused_2669_);
v___x_2663_ = v___x_2658_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_dec(v___x_2658_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2659_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
else
{
lean_dec(v_a_2659_);
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2672_; lean_object* v___x_2673_; lean_object* v___y_2675_; lean_object* v___y_2676_; uint8_t v___y_2677_; lean_object* v___y_2702_; lean_object* v_a_2703_; lean_object* v___f_2706_; lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v_a_2715_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v_a_2731_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; uint8_t v___y_2737_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v_a_2748_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v_a_2754_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v_a_2759_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v_a_2772_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; uint8_t v___y_2778_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v_a_2789_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v_a_2795_; 
v_inheritedTraceOptions_2672_ = lean_ctor_get(v_toCold_2655_, 11);
v___x_2673_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2706_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2706_, 0, v_inst_2600_);
lean_closure_set(v___f_2706_, 1, v_f_2602_);
lean_closure_set(v___f_2706_, 2, v_inst_2601_);
lean_closure_set(v___f_2706_, 3, v_xs_2603_);
v___f_2707_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2708_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2710_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2711_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2656_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2834_ = l_Lean_trace_profiler;
v___x_2835_ = l_Lean_Option_get___redArg(v___x_2654_, v_options_2656_, v___x_2834_);
v___x_2836_ = lean_unbox(v___x_2835_);
lean_dec(v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; 
lean_dec_ref(v___f_2706_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2837_ = lean_apply_5(v_k_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
v___x_2839_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2840_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2841_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2656_, v___x_2840_);
if (v___x_2841_ == 0)
{
lean_dec(v_a_2838_);
lean_dec_ref(v___x_2649_);
return v___x_2837_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_8995__overap_2843_; lean_object* v___x_2844_; 
lean_dec_ref_known(v___x_2837_, 1);
lean_inc(v_a_2838_);
v___x_2842_ = l_Lean_MessageData_ofExpr(v_a_2838_);
lean_inc_ref(v_toMonadRef_2652_);
lean_inc_ref(v___x_2649_);
v___x_8995__overap_2843_ = l_Lean_addTrace___redArg(v___x_2649_, v___x_2650_, v_toMonadRef_2652_, v___x_2673_, v___x_2839_, v___x_2842_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2844_ = lean_apply_5(v___x_8995__overap_2843_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec_ref(v___x_2649_);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; 
v_unused_2852_ = lean_ctor_get(v___x_2844_, 0);
lean_dec(v_unused_2852_);
v___x_2846_ = v___x_2844_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_dec(v___x_2844_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v_a_2838_);
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2838_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_a_2838_);
v_a_2853_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2844_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2844_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
lean_inc(v_a_2853_);
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
v___y_2702_ = v___x_2858_;
v_a_2703_ = v_a_2853_;
goto v___jp_2701_;
}
}
}
}
}
else
{
lean_object* v_a_2861_; 
v_a_2861_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2861_);
v___y_2702_ = v___x_2837_;
v_a_2703_ = v_a_2861_;
goto v___jp_2701_;
}
}
else
{
goto v___jp_2797_;
}
}
else
{
goto v___jp_2797_;
}
v___jp_2674_:
{
if (v___y_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
lean_dec_ref(v___y_2675_);
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2679_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2656_, v___x_2679_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; 
lean_dec_ref(v___x_2649_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___y_2676_);
return v___x_2681_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_8806__overap_2683_; lean_object* v___x_2684_; 
lean_inc_ref(v___y_2676_);
v___x_2682_ = l_Lean_Exception_toMessageData(v___y_2676_);
lean_inc_ref(v_toMonadRef_2652_);
v___x_8806__overap_2683_ = l_Lean_addTrace___redArg(v___x_2649_, v___x_2650_, v_toMonadRef_2652_, v___x_2673_, v___x_2678_, v___x_2682_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2684_ = lean_apply_5(v___x_8806__overap_2683_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; 
v_unused_2692_ = lean_ctor_get(v___x_2684_, 0);
lean_dec(v_unused_2692_);
v___x_2686_ = v___x_2684_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v___x_2684_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set_tag(v___x_2686_, 1);
lean_ctor_set(v___x_2686_, 0, v___y_2676_);
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___y_2676_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v___y_2676_);
v_a_2693_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2684_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2684_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2676_);
lean_dec_ref(v___x_2649_);
return v___y_2675_;
}
}
v___jp_2701_:
{
uint8_t v___x_2704_; 
v___x_2704_ = l_Lean_Exception_isInterrupt(v_a_2703_);
if (v___x_2704_ == 0)
{
uint8_t v___x_2705_; 
lean_inc_ref(v_a_2703_);
v___x_2705_ = l_Lean_Exception_isRuntime(v_a_2703_);
v___y_2675_ = v___y_2702_;
v___y_2676_ = v_a_2703_;
v___y_2677_ = v___x_2705_;
goto v___jp_2674_;
}
else
{
v___y_2675_ = v___y_2702_;
v___y_2676_ = v_a_2703_;
v___y_2677_ = v___x_2704_;
goto v___jp_2674_;
}
}
v___jp_2712_:
{
lean_object* v___x_2716_; double v___x_2717_; double v___x_2718_; double v___x_2719_; double v___x_2720_; double v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_8867__overap_2726_; lean_object* v___x_2727_; 
v___x_2716_ = lean_io_mono_nanos_now();
v___x_2717_ = lean_float_of_nat(v___y_2714_);
v___x_2718_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2719_ = lean_float_div(v___x_2717_, v___x_2718_);
v___x_2720_ = lean_float_of_nat(v___x_2716_);
v___x_2721_ = lean_float_div(v___x_2720_, v___x_2718_);
v___x_2722_ = lean_box_float(v___x_2719_);
v___x_2723_ = lean_box_float(v___x_2721_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2722_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v_a_2715_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
lean_inc_ref(v_toMonadRef_2652_);
v___x_8867__overap_2726_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2649_, v___x_2650_, v_toMonadRef_2652_, v___x_2673_, lean_box(0), v___x_2653_, v___f_2707_, v___x_2708_, v_hasTrace_2657_, v___x_2709_, v_options_2656_, v___x_2711_, v___y_2713_, v___f_2706_, v___x_2725_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2727_ = lean_apply_5(v___x_8867__overap_2726_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
return v___x_2727_;
}
v___jp_2728_:
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_a_2731_);
v___y_2713_ = v___y_2729_;
v___y_2714_ = v___y_2730_;
v_a_2715_ = v___x_2732_;
goto v___jp_2712_;
}
v___jp_2733_:
{
if (v___y_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2738_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2739_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2740_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2656_, v___x_2739_);
if (v___x_2740_ == 0)
{
v___y_2729_ = v___y_2735_;
v___y_2730_ = v___y_2736_;
v_a_2731_ = v___y_2734_;
goto v___jp_2728_;
}
else
{
lean_object* v___x_2741_; lean_object* v___x_8886__overap_2742_; lean_object* v___x_2743_; 
lean_inc_ref(v___y_2734_);
v___x_2741_ = l_Lean_Exception_toMessageData(v___y_2734_);
lean_inc_ref(v_toMonadRef_2652_);
lean_inc_ref(v___x_2649_);
v___x_8886__overap_2742_ = l_Lean_addTrace___redArg(v___x_2649_, v___x_2650_, v_toMonadRef_2652_, v___x_2673_, v___x_2738_, v___x_2741_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2743_ = lean_apply_5(v___x_8886__overap_2742_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_dec_ref_known(v___x_2743_, 1);
v___y_2729_ = v___y_2735_;
v___y_2730_ = v___y_2736_;
v_a_2731_ = v___y_2734_;
goto v___jp_2728_;
}
else
{
lean_object* v_a_2744_; 
lean_dec_ref(v___y_2734_);
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2743_, 1);
v___y_2729_ = v___y_2735_;
v___y_2730_ = v___y_2736_;
v_a_2731_ = v_a_2744_;
goto v___jp_2728_;
}
}
}
else
{
v___y_2729_ = v___y_2735_;
v___y_2730_ = v___y_2736_;
v_a_2731_ = v___y_2734_;
goto v___jp_2728_;
}
}
v___jp_2745_:
{
uint8_t v___x_2749_; 
v___x_2749_ = l_Lean_Exception_isInterrupt(v_a_2748_);
if (v___x_2749_ == 0)
{
uint8_t v___x_2750_; 
lean_inc_ref(v_a_2748_);
v___x_2750_ = l_Lean_Exception_isRuntime(v_a_2748_);
v___y_2734_ = v_a_2748_;
v___y_2735_ = v___y_2746_;
v___y_2736_ = v___y_2747_;
v___y_2737_ = v___x_2750_;
goto v___jp_2733_;
}
else
{
v___y_2734_ = v_a_2748_;
v___y_2735_ = v___y_2746_;
v___y_2736_ = v___y_2747_;
v___y_2737_ = v___x_2749_;
goto v___jp_2733_;
}
}
v___jp_2751_:
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2754_);
v___y_2713_ = v___y_2752_;
v___y_2714_ = v___y_2753_;
v_a_2715_ = v___x_2755_;
goto v___jp_2712_;
}
v___jp_2756_:
{
lean_object* v___x_2760_; double v___x_2761_; double v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_8929__overap_2767_; lean_object* v___x_2768_; 
v___x_2760_ = lean_io_get_num_heartbeats();
v___x_2761_ = lean_float_of_nat(v___y_2757_);
v___x_2762_ = lean_float_of_nat(v___x_2760_);
v___x_2763_ = lean_box_float(v___x_2761_);
v___x_2764_ = lean_box_float(v___x_2762_);
v___x_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_a_2759_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
lean_inc_ref(v_toMonadRef_2652_);
v___x_8929__overap_2767_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2649_, v___x_2650_, v_toMonadRef_2652_, v___x_2673_, lean_box(0), v___x_2653_, v___f_2707_, v___x_2708_, v_hasTrace_2657_, v___x_2709_, v_options_2656_, v___x_2711_, v___y_2758_, v___f_2706_, v___x_2766_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2768_ = lean_apply_5(v___x_8929__overap_2767_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
return v___x_2768_;
}
v___jp_2769_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v_a_2772_);
v___y_2757_ = v___y_2770_;
v___y_2758_ = v___y_2771_;
v_a_2759_ = v___x_2773_;
goto v___jp_2756_;
}
v___jp_2774_:
{
if (v___y_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v___x_2779_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2780_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2781_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2656_, v___x_2780_);
if (v___x_2781_ == 0)
{
v___y_2770_ = v___y_2776_;
v___y_2771_ = v___y_2777_;
v_a_2772_ = v___y_2775_;
goto v___jp_2769_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_8948__overap_2783_; lean_object* v___x_2784_; 
lean_inc_ref(v___y_2775_);
v___x_2782_ = l_Lean_Exception_toMessageData(v___y_2775_);
lean_inc_ref(v_toMonadRef_2652_);
lean_inc_ref(v___x_2649_);
v___x_8948__overap_2783_ = l_Lean_addTrace___redArg(v___x_2649_, v___x_2650_, v_toMonadRef_2652_, v___x_2673_, v___x_2779_, v___x_2782_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2784_ = lean_apply_5(v___x_8948__overap_2783_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_dec_ref_known(v___x_2784_, 1);
v___y_2770_ = v___y_2776_;
v___y_2771_ = v___y_2777_;
v_a_2772_ = v___y_2775_;
goto v___jp_2769_;
}
else
{
lean_object* v_a_2785_; 
lean_dec_ref(v___y_2775_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___y_2770_ = v___y_2776_;
v___y_2771_ = v___y_2777_;
v_a_2772_ = v_a_2785_;
goto v___jp_2769_;
}
}
}
else
{
v___y_2770_ = v___y_2776_;
v___y_2771_ = v___y_2777_;
v_a_2772_ = v___y_2775_;
goto v___jp_2769_;
}
}
v___jp_2786_:
{
uint8_t v___x_2790_; 
v___x_2790_ = l_Lean_Exception_isInterrupt(v_a_2789_);
if (v___x_2790_ == 0)
{
uint8_t v___x_2791_; 
lean_inc_ref(v_a_2789_);
v___x_2791_ = l_Lean_Exception_isRuntime(v_a_2789_);
v___y_2775_ = v_a_2789_;
v___y_2776_ = v___y_2787_;
v___y_2777_ = v___y_2788_;
v___y_2778_ = v___x_2791_;
goto v___jp_2774_;
}
else
{
v___y_2775_ = v_a_2789_;
v___y_2776_ = v___y_2787_;
v___y_2777_ = v___y_2788_;
v___y_2778_ = v___x_2790_;
goto v___jp_2774_;
}
}
v___jp_2792_:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2795_);
v___y_2757_ = v___y_2793_;
v___y_2758_ = v___y_2794_;
v_a_2759_ = v___x_2796_;
goto v___jp_2756_;
}
v___jp_2797_:
{
lean_object* v___x_8845__overap_2798_; lean_object* v___x_2799_; 
lean_inc_ref(v___x_2649_);
v___x_8845__overap_2798_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2649_, v___x_2650_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2799_ = lean_apply_5(v___x_8845__overap_2798_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2802_ = l_Lean_Option_get___redArg(v___x_2654_, v_options_2656_, v___x_2801_);
v___x_2803_ = lean_unbox(v___x_2802_);
lean_dec(v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = lean_io_mono_nanos_now();
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2805_ = lean_apply_5(v_k_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2808_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2809_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2656_, v___x_2808_);
if (v___x_2809_ == 0)
{
v___y_2752_ = v_a_2800_;
v___y_2753_ = v___x_2804_;
v_a_2754_ = v_a_2806_;
goto v___jp_2751_;
}
else
{
lean_object* v___x_2810_; lean_object* v___x_8909__overap_2811_; lean_object* v___x_2812_; 
lean_inc(v_a_2806_);
v___x_2810_ = l_Lean_MessageData_ofExpr(v_a_2806_);
lean_inc_ref(v_toMonadRef_2652_);
lean_inc_ref(v___x_2649_);
v___x_8909__overap_2811_ = l_Lean_addTrace___redArg(v___x_2649_, v___x_2650_, v_toMonadRef_2652_, v___x_2673_, v___x_2807_, v___x_2810_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2812_ = lean_apply_5(v___x_8909__overap_2811_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_dec_ref_known(v___x_2812_, 1);
v___y_2752_ = v_a_2800_;
v___y_2753_ = v___x_2804_;
v_a_2754_ = v_a_2806_;
goto v___jp_2751_;
}
else
{
lean_object* v_a_2813_; 
lean_dec(v_a_2806_);
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2746_ = v_a_2800_;
v___y_2747_ = v___x_2804_;
v_a_2748_ = v_a_2813_;
goto v___jp_2745_;
}
}
}
else
{
lean_object* v_a_2814_; 
v_a_2814_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2805_, 1);
v___y_2746_ = v_a_2800_;
v___y_2747_ = v___x_2804_;
v_a_2748_ = v_a_2814_;
goto v___jp_2745_;
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2816_ = lean_apply_5(v_k_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2819_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2820_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2656_, v___x_2819_);
if (v___x_2820_ == 0)
{
v___y_2793_ = v___x_2815_;
v___y_2794_ = v_a_2800_;
v_a_2795_ = v_a_2817_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_8971__overap_2822_; lean_object* v___x_2823_; 
lean_inc(v_a_2817_);
v___x_2821_ = l_Lean_MessageData_ofExpr(v_a_2817_);
lean_inc_ref(v_toMonadRef_2652_);
lean_inc_ref(v___x_2649_);
v___x_8971__overap_2822_ = l_Lean_addTrace___redArg(v___x_2649_, v___x_2650_, v_toMonadRef_2652_, v___x_2673_, v___x_2818_, v___x_2821_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
v___x_2823_ = lean_apply_5(v___x_8971__overap_2822_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, lean_box(0));
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_dec_ref_known(v___x_2823_, 1);
v___y_2793_ = v___x_2815_;
v___y_2794_ = v_a_2800_;
v_a_2795_ = v_a_2817_;
goto v___jp_2792_;
}
else
{
lean_object* v_a_2824_; 
lean_dec(v_a_2817_);
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___y_2787_ = v___x_2815_;
v___y_2788_ = v_a_2800_;
v_a_2789_ = v_a_2824_;
goto v___jp_2786_;
}
}
}
else
{
lean_object* v_a_2825_; 
v_a_2825_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2816_, 1);
v___y_2787_ = v___x_2815_;
v___y_2788_ = v_a_2800_;
v_a_2789_ = v_a_2825_;
goto v___jp_2786_;
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec_ref(v___f_2706_);
lean_dec_ref(v___x_2649_);
lean_dec_ref(v_k_2604_);
v_a_2826_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2799_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2799_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2868_, lean_object* v_inst_2869_, lean_object* v_f_2870_, lean_object* v_xs_2871_, lean_object* v_k_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2868_, v_inst_2869_, v_f_2870_, v_xs_2871_, v_k_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2879_, lean_object* v_00_u03b2_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_f_2883_, lean_object* v_xs_2884_, lean_object* v_k_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2881_, v_inst_2882_, v_f_2883_, v_xs_2884_, v_k_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2892_, lean_object* v_00_u03b2_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_f_2896_, lean_object* v_xs_2897_, lean_object* v_k_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2892_, v_00_u03b2_2893_, v_inst_2894_, v_inst_2895_, v_f_2896_, v_xs_2897_, v_k_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2905_, uint8_t v_allowLevelAssignments_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2906_, v_k_2905_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_a_2921_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2912_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2912_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2929_, lean_object* v_allowLevelAssignments_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2936_; lean_object* v_res_2937_; 
v_allowLevelAssignments_boxed_2936_ = lean_unbox(v_allowLevelAssignments_2930_);
v_res_2937_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2929_, v_allowLevelAssignments_boxed_2936_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2938_, lean_object* v_k_2939_, uint8_t v_allowLevelAssignments_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2939_, v_allowLevelAssignments_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2947_, lean_object* v_k_2948_, lean_object* v_allowLevelAssignments_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2955_; lean_object* v_res_2956_; 
v_allowLevelAssignments_boxed_2955_ = lean_unbox(v_allowLevelAssignments_2949_);
v_res_2956_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2947_, v_k_2948_, v_allowLevelAssignments_boxed_2955_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2957_, lean_object* v_xs_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2957_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v_fst_2966_; lean_object* v_snd_2967_; lean_object* v___x_2968_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v_fst_2966_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_fst_2966_);
v_snd_2967_ = lean_ctor_get(v_a_2965_, 1);
lean_inc(v_snd_2967_);
lean_dec(v_a_2965_);
v___x_2968_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2966_, v_snd_2967_, v_xs_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2968_;
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
v_a_2969_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2964_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2964_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2977_, lean_object* v_xs_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2977_, v_xs_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v_xs_2978_);
return v_res_2984_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_unsigned_to_nat(32u);
v___x_2986_ = lean_mk_empty_array_with_capacity(v___x_2985_);
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2988_ = ((size_t)5ULL);
v___x_2989_ = lean_unsigned_to_nat(0u);
v___x_2990_ = lean_unsigned_to_nat(32u);
v___x_2991_ = lean_mk_empty_array_with_capacity(v___x_2990_);
v___x_2992_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2993_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v___x_2991_);
lean_ctor_set(v___x_2993_, 2, v___x_2989_);
lean_ctor_set(v___x_2993_, 3, v___x_2989_);
lean_ctor_set_usize(v___x_2993_, 4, v___x_2988_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2996_; lean_object* v_traceState_2997_; lean_object* v_traces_2998_; lean_object* v___x_2999_; lean_object* v_traceState_3000_; lean_object* v_env_3001_; lean_object* v_nextMacroScope_3002_; lean_object* v_ngen_3003_; lean_object* v_auxDeclNGen_3004_; lean_object* v_cache_3005_; lean_object* v_recordedDeps_3006_; lean_object* v_messages_3007_; lean_object* v_infoState_3008_; lean_object* v_snapshotTasks_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3028_; 
v___x_2996_ = lean_st_ref_get(v___y_2994_);
v_traceState_2997_ = lean_ctor_get(v___x_2996_, 4);
lean_inc_ref(v_traceState_2997_);
lean_dec(v___x_2996_);
v_traces_2998_ = lean_ctor_get(v_traceState_2997_, 0);
lean_inc_ref(v_traces_2998_);
lean_dec_ref(v_traceState_2997_);
v___x_2999_ = lean_st_ref_take(v___y_2994_);
v_traceState_3000_ = lean_ctor_get(v___x_2999_, 4);
v_env_3001_ = lean_ctor_get(v___x_2999_, 0);
v_nextMacroScope_3002_ = lean_ctor_get(v___x_2999_, 1);
v_ngen_3003_ = lean_ctor_get(v___x_2999_, 2);
v_auxDeclNGen_3004_ = lean_ctor_get(v___x_2999_, 3);
v_cache_3005_ = lean_ctor_get(v___x_2999_, 5);
v_recordedDeps_3006_ = lean_ctor_get(v___x_2999_, 6);
v_messages_3007_ = lean_ctor_get(v___x_2999_, 7);
v_infoState_3008_ = lean_ctor_get(v___x_2999_, 8);
v_snapshotTasks_3009_ = lean_ctor_get(v___x_2999_, 9);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3011_ = v___x_2999_;
v_isShared_3012_ = v_isSharedCheck_3028_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_snapshotTasks_3009_);
lean_inc(v_infoState_3008_);
lean_inc(v_messages_3007_);
lean_inc(v_recordedDeps_3006_);
lean_inc(v_cache_3005_);
lean_inc(v_traceState_3000_);
lean_inc(v_auxDeclNGen_3004_);
lean_inc(v_ngen_3003_);
lean_inc(v_nextMacroScope_3002_);
lean_inc(v_env_3001_);
lean_dec(v___x_2999_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3028_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
uint64_t v_tid_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3026_; 
v_tid_3013_ = lean_ctor_get_uint64(v_traceState_3000_, sizeof(void*)*1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_traceState_3000_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v_traceState_3000_, 0);
lean_dec(v_unused_3027_);
v___x_3015_ = v_traceState_3000_;
v_isShared_3016_ = v_isSharedCheck_3026_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v_traceState_3000_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3026_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3017_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3017_);
v___x_3019_ = v___x_3015_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3017_);
lean_ctor_set_uint64(v_reuseFailAlloc_3025_, sizeof(void*)*1, v_tid_3013_);
v___x_3019_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3021_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 4, v___x_3019_);
v___x_3021_ = v___x_3011_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_env_3001_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_nextMacroScope_3002_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_ngen_3003_);
lean_ctor_set(v_reuseFailAlloc_3024_, 3, v_auxDeclNGen_3004_);
lean_ctor_set(v_reuseFailAlloc_3024_, 4, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3024_, 5, v_cache_3005_);
lean_ctor_set(v_reuseFailAlloc_3024_, 6, v_recordedDeps_3006_);
lean_ctor_set(v_reuseFailAlloc_3024_, 7, v_messages_3007_);
lean_ctor_set(v_reuseFailAlloc_3024_, 8, v_infoState_3008_);
lean_ctor_set(v_reuseFailAlloc_3024_, 9, v_snapshotTasks_3009_);
v___x_3021_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_st_ref_put(v___y_2994_, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_traces_2998_);
return v___x_3023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3029_);
lean_dec(v___y_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3032_, lean_object* v_opt_3033_){
_start:
{
lean_object* v_name_3034_; lean_object* v_defValue_3035_; lean_object* v_map_3036_; lean_object* v___x_3037_; 
v_name_3034_ = lean_ctor_get(v_opt_3033_, 0);
v_defValue_3035_ = lean_ctor_get(v_opt_3033_, 1);
v_map_3036_ = lean_ctor_get(v_opts_3032_, 0);
v___x_3037_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3036_, v_name_3034_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_inc(v_defValue_3035_);
return v_defValue_3035_;
}
else
{
lean_object* v_val_3038_; 
v_val_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_val_3038_);
lean_dec_ref_known(v___x_3037_, 1);
if (lean_obj_tag(v_val_3038_) == 3)
{
lean_object* v_v_3039_; 
v_v_3039_ = lean_ctor_get(v_val_3038_, 0);
lean_inc(v_v_3039_);
lean_dec_ref_known(v_val_3038_, 1);
return v_v_3039_;
}
else
{
lean_dec(v_val_3038_);
lean_inc(v_defValue_3035_);
return v_defValue_3035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3040_, lean_object* v_opt_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3040_, v_opt_3041_);
lean_dec_ref(v_opt_3041_);
lean_dec_ref(v_opts_3040_);
return v_res_3042_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3043_, lean_object* v_opt_3044_){
_start:
{
lean_object* v_name_3045_; lean_object* v_defValue_3046_; lean_object* v_map_3047_; lean_object* v___x_3048_; 
v_name_3045_ = lean_ctor_get(v_opt_3044_, 0);
v_defValue_3046_ = lean_ctor_get(v_opt_3044_, 1);
v_map_3047_ = lean_ctor_get(v_opts_3043_, 0);
v___x_3048_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3047_, v_name_3045_);
if (lean_obj_tag(v___x_3048_) == 0)
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_unbox(v_defValue_3046_);
return v___x_3049_;
}
else
{
lean_object* v_val_3050_; 
v_val_3050_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_val_3050_);
lean_dec_ref_known(v___x_3048_, 1);
if (lean_obj_tag(v_val_3050_) == 1)
{
uint8_t v_v_3051_; 
v_v_3051_ = lean_ctor_get_uint8(v_val_3050_, 0);
lean_dec_ref_known(v_val_3050_, 0);
return v_v_3051_;
}
else
{
uint8_t v___x_3052_; 
lean_dec(v_val_3050_);
v___x_3052_ = lean_unbox(v_defValue_3046_);
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3053_, lean_object* v_opt_3054_){
_start:
{
uint8_t v_res_3055_; lean_object* v_r_3056_; 
v_res_3055_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3053_, v_opt_3054_);
lean_dec_ref(v_opt_3054_);
lean_dec_ref(v_opts_3053_);
v_r_3056_ = lean_box(v_res_3055_);
return v_r_3056_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3057_){
_start:
{
if (lean_obj_tag(v_e_3057_) == 0)
{
uint8_t v___x_3058_; 
v___x_3058_ = 2;
return v___x_3058_;
}
else
{
lean_object* v_a_3059_; uint8_t v___x_3060_; 
v_a_3059_ = lean_ctor_get(v_e_3057_, 0);
v___x_3060_ = l_Lean_Expr_hasSyntheticSorry(v_a_3059_);
if (v___x_3060_ == 0)
{
uint8_t v___x_3061_; 
v___x_3061_ = 0;
return v___x_3061_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = 1;
return v___x_3062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3063_){
_start:
{
uint8_t v_res_3064_; lean_object* v_r_3065_; 
v_res_3064_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3063_);
lean_dec_ref(v_e_3063_);
v_r_3065_ = lean_box(v_res_3064_);
return v_r_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3066_, size_t v_i_3067_, lean_object* v_bs_3068_){
_start:
{
uint8_t v___x_3069_; 
v___x_3069_ = lean_usize_dec_lt(v_i_3067_, v_sz_3066_);
if (v___x_3069_ == 0)
{
return v_bs_3068_;
}
else
{
lean_object* v_v_3070_; lean_object* v_msg_3071_; lean_object* v___x_3072_; lean_object* v_bs_x27_3073_; size_t v___x_3074_; size_t v___x_3075_; lean_object* v___x_3076_; 
v_v_3070_ = lean_array_uget_borrowed(v_bs_3068_, v_i_3067_);
v_msg_3071_ = lean_ctor_get(v_v_3070_, 1);
lean_inc_ref(v_msg_3071_);
v___x_3072_ = lean_unsigned_to_nat(0u);
v_bs_x27_3073_ = lean_array_uset(v_bs_3068_, v_i_3067_, v___x_3072_);
v___x_3074_ = ((size_t)1ULL);
v___x_3075_ = lean_usize_add(v_i_3067_, v___x_3074_);
v___x_3076_ = lean_array_uset(v_bs_x27_3073_, v_i_3067_, v_msg_3071_);
v_i_3067_ = v___x_3075_;
v_bs_3068_ = v___x_3076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3078_, lean_object* v_i_3079_, lean_object* v_bs_3080_){
_start:
{
size_t v_sz_boxed_3081_; size_t v_i_boxed_3082_; lean_object* v_res_3083_; 
v_sz_boxed_3081_ = lean_unbox_usize(v_sz_3078_);
lean_dec(v_sz_3078_);
v_i_boxed_3082_ = lean_unbox_usize(v_i_3079_);
lean_dec(v_i_3079_);
v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3081_, v_i_boxed_3082_, v_bs_3080_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3084_, lean_object* v_data_3085_, lean_object* v_ref_3086_, lean_object* v_msg_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_toCold_3093_; lean_object* v_currRecDepth_3094_; lean_object* v_ref_3095_; uint16_t v_optionFlags_3096_; uint8_t v_suppressElabErrors_3097_; uint8_t v_isRecordingDeps_3098_; lean_object* v_ref_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v_traceState_3102_; lean_object* v_traces_3103_; lean_object* v___x_3104_; size_t v_sz_3105_; size_t v___x_3106_; lean_object* v___x_3107_; lean_object* v_msg_3108_; lean_object* v___x_3109_; lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3148_; 
v_toCold_3093_ = lean_ctor_get(v___y_3090_, 0);
v_currRecDepth_3094_ = lean_ctor_get(v___y_3090_, 1);
v_ref_3095_ = lean_ctor_get(v___y_3090_, 2);
v_optionFlags_3096_ = lean_ctor_get_uint16(v___y_3090_, sizeof(void*)*3);
v_suppressElabErrors_3097_ = lean_ctor_get_uint8(v___y_3090_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3098_ = lean_ctor_get_uint8(v___y_3090_, sizeof(void*)*3 + 3);
v_ref_3099_ = l_Lean_replaceRef(v_ref_3086_, v_ref_3095_);
lean_inc(v_currRecDepth_3094_);
lean_inc_ref(v_toCold_3093_);
v___x_3100_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3100_, 0, v_toCold_3093_);
lean_ctor_set(v___x_3100_, 1, v_currRecDepth_3094_);
lean_ctor_set(v___x_3100_, 2, v_ref_3099_);
lean_ctor_set_uint16(v___x_3100_, sizeof(void*)*3, v_optionFlags_3096_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*3 + 2, v_suppressElabErrors_3097_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*3 + 3, v_isRecordingDeps_3098_);
v___x_3101_ = lean_st_ref_get(v___y_3091_);
v_traceState_3102_ = lean_ctor_get(v___x_3101_, 4);
lean_inc_ref(v_traceState_3102_);
lean_dec(v___x_3101_);
v_traces_3103_ = lean_ctor_get(v_traceState_3102_, 0);
lean_inc_ref(v_traces_3103_);
lean_dec_ref(v_traceState_3102_);
v___x_3104_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3103_);
lean_dec_ref(v_traces_3103_);
v_sz_3105_ = lean_array_size(v___x_3104_);
v___x_3106_ = ((size_t)0ULL);
v___x_3107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3105_, v___x_3106_, v___x_3104_);
v_msg_3108_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3108_, 0, v_data_3085_);
lean_ctor_set(v_msg_3108_, 1, v_msg_3087_);
lean_ctor_set(v_msg_3108_, 2, v___x_3107_);
v___x_3109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3108_, v___y_3088_, v___y_3089_, v___x_3100_, v___y_3091_);
lean_dec_ref_known(v___x_3100_, 3);
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3148_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3148_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v_traceState_3115_; lean_object* v_env_3116_; lean_object* v_nextMacroScope_3117_; lean_object* v_ngen_3118_; lean_object* v_auxDeclNGen_3119_; lean_object* v_cache_3120_; lean_object* v_recordedDeps_3121_; lean_object* v_messages_3122_; lean_object* v_infoState_3123_; lean_object* v_snapshotTasks_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3147_; 
v___x_3114_ = lean_st_ref_take(v___y_3091_);
v_traceState_3115_ = lean_ctor_get(v___x_3114_, 4);
v_env_3116_ = lean_ctor_get(v___x_3114_, 0);
v_nextMacroScope_3117_ = lean_ctor_get(v___x_3114_, 1);
v_ngen_3118_ = lean_ctor_get(v___x_3114_, 2);
v_auxDeclNGen_3119_ = lean_ctor_get(v___x_3114_, 3);
v_cache_3120_ = lean_ctor_get(v___x_3114_, 5);
v_recordedDeps_3121_ = lean_ctor_get(v___x_3114_, 6);
v_messages_3122_ = lean_ctor_get(v___x_3114_, 7);
v_infoState_3123_ = lean_ctor_get(v___x_3114_, 8);
v_snapshotTasks_3124_ = lean_ctor_get(v___x_3114_, 9);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3126_ = v___x_3114_;
v_isShared_3127_ = v_isSharedCheck_3147_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_snapshotTasks_3124_);
lean_inc(v_infoState_3123_);
lean_inc(v_messages_3122_);
lean_inc(v_recordedDeps_3121_);
lean_inc(v_cache_3120_);
lean_inc(v_traceState_3115_);
lean_inc(v_auxDeclNGen_3119_);
lean_inc(v_ngen_3118_);
lean_inc(v_nextMacroScope_3117_);
lean_inc(v_env_3116_);
lean_dec(v___x_3114_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3147_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
uint64_t v_tid_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3145_; 
v_tid_3128_ = lean_ctor_get_uint64(v_traceState_3115_, sizeof(void*)*1);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_traceState_3115_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; 
v_unused_3146_ = lean_ctor_get(v_traceState_3115_, 0);
lean_dec(v_unused_3146_);
v___x_3130_ = v_traceState_3115_;
v_isShared_3131_ = v_isSharedCheck_3145_;
goto v_resetjp_3129_;
}
else
{
lean_dec(v_traceState_3115_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3145_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v_ref_3086_);
lean_ctor_set(v___x_3133_, 1, v_a_3110_);
v___x_3134_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3084_, v___x_3133_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3134_);
v___x_3136_ = v___x_3130_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3134_);
lean_ctor_set_uint64(v_reuseFailAlloc_3144_, sizeof(void*)*1, v_tid_3128_);
v___x_3136_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 4, v___x_3136_);
v___x_3138_ = v___x_3126_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_env_3116_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_nextMacroScope_3117_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_ngen_3118_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_auxDeclNGen_3119_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3143_, 5, v_cache_3120_);
lean_ctor_set(v_reuseFailAlloc_3143_, 6, v_recordedDeps_3121_);
lean_ctor_set(v_reuseFailAlloc_3143_, 7, v_messages_3122_);
lean_ctor_set(v_reuseFailAlloc_3143_, 8, v_infoState_3123_);
lean_ctor_set(v_reuseFailAlloc_3143_, 9, v_snapshotTasks_3124_);
v___x_3138_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = lean_st_ref_put(v___y_3091_, v___x_3138_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3132_);
v___x_3141_ = v___x_3112_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3132_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3149_, lean_object* v_data_3150_, lean_object* v_ref_3151_, lean_object* v_msg_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3149_, v_data_3150_, v_ref_3151_, v_msg_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3159_){
_start:
{
if (lean_obj_tag(v_x_3159_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
v_a_3161_ = lean_ctor_get(v_x_3159_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v_x_3159_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v_x_3159_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v_x_3159_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 1);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
v_a_3169_ = lean_ctor_get(v_x_3159_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_x_3159_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v_x_3159_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v_x_3159_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 0);
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3177_);
return v_res_3179_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3180_; double v___x_3181_; 
v___x_3180_ = lean_unsigned_to_nat(0u);
v___x_3181_ = lean_float_of_nat(v___x_3180_);
return v___x_3181_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3184_ = l_Lean_stringToMessageData(v___x_3183_);
return v___x_3184_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3185_; double v___x_3186_; 
v___x_3185_ = lean_unsigned_to_nat(1000u);
v___x_3186_ = lean_float_of_nat(v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3187_, uint8_t v_collapsed_3188_, lean_object* v_tag_3189_, lean_object* v_opts_3190_, uint8_t v_clsEnabled_3191_, lean_object* v_oldTraces_3192_, lean_object* v_msg_3193_, lean_object* v_resStartStop_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_fst_3200_; lean_object* v_snd_3201_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v_data_3205_; lean_object* v_fst_3216_; lean_object* v_snd_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; lean_object* v___y_3221_; lean_object* v_a_3222_; uint8_t v___y_3237_; double v___y_3269_; 
v_fst_3200_ = lean_ctor_get(v_resStartStop_3194_, 0);
lean_inc(v_fst_3200_);
v_snd_3201_ = lean_ctor_get(v_resStartStop_3194_, 1);
lean_inc(v_snd_3201_);
lean_dec_ref(v_resStartStop_3194_);
v_fst_3216_ = lean_ctor_get(v_snd_3201_, 0);
lean_inc(v_fst_3216_);
v_snd_3217_ = lean_ctor_get(v_snd_3201_, 1);
lean_inc(v_snd_3217_);
lean_dec(v_snd_3201_);
v___x_3218_ = l_Lean_trace_profiler;
v___x_3219_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3190_, v___x_3218_);
if (v___x_3219_ == 0)
{
v___y_3237_ = v___x_3219_;
goto v___jp_3236_;
}
else
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3275_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3190_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; double v___x_3278_; double v___x_3279_; double v___x_3280_; 
v___x_3276_ = l_Lean_trace_profiler_threshold;
v___x_3277_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3190_, v___x_3276_);
v___x_3278_ = lean_float_of_nat(v___x_3277_);
v___x_3279_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3280_ = lean_float_div(v___x_3278_, v___x_3279_);
v___y_3269_ = v___x_3280_;
goto v___jp_3268_;
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3282_; double v___x_3283_; 
v___x_3281_ = l_Lean_trace_profiler_threshold;
v___x_3282_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3190_, v___x_3281_);
v___x_3283_ = lean_float_of_nat(v___x_3282_);
v___y_3269_ = v___x_3283_;
goto v___jp_3268_;
}
}
v___jp_3202_:
{
lean_object* v___x_3206_; 
lean_inc(v___y_3204_);
v___x_3206_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3192_, v_data_3205_, v___y_3204_, v___y_3203_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v___x_3207_; 
lean_dec_ref_known(v___x_3206_, 1);
v___x_3207_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3200_);
return v___x_3207_;
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_fst_3200_);
v_a_3208_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3206_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3206_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
v___jp_3220_:
{
uint8_t v_result_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; double v___x_3226_; lean_object* v_data_3227_; 
v_result_3223_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3200_);
v___x_3224_ = lean_box(v_result_3223_);
v___x_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
v___x_3226_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3189_);
lean_inc_ref(v___x_3225_);
lean_inc(v_cls_3187_);
v_data_3227_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3227_, 0, v_cls_3187_);
lean_ctor_set(v_data_3227_, 1, v___x_3225_);
lean_ctor_set(v_data_3227_, 2, v_tag_3189_);
lean_ctor_set_float(v_data_3227_, sizeof(void*)*3, v___x_3226_);
lean_ctor_set_float(v_data_3227_, sizeof(void*)*3 + 8, v___x_3226_);
lean_ctor_set_uint8(v_data_3227_, sizeof(void*)*3 + 16, v_collapsed_3188_);
if (v___x_3219_ == 0)
{
lean_dec_ref_known(v___x_3225_, 1);
lean_dec(v_snd_3217_);
lean_dec(v_fst_3216_);
lean_dec_ref(v_tag_3189_);
lean_dec(v_cls_3187_);
v___y_3203_ = v_a_3222_;
v___y_3204_ = v___y_3221_;
v_data_3205_ = v_data_3227_;
goto v___jp_3202_;
}
else
{
lean_object* v_data_3228_; double v___x_3229_; double v___x_3230_; 
lean_dec_ref_known(v_data_3227_, 3);
v_data_3228_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3228_, 0, v_cls_3187_);
lean_ctor_set(v_data_3228_, 1, v___x_3225_);
lean_ctor_set(v_data_3228_, 2, v_tag_3189_);
v___x_3229_ = lean_unbox_float(v_fst_3216_);
lean_dec(v_fst_3216_);
lean_ctor_set_float(v_data_3228_, sizeof(void*)*3, v___x_3229_);
v___x_3230_ = lean_unbox_float(v_snd_3217_);
lean_dec(v_snd_3217_);
lean_ctor_set_float(v_data_3228_, sizeof(void*)*3 + 8, v___x_3230_);
lean_ctor_set_uint8(v_data_3228_, sizeof(void*)*3 + 16, v_collapsed_3188_);
v___y_3203_ = v_a_3222_;
v___y_3204_ = v___y_3221_;
v_data_3205_ = v_data_3228_;
goto v___jp_3202_;
}
}
v___jp_3231_:
{
lean_object* v_ref_3232_; lean_object* v___x_3233_; 
v_ref_3232_ = lean_ctor_get(v___y_3197_, 2);
lean_inc(v___y_3198_);
lean_inc_ref(v___y_3197_);
lean_inc(v___y_3196_);
lean_inc_ref(v___y_3195_);
lean_inc(v_fst_3200_);
v___x_3233_ = lean_apply_6(v_msg_3193_, v_fst_3200_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, lean_box(0));
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3233_, 1);
v___y_3221_ = v_ref_3232_;
v_a_3222_ = v_a_3234_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3235_; 
lean_dec_ref_known(v___x_3233_, 1);
v___x_3235_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3221_ = v_ref_3232_;
v_a_3222_ = v___x_3235_;
goto v___jp_3220_;
}
}
v___jp_3236_:
{
if (v_clsEnabled_3191_ == 0)
{
if (v___y_3237_ == 0)
{
lean_object* v___x_3238_; lean_object* v_traceState_3239_; lean_object* v_env_3240_; lean_object* v_nextMacroScope_3241_; lean_object* v_ngen_3242_; lean_object* v_auxDeclNGen_3243_; lean_object* v_cache_3244_; lean_object* v_recordedDeps_3245_; lean_object* v_messages_3246_; lean_object* v_infoState_3247_; lean_object* v_snapshotTasks_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_snd_3217_);
lean_dec(v_fst_3216_);
lean_dec_ref(v_msg_3193_);
lean_dec_ref(v_tag_3189_);
lean_dec(v_cls_3187_);
v___x_3238_ = lean_st_ref_take(v___y_3198_);
v_traceState_3239_ = lean_ctor_get(v___x_3238_, 4);
v_env_3240_ = lean_ctor_get(v___x_3238_, 0);
v_nextMacroScope_3241_ = lean_ctor_get(v___x_3238_, 1);
v_ngen_3242_ = lean_ctor_get(v___x_3238_, 2);
v_auxDeclNGen_3243_ = lean_ctor_get(v___x_3238_, 3);
v_cache_3244_ = lean_ctor_get(v___x_3238_, 5);
v_recordedDeps_3245_ = lean_ctor_get(v___x_3238_, 6);
v_messages_3246_ = lean_ctor_get(v___x_3238_, 7);
v_infoState_3247_ = lean_ctor_get(v___x_3238_, 8);
v_snapshotTasks_3248_ = lean_ctor_get(v___x_3238_, 9);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3250_ = v___x_3238_;
v_isShared_3251_ = v_isSharedCheck_3267_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_snapshotTasks_3248_);
lean_inc(v_infoState_3247_);
lean_inc(v_messages_3246_);
lean_inc(v_recordedDeps_3245_);
lean_inc(v_cache_3244_);
lean_inc(v_traceState_3239_);
lean_inc(v_auxDeclNGen_3243_);
lean_inc(v_ngen_3242_);
lean_inc(v_nextMacroScope_3241_);
lean_inc(v_env_3240_);
lean_dec(v___x_3238_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3267_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
uint64_t v_tid_3252_; lean_object* v_traces_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3266_; 
v_tid_3252_ = lean_ctor_get_uint64(v_traceState_3239_, sizeof(void*)*1);
v_traces_3253_ = lean_ctor_get(v_traceState_3239_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_traceState_3239_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3255_ = v_traceState_3239_;
v_isShared_3256_ = v_isSharedCheck_3266_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_traces_3253_);
lean_dec(v_traceState_3239_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3266_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3257_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3192_, v_traces_3253_);
lean_dec_ref(v_traces_3253_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3257_);
v___x_3259_ = v___x_3255_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3257_);
lean_ctor_set_uint64(v_reuseFailAlloc_3265_, sizeof(void*)*1, v_tid_3252_);
v___x_3259_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3261_; 
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 4, v___x_3259_);
v___x_3261_ = v___x_3250_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_env_3240_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_nextMacroScope_3241_);
lean_ctor_set(v_reuseFailAlloc_3264_, 2, v_ngen_3242_);
lean_ctor_set(v_reuseFailAlloc_3264_, 3, v_auxDeclNGen_3243_);
lean_ctor_set(v_reuseFailAlloc_3264_, 4, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3264_, 5, v_cache_3244_);
lean_ctor_set(v_reuseFailAlloc_3264_, 6, v_recordedDeps_3245_);
lean_ctor_set(v_reuseFailAlloc_3264_, 7, v_messages_3246_);
lean_ctor_set(v_reuseFailAlloc_3264_, 8, v_infoState_3247_);
lean_ctor_set(v_reuseFailAlloc_3264_, 9, v_snapshotTasks_3248_);
v___x_3261_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = lean_st_ref_put(v___y_3198_, v___x_3261_);
v___x_3263_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3200_);
return v___x_3263_;
}
}
}
}
}
else
{
goto v___jp_3231_;
}
}
else
{
goto v___jp_3231_;
}
}
v___jp_3268_:
{
double v___x_3270_; double v___x_3271_; double v___x_3272_; uint8_t v___x_3273_; 
v___x_3270_ = lean_unbox_float(v_snd_3217_);
v___x_3271_ = lean_unbox_float(v_fst_3216_);
v___x_3272_ = lean_float_sub(v___x_3270_, v___x_3271_);
v___x_3273_ = lean_float_decLt(v___y_3269_, v___x_3272_);
v___y_3237_ = v___x_3273_;
goto v___jp_3236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3284_, lean_object* v_collapsed_3285_, lean_object* v_tag_3286_, lean_object* v_opts_3287_, lean_object* v_clsEnabled_3288_, lean_object* v_oldTraces_3289_, lean_object* v_msg_3290_, lean_object* v_resStartStop_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v_collapsed_boxed_3297_; uint8_t v_clsEnabled_boxed_3298_; lean_object* v_res_3299_; 
v_collapsed_boxed_3297_ = lean_unbox(v_collapsed_3285_);
v_clsEnabled_boxed_3298_ = lean_unbox(v_clsEnabled_3288_);
v_res_3299_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3284_, v_collapsed_boxed_3297_, v_tag_3286_, v_opts_3287_, v_clsEnabled_boxed_3298_, v_oldTraces_3289_, v_msg_3290_, v_resStartStop_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec_ref(v_opts_3287_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
if (lean_obj_tag(v_a_3300_) == 0)
{
lean_object* v___x_3302_; 
v___x_3302_ = l_List_reverse___redArg(v_a_3301_);
return v___x_3302_;
}
else
{
lean_object* v_head_3303_; lean_object* v_tail_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3313_; 
v_head_3303_ = lean_ctor_get(v_a_3300_, 0);
v_tail_3304_ = lean_ctor_get(v_a_3300_, 1);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_a_3300_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3306_ = v_a_3300_;
v_isShared_3307_ = v_isSharedCheck_3313_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_tail_3304_);
lean_inc(v_head_3303_);
lean_dec(v_a_3300_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3313_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3310_; 
v___x_3308_ = l_Lean_MessageData_ofExpr(v_head_3303_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 1, v_a_3301_);
lean_ctor_set(v___x_3306_, 0, v___x_3308_);
v___x_3310_ = v___x_3306_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3308_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v_a_3301_);
v___x_3310_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
v_a_3300_ = v_tail_3304_;
v_a_3301_ = v___x_3310_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3314_, lean_object* v_xs_3315_, lean_object* v_x_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3322_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3323_ = l_Lean_MessageData_ofName(v_f_3314_);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = lean_array_to_list(v_xs_3315_);
v___x_3328_ = lean_box(0);
v___x_3329_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3327_, v___x_3328_);
v___x_3330_ = l_Lean_MessageData_ofList(v___x_3329_);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3326_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3333_, lean_object* v_xs_3334_, lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3333_, v_xs_3334_, v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec_ref(v_x_3335_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3344_, lean_object* v_msg_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_ref_3351_; lean_object* v___x_3352_; lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3398_; 
v_ref_3351_ = lean_ctor_get(v___y_3348_, 2);
v___x_3352_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3398_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3398_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v_traceState_3358_; lean_object* v_env_3359_; lean_object* v_nextMacroScope_3360_; lean_object* v_ngen_3361_; lean_object* v_auxDeclNGen_3362_; lean_object* v_cache_3363_; lean_object* v_recordedDeps_3364_; lean_object* v_messages_3365_; lean_object* v_infoState_3366_; lean_object* v_snapshotTasks_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3397_; 
v___x_3357_ = lean_st_ref_take(v___y_3349_);
v_traceState_3358_ = lean_ctor_get(v___x_3357_, 4);
v_env_3359_ = lean_ctor_get(v___x_3357_, 0);
v_nextMacroScope_3360_ = lean_ctor_get(v___x_3357_, 1);
v_ngen_3361_ = lean_ctor_get(v___x_3357_, 2);
v_auxDeclNGen_3362_ = lean_ctor_get(v___x_3357_, 3);
v_cache_3363_ = lean_ctor_get(v___x_3357_, 5);
v_recordedDeps_3364_ = lean_ctor_get(v___x_3357_, 6);
v_messages_3365_ = lean_ctor_get(v___x_3357_, 7);
v_infoState_3366_ = lean_ctor_get(v___x_3357_, 8);
v_snapshotTasks_3367_ = lean_ctor_get(v___x_3357_, 9);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3369_ = v___x_3357_;
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snapshotTasks_3367_);
lean_inc(v_infoState_3366_);
lean_inc(v_messages_3365_);
lean_inc(v_recordedDeps_3364_);
lean_inc(v_cache_3363_);
lean_inc(v_traceState_3358_);
lean_inc(v_auxDeclNGen_3362_);
lean_inc(v_ngen_3361_);
lean_inc(v_nextMacroScope_3360_);
lean_inc(v_env_3359_);
lean_dec(v___x_3357_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
uint64_t v_tid_3371_; lean_object* v_traces_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3396_; 
v_tid_3371_ = lean_ctor_get_uint64(v_traceState_3358_, sizeof(void*)*1);
v_traces_3372_ = lean_ctor_get(v_traceState_3358_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_traceState_3358_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3374_ = v_traceState_3358_;
v_isShared_3375_ = v_isSharedCheck_3396_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_traces_3372_);
lean_dec(v_traceState_3358_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3396_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; double v___x_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_box(0);
v___x_3378_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3379_ = 0;
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3381_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3381_, 0, v_cls_3344_);
lean_ctor_set(v___x_3381_, 1, v___x_3377_);
lean_ctor_set(v___x_3381_, 2, v___x_3380_);
lean_ctor_set_float(v___x_3381_, sizeof(void*)*3, v___x_3378_);
lean_ctor_set_float(v___x_3381_, sizeof(void*)*3 + 8, v___x_3378_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*3 + 16, v___x_3379_);
v___x_3382_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3383_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v_a_3353_);
lean_ctor_set(v___x_3383_, 2, v___x_3382_);
lean_inc(v_ref_3351_);
v___x_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3384_, 0, v_ref_3351_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = l_Lean_PersistentArray_push___redArg(v_traces_3372_, v___x_3384_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3385_);
v___x_3387_ = v___x_3374_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3385_);
lean_ctor_set_uint64(v_reuseFailAlloc_3395_, sizeof(void*)*1, v_tid_3371_);
v___x_3387_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3389_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 4, v___x_3387_);
v___x_3389_ = v___x_3369_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_env_3359_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_nextMacroScope_3360_);
lean_ctor_set(v_reuseFailAlloc_3394_, 2, v_ngen_3361_);
lean_ctor_set(v_reuseFailAlloc_3394_, 3, v_auxDeclNGen_3362_);
lean_ctor_set(v_reuseFailAlloc_3394_, 4, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3394_, 5, v_cache_3363_);
lean_ctor_set(v_reuseFailAlloc_3394_, 6, v_recordedDeps_3364_);
lean_ctor_set(v_reuseFailAlloc_3394_, 7, v_messages_3365_);
lean_ctor_set(v_reuseFailAlloc_3394_, 8, v_infoState_3366_);
lean_ctor_set(v_reuseFailAlloc_3394_, 9, v_snapshotTasks_3367_);
v___x_3389_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_st_ref_put(v___y_3349_, v___x_3389_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3376_);
v___x_3392_ = v___x_3355_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3376_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3399_, lean_object* v_msg_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3399_, v_msg_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3407_, lean_object* v_xs_3408_, lean_object* v_k_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v_toCold_3415_; lean_object* v_options_3416_; uint8_t v_hasTrace_3417_; 
v_toCold_3415_ = lean_ctor_get(v_a_3412_, 0);
v_options_3416_ = lean_ctor_get(v_toCold_3415_, 2);
v_hasTrace_3417_ = lean_ctor_get_uint8(v_options_3416_, sizeof(void*)*1);
if (v_hasTrace_3417_ == 0)
{
lean_object* v___x_3418_; 
lean_dec_ref(v_xs_3408_);
lean_dec(v_f_3407_);
lean_inc(v_a_3413_);
lean_inc_ref(v_a_3412_);
lean_inc(v_a_3411_);
lean_inc_ref(v_a_3410_);
v___x_3418_ = lean_apply_5(v_k_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, lean_box(0));
return v___x_3418_;
}
else
{
lean_object* v_inheritedTraceOptions_3419_; lean_object* v___f_3420_; lean_object* v___y_3422_; lean_object* v___y_3423_; uint8_t v___y_3424_; lean_object* v___y_3448_; lean_object* v_a_3449_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v_a_3459_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v_a_3474_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; uint8_t v___y_3480_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v_a_3490_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v_a_3496_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v_a_3501_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v_a_3513_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; uint8_t v___y_3519_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v_a_3529_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v_a_3535_; 
v_inheritedTraceOptions_3419_ = lean_ctor_get(v_toCold_3415_, 11);
v___f_3420_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3420_, 0, v_f_3407_);
lean_closure_set(v___f_3420_, 1, v_xs_3408_);
v___x_3452_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3453_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3454_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3455_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3416_, v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = l_Lean_trace_profiler;
v___x_3563_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3416_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
lean_dec_ref(v___f_3420_);
lean_inc(v_a_3413_);
lean_inc_ref(v_a_3412_);
lean_inc(v_a_3411_);
lean_inc_ref(v_a_3410_);
v___x_3564_ = lean_apply_5(v_k_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, lean_box(0));
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
v___x_3566_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3567_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3416_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_dec(v_a_3565_);
return v___x_3564_;
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec_ref_known(v___x_3564_, 1);
lean_inc(v_a_3565_);
v___x_3569_ = l_Lean_MessageData_ofExpr(v_a_3565_);
v___x_3570_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3566_, v___x_3569_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v___x_3570_, 0);
lean_dec(v_unused_3578_);
v___x_3572_ = v___x_3570_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_dec(v___x_3570_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v_a_3565_);
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3565_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v_a_3565_);
v_a_3579_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3570_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3570_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
lean_inc(v_a_3579_);
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
v___y_3448_ = v___x_3584_;
v_a_3449_ = v_a_3579_;
goto v___jp_3447_;
}
}
}
}
}
else
{
lean_object* v_a_3587_; 
v_a_3587_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3587_);
v___y_3448_ = v___x_3564_;
v_a_3449_ = v_a_3587_;
goto v___jp_3447_;
}
}
else
{
goto v___jp_3537_;
}
}
else
{
goto v___jp_3537_;
}
v___jp_3421_:
{
if (v___y_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
lean_dec_ref(v___y_3423_);
v___x_3425_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3426_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3427_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3416_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___y_3422_);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_inc_ref(v___y_3422_);
v___x_3429_ = l_Lean_Exception_toMessageData(v___y_3422_);
v___x_3430_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3425_, v___x_3429_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3437_ == 0)
{
lean_object* v_unused_3438_; 
v_unused_3438_ = lean_ctor_get(v___x_3430_, 0);
lean_dec(v_unused_3438_);
v___x_3432_ = v___x_3430_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_dec(v___x_3430_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 1);
lean_ctor_set(v___x_3432_, 0, v___y_3422_);
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___y_3422_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec_ref(v___y_3422_);
v_a_3439_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3430_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3430_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3422_);
return v___y_3423_;
}
}
v___jp_3447_:
{
uint8_t v___x_3450_; 
v___x_3450_ = l_Lean_Exception_isInterrupt(v_a_3449_);
if (v___x_3450_ == 0)
{
uint8_t v___x_3451_; 
lean_inc_ref(v_a_3449_);
v___x_3451_ = l_Lean_Exception_isRuntime(v_a_3449_);
v___y_3422_ = v_a_3449_;
v___y_3423_ = v___y_3448_;
v___y_3424_ = v___x_3451_;
goto v___jp_3421_;
}
else
{
v___y_3422_ = v_a_3449_;
v___y_3423_ = v___y_3448_;
v___y_3424_ = v___x_3450_;
goto v___jp_3421_;
}
}
v___jp_3456_:
{
lean_object* v___x_3460_; double v___x_3461_; double v___x_3462_; double v___x_3463_; double v___x_3464_; double v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3460_ = lean_io_mono_nanos_now();
v___x_3461_ = lean_float_of_nat(v___y_3457_);
v___x_3462_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3463_ = lean_float_div(v___x_3461_, v___x_3462_);
v___x_3464_ = lean_float_of_nat(v___x_3460_);
v___x_3465_ = lean_float_div(v___x_3464_, v___x_3462_);
v___x_3466_ = lean_box_float(v___x_3463_);
v___x_3467_ = lean_box_float(v___x_3465_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v_a_3459_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3452_, v_hasTrace_3417_, v___x_3453_, v_options_3416_, v___x_3455_, v___y_3458_, v___f_3420_, v___x_3469_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
return v___x_3470_;
}
v___jp_3471_:
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v_a_3474_);
v___y_3457_ = v___y_3472_;
v___y_3458_ = v___y_3473_;
v_a_3459_ = v___x_3475_;
goto v___jp_3456_;
}
v___jp_3476_:
{
if (v___y_3480_ == 0)
{
lean_object* v___x_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
v___x_3481_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3482_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3483_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3416_, v___x_3482_);
if (v___x_3483_ == 0)
{
v___y_3472_ = v___y_3477_;
v___y_3473_ = v___y_3479_;
v_a_3474_ = v___y_3478_;
goto v___jp_3471_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
lean_inc_ref(v___y_3478_);
v___x_3484_ = l_Lean_Exception_toMessageData(v___y_3478_);
v___x_3485_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3481_, v___x_3484_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_dec_ref_known(v___x_3485_, 1);
v___y_3472_ = v___y_3477_;
v___y_3473_ = v___y_3479_;
v_a_3474_ = v___y_3478_;
goto v___jp_3471_;
}
else
{
lean_object* v_a_3486_; 
lean_dec_ref(v___y_3478_);
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___y_3472_ = v___y_3477_;
v___y_3473_ = v___y_3479_;
v_a_3474_ = v_a_3486_;
goto v___jp_3471_;
}
}
}
else
{
v___y_3472_ = v___y_3477_;
v___y_3473_ = v___y_3479_;
v_a_3474_ = v___y_3478_;
goto v___jp_3471_;
}
}
v___jp_3487_:
{
uint8_t v___x_3491_; 
v___x_3491_ = l_Lean_Exception_isInterrupt(v_a_3490_);
if (v___x_3491_ == 0)
{
uint8_t v___x_3492_; 
lean_inc_ref(v_a_3490_);
v___x_3492_ = l_Lean_Exception_isRuntime(v_a_3490_);
v___y_3477_ = v___y_3488_;
v___y_3478_ = v_a_3490_;
v___y_3479_ = v___y_3489_;
v___y_3480_ = v___x_3492_;
goto v___jp_3476_;
}
else
{
v___y_3477_ = v___y_3488_;
v___y_3478_ = v_a_3490_;
v___y_3479_ = v___y_3489_;
v___y_3480_ = v___x_3491_;
goto v___jp_3476_;
}
}
v___jp_3493_:
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3497_, 0, v_a_3496_);
v___y_3457_ = v___y_3494_;
v___y_3458_ = v___y_3495_;
v_a_3459_ = v___x_3497_;
goto v___jp_3456_;
}
v___jp_3498_:
{
lean_object* v___x_3502_; double v___x_3503_; double v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3502_ = lean_io_get_num_heartbeats();
v___x_3503_ = lean_float_of_nat(v___y_3499_);
v___x_3504_ = lean_float_of_nat(v___x_3502_);
v___x_3505_ = lean_box_float(v___x_3503_);
v___x_3506_ = lean_box_float(v___x_3504_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_a_3501_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v___x_3509_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3452_, v_hasTrace_3417_, v___x_3453_, v_options_3416_, v___x_3455_, v___y_3500_, v___f_3420_, v___x_3508_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
return v___x_3509_;
}
v___jp_3510_:
{
lean_object* v___x_3514_; 
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v_a_3513_);
v___y_3499_ = v___y_3511_;
v___y_3500_ = v___y_3512_;
v_a_3501_ = v___x_3514_;
goto v___jp_3498_;
}
v___jp_3515_:
{
if (v___y_3519_ == 0)
{
lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3521_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3522_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3416_, v___x_3521_);
if (v___x_3522_ == 0)
{
v___y_3511_ = v___y_3517_;
v___y_3512_ = v___y_3518_;
v_a_3513_ = v___y_3516_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
lean_inc_ref(v___y_3516_);
v___x_3523_ = l_Lean_Exception_toMessageData(v___y_3516_);
v___x_3524_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3520_, v___x_3523_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_dec_ref_known(v___x_3524_, 1);
v___y_3511_ = v___y_3517_;
v___y_3512_ = v___y_3518_;
v_a_3513_ = v___y_3516_;
goto v___jp_3510_;
}
else
{
lean_object* v_a_3525_; 
lean_dec_ref(v___y_3516_);
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
v___y_3511_ = v___y_3517_;
v___y_3512_ = v___y_3518_;
v_a_3513_ = v_a_3525_;
goto v___jp_3510_;
}
}
}
else
{
v___y_3511_ = v___y_3517_;
v___y_3512_ = v___y_3518_;
v_a_3513_ = v___y_3516_;
goto v___jp_3510_;
}
}
v___jp_3526_:
{
uint8_t v___x_3530_; 
v___x_3530_ = l_Lean_Exception_isInterrupt(v_a_3529_);
if (v___x_3530_ == 0)
{
uint8_t v___x_3531_; 
lean_inc_ref(v_a_3529_);
v___x_3531_ = l_Lean_Exception_isRuntime(v_a_3529_);
v___y_3516_ = v_a_3529_;
v___y_3517_ = v___y_3527_;
v___y_3518_ = v___y_3528_;
v___y_3519_ = v___x_3531_;
goto v___jp_3515_;
}
else
{
v___y_3516_ = v_a_3529_;
v___y_3517_ = v___y_3527_;
v___y_3518_ = v___y_3528_;
v___y_3519_ = v___x_3530_;
goto v___jp_3515_;
}
}
v___jp_3532_:
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_a_3535_);
v___y_3499_ = v___y_3533_;
v___y_3500_ = v___y_3534_;
v_a_3501_ = v___x_3536_;
goto v___jp_3498_;
}
v___jp_3537_:
{
lean_object* v___x_3538_; lean_object* v_a_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v___x_3538_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3413_);
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref(v___x_3538_);
v___x_3540_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3541_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3416_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_io_mono_nanos_now();
lean_inc(v_a_3413_);
lean_inc_ref(v_a_3412_);
lean_inc(v_a_3411_);
lean_inc_ref(v_a_3410_);
v___x_3543_ = lean_apply_5(v_k_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, lean_box(0));
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3546_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3416_, v___x_3546_);
if (v___x_3547_ == 0)
{
v___y_3494_ = v___x_3542_;
v___y_3495_ = v_a_3539_;
v_a_3496_ = v_a_3544_;
goto v___jp_3493_;
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_inc(v_a_3544_);
v___x_3548_ = l_Lean_MessageData_ofExpr(v_a_3544_);
v___x_3549_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3545_, v___x_3548_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_dec_ref_known(v___x_3549_, 1);
v___y_3494_ = v___x_3542_;
v___y_3495_ = v_a_3539_;
v_a_3496_ = v_a_3544_;
goto v___jp_3493_;
}
else
{
lean_object* v_a_3550_; 
lean_dec(v_a_3544_);
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___y_3488_ = v___x_3542_;
v___y_3489_ = v_a_3539_;
v_a_3490_ = v_a_3550_;
goto v___jp_3487_;
}
}
}
else
{
lean_object* v_a_3551_; 
v_a_3551_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3543_, 1);
v___y_3488_ = v___x_3542_;
v___y_3489_ = v_a_3539_;
v_a_3490_ = v_a_3551_;
goto v___jp_3487_;
}
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3413_);
lean_inc_ref(v_a_3412_);
lean_inc(v_a_3411_);
lean_inc_ref(v_a_3410_);
v___x_3553_ = lean_apply_5(v_k_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, lean_box(0));
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3556_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3557_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3416_, v___x_3556_);
if (v___x_3557_ == 0)
{
v___y_3533_ = v___x_3552_;
v___y_3534_ = v_a_3539_;
v_a_3535_ = v_a_3554_;
goto v___jp_3532_;
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
lean_inc(v_a_3554_);
v___x_3558_ = l_Lean_MessageData_ofExpr(v_a_3554_);
v___x_3559_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3555_, v___x_3558_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_dec_ref_known(v___x_3559_, 1);
v___y_3533_ = v___x_3552_;
v___y_3534_ = v_a_3539_;
v_a_3535_ = v_a_3554_;
goto v___jp_3532_;
}
else
{
lean_object* v_a_3560_; 
lean_dec(v_a_3554_);
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___y_3527_ = v___x_3552_;
v___y_3528_ = v_a_3539_;
v_a_3529_ = v_a_3560_;
goto v___jp_3526_;
}
}
}
else
{
lean_object* v_a_3561_; 
v_a_3561_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3553_, 1);
v___y_3527_ = v___x_3552_;
v___y_3528_ = v_a_3539_;
v_a_3529_ = v_a_3561_;
goto v___jp_3526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3588_, lean_object* v_xs_3589_, lean_object* v_k_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3588_, v_xs_3589_, v_k_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3597_, lean_object* v_xs_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v___f_3604_; uint8_t v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_inc_ref(v_xs_3598_);
lean_inc(v_constName_3597_);
v___f_3604_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3604_, 0, v_constName_3597_);
lean_closure_set(v___f_3604_, 1, v_xs_3598_);
v___x_3605_ = 0;
v___x_3606_ = lean_box(v___x_3605_);
v___x_3607_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3607_, 0, lean_box(0));
lean_closure_set(v___x_3607_, 1, v___f_3604_);
lean_closure_set(v___x_3607_, 2, v___x_3606_);
v___x_3608_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3597_, v_xs_3598_, v___x_3607_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3609_, lean_object* v_xs_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_Meta_mkAppM(v_constName_3609_, v_xs_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3629_, lean_object* v_x_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3630_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3637_, lean_object* v_x_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3637_, v_x_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3645_, lean_object* v_xs_3646_, lean_object* v_x_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3653_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3654_ = l_Lean_MessageData_ofExpr(v_f_3645_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = lean_array_to_list(v_xs_3646_);
v___x_3659_ = lean_box(0);
v___x_3660_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3658_, v___x_3659_);
v___x_3661_ = l_Lean_MessageData_ofList(v___x_3660_);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3657_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3664_, lean_object* v_xs_3665_, lean_object* v_x_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3664_, v_xs_3665_, v_x_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_x_3666_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3673_, lean_object* v_xs_3674_, lean_object* v_k_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_toCold_3681_; lean_object* v_options_3682_; uint8_t v_hasTrace_3683_; 
v_toCold_3681_ = lean_ctor_get(v_a_3678_, 0);
v_options_3682_ = lean_ctor_get(v_toCold_3681_, 2);
v_hasTrace_3683_ = lean_ctor_get_uint8(v_options_3682_, sizeof(void*)*1);
if (v_hasTrace_3683_ == 0)
{
lean_object* v___x_3684_; 
lean_dec_ref(v_xs_3674_);
lean_dec_ref(v_f_3673_);
lean_inc(v_a_3679_);
lean_inc_ref(v_a_3678_);
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
v___x_3684_ = lean_apply_5(v_k_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, lean_box(0));
return v___x_3684_;
}
else
{
lean_object* v_inheritedTraceOptions_3685_; lean_object* v___f_3686_; lean_object* v___y_3688_; lean_object* v___y_3689_; uint8_t v___y_3690_; lean_object* v___y_3714_; lean_object* v_a_3715_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v_a_3725_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v_a_3740_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; uint8_t v___y_3746_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v_a_3756_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v_a_3762_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v_a_3767_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v_a_3779_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; uint8_t v___y_3785_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v_a_3795_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v_a_3801_; 
v_inheritedTraceOptions_3685_ = lean_ctor_get(v_toCold_3681_, 11);
v___f_3686_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3686_, 0, v_f_3673_);
lean_closure_set(v___f_3686_, 1, v_xs_3674_);
v___x_3718_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3719_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3720_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3685_, v_options_3682_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3828_; uint8_t v___x_3829_; 
v___x_3828_ = l_Lean_trace_profiler;
v___x_3829_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3682_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; 
lean_dec_ref(v___f_3686_);
lean_inc(v_a_3679_);
lean_inc_ref(v_a_3678_);
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
v___x_3830_ = lean_apply_5(v_k_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, lean_box(0));
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
v___x_3832_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3833_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3685_, v_options_3682_, v___x_3833_);
if (v___x_3834_ == 0)
{
lean_dec(v_a_3831_);
return v___x_3830_;
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
lean_dec_ref_known(v___x_3830_, 1);
lean_inc(v_a_3831_);
v___x_3835_ = l_Lean_MessageData_ofExpr(v_a_3831_);
v___x_3836_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3832_, v___x_3835_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3843_ == 0)
{
lean_object* v_unused_3844_; 
v_unused_3844_ = lean_ctor_get(v___x_3836_, 0);
lean_dec(v_unused_3844_);
v___x_3838_ = v___x_3836_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_dec(v___x_3836_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v_a_3831_);
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3831_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v_a_3831_);
v_a_3845_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3836_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3836_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
lean_inc(v_a_3845_);
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
v___y_3714_ = v___x_3850_;
v_a_3715_ = v_a_3845_;
goto v___jp_3713_;
}
}
}
}
}
else
{
lean_object* v_a_3853_; 
v_a_3853_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3853_);
v___y_3714_ = v___x_3830_;
v_a_3715_ = v_a_3853_;
goto v___jp_3713_;
}
}
else
{
goto v___jp_3803_;
}
}
else
{
goto v___jp_3803_;
}
v___jp_3687_:
{
if (v___y_3690_ == 0)
{
lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
lean_dec_ref(v___y_3688_);
v___x_3691_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3692_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3685_, v_options_3682_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3694_, 0, v___y_3689_);
return v___x_3694_;
}
else
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
lean_inc_ref(v___y_3689_);
v___x_3695_ = l_Lean_Exception_toMessageData(v___y_3689_);
v___x_3696_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3691_, v___x_3695_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3703_ == 0)
{
lean_object* v_unused_3704_; 
v_unused_3704_ = lean_ctor_get(v___x_3696_, 0);
lean_dec(v_unused_3704_);
v___x_3698_ = v___x_3696_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_dec(v___x_3696_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
lean_ctor_set_tag(v___x_3698_, 1);
lean_ctor_set(v___x_3698_, 0, v___y_3689_);
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___y_3689_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec_ref(v___y_3689_);
v_a_3705_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3696_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3696_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3689_);
return v___y_3688_;
}
}
v___jp_3713_:
{
uint8_t v___x_3716_; 
v___x_3716_ = l_Lean_Exception_isInterrupt(v_a_3715_);
if (v___x_3716_ == 0)
{
uint8_t v___x_3717_; 
lean_inc_ref(v_a_3715_);
v___x_3717_ = l_Lean_Exception_isRuntime(v_a_3715_);
v___y_3688_ = v___y_3714_;
v___y_3689_ = v_a_3715_;
v___y_3690_ = v___x_3717_;
goto v___jp_3687_;
}
else
{
v___y_3688_ = v___y_3714_;
v___y_3689_ = v_a_3715_;
v___y_3690_ = v___x_3716_;
goto v___jp_3687_;
}
}
v___jp_3722_:
{
lean_object* v___x_3726_; double v___x_3727_; double v___x_3728_; double v___x_3729_; double v___x_3730_; double v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3726_ = lean_io_mono_nanos_now();
v___x_3727_ = lean_float_of_nat(v___y_3723_);
v___x_3728_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3729_ = lean_float_div(v___x_3727_, v___x_3728_);
v___x_3730_ = lean_float_of_nat(v___x_3726_);
v___x_3731_ = lean_float_div(v___x_3730_, v___x_3728_);
v___x_3732_ = lean_box_float(v___x_3729_);
v___x_3733_ = lean_box_float(v___x_3731_);
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v_a_3725_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3718_, v_hasTrace_3683_, v___x_3719_, v_options_3682_, v___x_3721_, v___y_3724_, v___f_3686_, v___x_3735_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
return v___x_3736_;
}
v___jp_3737_:
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_a_3740_);
v___y_3723_ = v___y_3738_;
v___y_3724_ = v___y_3739_;
v_a_3725_ = v___x_3741_;
goto v___jp_3722_;
}
v___jp_3742_:
{
if (v___y_3746_ == 0)
{
lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___x_3747_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3748_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3749_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3685_, v_options_3682_, v___x_3748_);
if (v___x_3749_ == 0)
{
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3745_;
v_a_3740_ = v___y_3744_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_inc_ref(v___y_3744_);
v___x_3750_ = l_Lean_Exception_toMessageData(v___y_3744_);
v___x_3751_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3747_, v___x_3750_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_dec_ref_known(v___x_3751_, 1);
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3745_;
v_a_3740_ = v___y_3744_;
goto v___jp_3737_;
}
else
{
lean_object* v_a_3752_; 
lean_dec_ref(v___y_3744_);
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3751_, 1);
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3745_;
v_a_3740_ = v_a_3752_;
goto v___jp_3737_;
}
}
}
else
{
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3745_;
v_a_3740_ = v___y_3744_;
goto v___jp_3737_;
}
}
v___jp_3753_:
{
uint8_t v___x_3757_; 
v___x_3757_ = l_Lean_Exception_isInterrupt(v_a_3756_);
if (v___x_3757_ == 0)
{
uint8_t v___x_3758_; 
lean_inc_ref(v_a_3756_);
v___x_3758_ = l_Lean_Exception_isRuntime(v_a_3756_);
v___y_3743_ = v___y_3754_;
v___y_3744_ = v_a_3756_;
v___y_3745_ = v___y_3755_;
v___y_3746_ = v___x_3758_;
goto v___jp_3742_;
}
else
{
v___y_3743_ = v___y_3754_;
v___y_3744_ = v_a_3756_;
v___y_3745_ = v___y_3755_;
v___y_3746_ = v___x_3757_;
goto v___jp_3742_;
}
}
v___jp_3759_:
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_a_3762_);
v___y_3723_ = v___y_3760_;
v___y_3724_ = v___y_3761_;
v_a_3725_ = v___x_3763_;
goto v___jp_3722_;
}
v___jp_3764_:
{
lean_object* v___x_3768_; double v___x_3769_; double v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3768_ = lean_io_get_num_heartbeats();
v___x_3769_ = lean_float_of_nat(v___y_3765_);
v___x_3770_ = lean_float_of_nat(v___x_3768_);
v___x_3771_ = lean_box_float(v___x_3769_);
v___x_3772_ = lean_box_float(v___x_3770_);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_a_3767_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3718_, v_hasTrace_3683_, v___x_3719_, v_options_3682_, v___x_3721_, v___y_3766_, v___f_3686_, v___x_3774_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
return v___x_3775_;
}
v___jp_3776_:
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3780_, 0, v_a_3779_);
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3778_;
v_a_3767_ = v___x_3780_;
goto v___jp_3764_;
}
v___jp_3781_:
{
if (v___y_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3786_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3787_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3788_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3685_, v_options_3682_, v___x_3787_);
if (v___x_3788_ == 0)
{
v___y_3777_ = v___y_3783_;
v___y_3778_ = v___y_3784_;
v_a_3779_ = v___y_3782_;
goto v___jp_3776_;
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_inc_ref(v___y_3782_);
v___x_3789_ = l_Lean_Exception_toMessageData(v___y_3782_);
v___x_3790_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3786_, v___x_3789_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_dec_ref_known(v___x_3790_, 1);
v___y_3777_ = v___y_3783_;
v___y_3778_ = v___y_3784_;
v_a_3779_ = v___y_3782_;
goto v___jp_3776_;
}
else
{
lean_object* v_a_3791_; 
lean_dec_ref(v___y_3782_);
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
v___y_3777_ = v___y_3783_;
v___y_3778_ = v___y_3784_;
v_a_3779_ = v_a_3791_;
goto v___jp_3776_;
}
}
}
else
{
v___y_3777_ = v___y_3783_;
v___y_3778_ = v___y_3784_;
v_a_3779_ = v___y_3782_;
goto v___jp_3776_;
}
}
v___jp_3792_:
{
uint8_t v___x_3796_; 
v___x_3796_ = l_Lean_Exception_isInterrupt(v_a_3795_);
if (v___x_3796_ == 0)
{
uint8_t v___x_3797_; 
lean_inc_ref(v_a_3795_);
v___x_3797_ = l_Lean_Exception_isRuntime(v_a_3795_);
v___y_3782_ = v_a_3795_;
v___y_3783_ = v___y_3793_;
v___y_3784_ = v___y_3794_;
v___y_3785_ = v___x_3797_;
goto v___jp_3781_;
}
else
{
v___y_3782_ = v_a_3795_;
v___y_3783_ = v___y_3793_;
v___y_3784_ = v___y_3794_;
v___y_3785_ = v___x_3796_;
goto v___jp_3781_;
}
}
v___jp_3798_:
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3802_, 0, v_a_3801_);
v___y_3765_ = v___y_3799_;
v___y_3766_ = v___y_3800_;
v_a_3767_ = v___x_3802_;
goto v___jp_3764_;
}
v___jp_3803_:
{
lean_object* v___x_3804_; lean_object* v_a_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3804_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3679_);
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref(v___x_3804_);
v___x_3806_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3807_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3682_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_io_mono_nanos_now();
lean_inc(v_a_3679_);
lean_inc_ref(v_a_3678_);
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
v___x_3809_ = lean_apply_5(v_k_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, lean_box(0));
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3812_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3813_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3685_, v_options_3682_, v___x_3812_);
if (v___x_3813_ == 0)
{
v___y_3760_ = v___x_3808_;
v___y_3761_ = v_a_3805_;
v_a_3762_ = v_a_3810_;
goto v___jp_3759_;
}
else
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
lean_inc(v_a_3810_);
v___x_3814_ = l_Lean_MessageData_ofExpr(v_a_3810_);
v___x_3815_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3811_, v___x_3814_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_dec_ref_known(v___x_3815_, 1);
v___y_3760_ = v___x_3808_;
v___y_3761_ = v_a_3805_;
v_a_3762_ = v_a_3810_;
goto v___jp_3759_;
}
else
{
lean_object* v_a_3816_; 
lean_dec(v_a_3810_);
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
v___y_3754_ = v___x_3808_;
v___y_3755_ = v_a_3805_;
v_a_3756_ = v_a_3816_;
goto v___jp_3753_;
}
}
}
else
{
lean_object* v_a_3817_; 
v_a_3817_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3809_, 1);
v___y_3754_ = v___x_3808_;
v___y_3755_ = v_a_3805_;
v_a_3756_ = v_a_3817_;
goto v___jp_3753_;
}
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3679_);
lean_inc_ref(v_a_3678_);
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
v___x_3819_ = lean_apply_5(v_k_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, lean_box(0));
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3819_, 1);
v___x_3821_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3822_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3685_, v_options_3682_, v___x_3822_);
if (v___x_3823_ == 0)
{
v___y_3799_ = v___x_3818_;
v___y_3800_ = v_a_3805_;
v_a_3801_ = v_a_3820_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_inc(v_a_3820_);
v___x_3824_ = l_Lean_MessageData_ofExpr(v_a_3820_);
v___x_3825_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3821_, v___x_3824_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_dec_ref_known(v___x_3825_, 1);
v___y_3799_ = v___x_3818_;
v___y_3800_ = v_a_3805_;
v_a_3801_ = v_a_3820_;
goto v___jp_3798_;
}
else
{
lean_object* v_a_3826_; 
lean_dec(v_a_3820_);
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3825_, 1);
v___y_3793_ = v___x_3818_;
v___y_3794_ = v_a_3805_;
v_a_3795_ = v_a_3826_;
goto v___jp_3792_;
}
}
}
else
{
lean_object* v_a_3827_; 
v_a_3827_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3819_, 1);
v___y_3793_ = v___x_3818_;
v___y_3794_ = v_a_3805_;
v_a_3795_ = v_a_3827_;
goto v___jp_3792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3854_, lean_object* v_xs_3855_, lean_object* v_k_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3854_, v_xs_3855_, v_k_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3863_, lean_object* v_xs_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v___x_3870_; 
lean_inc(v_a_3868_);
lean_inc_ref(v_a_3867_);
lean_inc(v_a_3866_);
lean_inc_ref(v_a_3865_);
lean_inc_ref(v_f_3863_);
v___x_3870_ = lean_infer_type(v_f_3863_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
lean_inc_ref(v_xs_3864_);
lean_inc_ref(v_f_3863_);
v___x_3872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3872_, 0, v_f_3863_);
lean_closure_set(v___x_3872_, 1, v_a_3871_);
lean_closure_set(v___x_3872_, 2, v_xs_3864_);
v___x_3873_ = 0;
v___x_3874_ = lean_box(v___x_3873_);
v___x_3875_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3875_, 0, lean_box(0));
lean_closure_set(v___x_3875_, 1, v___x_3872_);
lean_closure_set(v___x_3875_, 2, v___x_3874_);
v___x_3876_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3863_, v_xs_3864_, v___x_3875_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
return v___x_3876_;
}
else
{
lean_dec_ref(v_xs_3864_);
lean_dec_ref(v_f_3863_);
return v___x_3870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3877_, lean_object* v_xs_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Meta_mkAppM_x27(v_f_3877_, v_xs_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3885_, size_t v_i_3886_, size_t v_stop_3887_, lean_object* v_b_3888_){
_start:
{
lean_object* v___y_3890_; uint8_t v___x_3894_; 
v___x_3894_ = lean_usize_dec_eq(v_i_3886_, v_stop_3887_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
v___x_3895_ = lean_array_uget_borrowed(v_as_3885_, v_i_3886_);
if (lean_obj_tag(v___x_3895_) == 0)
{
v___y_3890_ = v_b_3888_;
goto v___jp_3889_;
}
else
{
lean_object* v_val_3896_; lean_object* v___x_3897_; 
v_val_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_val_3896_);
v___x_3897_ = lean_array_push(v_b_3888_, v_val_3896_);
v___y_3890_ = v___x_3897_;
goto v___jp_3889_;
}
}
else
{
return v_b_3888_;
}
v___jp_3889_:
{
size_t v___x_3891_; size_t v___x_3892_; 
v___x_3891_ = ((size_t)1ULL);
v___x_3892_ = lean_usize_add(v_i_3886_, v___x_3891_);
v_i_3886_ = v___x_3892_;
v_b_3888_ = v___y_3890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3898_, lean_object* v_i_3899_, lean_object* v_stop_3900_, lean_object* v_b_3901_){
_start:
{
size_t v_i_boxed_3902_; size_t v_stop_boxed_3903_; lean_object* v_res_3904_; 
v_i_boxed_3902_ = lean_unbox_usize(v_i_3899_);
lean_dec(v_i_3899_);
v_stop_boxed_3903_ = lean_unbox_usize(v_stop_3900_);
lean_dec(v_stop_3900_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3898_, v_i_boxed_3902_, v_stop_boxed_3903_, v_b_3901_);
lean_dec_ref(v_as_3898_);
return v_res_3904_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3912_ = l_Lean_MessageData_ofFormat(v___x_3911_);
return v___x_3912_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_box(1);
v___x_3914_ = l_Lean_MessageData_ofFormat(v___x_3913_);
return v___x_3914_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3919_ = l_Lean_MessageData_ofFormat(v___x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3920_, lean_object* v_xs_3921_, lean_object* v_x_3922_, lean_object* v_x_3923_, lean_object* v_x_3924_, lean_object* v_x_3925_, lean_object* v_x_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_){
_start:
{
if (lean_obj_tag(v_x_3926_) == 7)
{
lean_object* v_binderName_3932_; lean_object* v_binderType_3933_; lean_object* v_body_3934_; uint8_t v_binderInfo_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; 
v_binderName_3932_ = lean_ctor_get(v_x_3926_, 0);
lean_inc(v_binderName_3932_);
v_binderType_3933_ = lean_ctor_get(v_x_3926_, 1);
lean_inc_ref(v_binderType_3933_);
v_body_3934_ = lean_ctor_get(v_x_3926_, 2);
lean_inc_ref(v_body_3934_);
v_binderInfo_3935_ = lean_ctor_get_uint8(v_x_3926_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3926_, 3);
v___x_3936_ = lean_array_get_size(v_xs_3921_);
v___x_3937_ = lean_nat_dec_lt(v_x_3922_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_dec_ref(v_body_3934_);
lean_dec_ref(v_binderType_3933_);
lean_dec(v_binderName_3932_);
lean_dec(v_x_3924_);
lean_dec(v_x_3922_);
v___x_3938_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3939_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3938_, v_f_3920_, v_x_3923_, v_x_3925_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
lean_dec_ref(v_x_3925_);
lean_dec_ref(v_x_3923_);
return v___x_3939_;
}
else
{
lean_object* v___x_3940_; lean_object* v_d_3941_; lean_object* v___x_3942_; 
v___x_3940_ = lean_array_get_size(v_x_3923_);
v_d_3941_ = lean_expr_instantiate_rev_range(v_binderType_3933_, v_x_3924_, v___x_3940_, v_x_3923_);
lean_dec_ref(v_binderType_3933_);
v___x_3942_ = lean_array_fget_borrowed(v_xs_3921_, v_x_3922_);
if (lean_obj_tag(v___x_3942_) == 0)
{
if (v_binderInfo_3935_ == 3)
{
lean_object* v___x_3943_; uint8_t v___x_3944_; lean_object* v___x_3945_; 
v___x_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3943_, 0, v_d_3941_);
v___x_3944_ = 1;
v___x_3945_ = l_Lean_Meta_mkFreshExprMVar(v___x_3943_, v___x_3944_, v_binderName_3932_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc_n(v_a_3946_, 2);
lean_dec_ref_known(v___x_3945_, 1);
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = lean_nat_add(v_x_3922_, v___x_3947_);
lean_dec(v_x_3922_);
v___x_3949_ = lean_array_push(v_x_3923_, v_a_3946_);
v___x_3950_ = l_Lean_Expr_mvarId_x21(v_a_3946_);
lean_dec(v_a_3946_);
v___x_3951_ = lean_array_push(v_x_3925_, v___x_3950_);
v_x_3922_ = v___x_3948_;
v_x_3923_ = v___x_3949_;
v_x_3925_ = v___x_3951_;
v_x_3926_ = v_body_3934_;
goto _start;
}
else
{
lean_dec_ref(v_body_3934_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_f_3920_);
return v___x_3945_;
}
}
else
{
lean_object* v___x_3953_; uint8_t v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3953_, 0, v_d_3941_);
v___x_3954_ = 0;
v___x_3955_ = l_Lean_Meta_mkFreshExprMVar(v___x_3953_, v___x_3954_, v_binderName_3932_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v___x_3955_, 1);
v___x_3957_ = lean_unsigned_to_nat(1u);
v___x_3958_ = lean_nat_add(v_x_3922_, v___x_3957_);
lean_dec(v_x_3922_);
v___x_3959_ = lean_array_push(v_x_3923_, v_a_3956_);
v_x_3922_ = v___x_3958_;
v_x_3923_ = v___x_3959_;
v_x_3926_ = v_body_3934_;
goto _start;
}
else
{
lean_dec_ref(v_body_3934_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_f_3920_);
return v___x_3955_;
}
}
}
else
{
lean_object* v_val_3961_; lean_object* v___x_3962_; 
lean_dec(v_binderName_3932_);
v_val_3961_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3930_);
lean_inc_ref(v_a_3929_);
lean_inc(v_a_3928_);
lean_inc_ref(v_a_3927_);
lean_inc(v_val_3961_);
v___x_3962_ = lean_infer_type(v_val_3961_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3964_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___x_3964_ = l_Lean_Meta_isExprDefEq(v_d_3941_, v_a_3963_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; uint8_t v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___x_3966_ = lean_unbox(v_a_3965_);
lean_dec(v_a_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
lean_dec_ref(v_body_3934_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec(v_x_3922_);
v___x_3967_ = l_Lean_mkAppN(v_f_3920_, v_x_3923_);
lean_dec_ref(v_x_3923_);
lean_inc(v_val_3961_);
v___x_3968_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3967_, v_val_3961_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
return v___x_3968_;
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = lean_unsigned_to_nat(1u);
v___x_3970_ = lean_nat_add(v_x_3922_, v___x_3969_);
lean_dec(v_x_3922_);
lean_inc(v_val_3961_);
v___x_3971_ = lean_array_push(v_x_3923_, v_val_3961_);
v_x_3922_ = v___x_3970_;
v_x_3923_ = v___x_3971_;
v_x_3926_ = v_body_3934_;
goto _start;
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v_body_3934_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_f_3920_);
v_a_3973_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3964_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3964_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_dec_ref(v_d_3941_);
lean_dec_ref(v_body_3934_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_f_3920_);
return v___x_3962_;
}
}
}
}
else
{
lean_object* v___x_3981_; lean_object* v_type_3982_; lean_object* v___x_3983_; 
v___x_3981_ = lean_array_get_size(v_x_3923_);
v_type_3982_ = lean_expr_instantiate_rev_range(v_x_3926_, v_x_3924_, v___x_3981_, v_x_3923_);
lean_dec(v_x_3924_);
lean_dec_ref(v_x_3926_);
v___x_3983_ = l_Lean_Meta_whnfD(v_type_3982_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; uint8_t v___x_3985_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v___x_3983_, 1);
v___x_3985_ = l_Lean_Expr_isForall(v_a_3984_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; uint8_t v___x_3987_; 
lean_dec(v_a_3984_);
v___x_3986_ = lean_array_get_size(v_xs_3921_);
v___x_3987_ = lean_nat_dec_eq(v_x_3922_, v___x_3986_);
lean_dec(v_x_3922_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; lean_object* v___y_3990_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
lean_dec_ref(v_x_3925_);
lean_dec_ref(v_x_3923_);
v___x_3988_ = lean_unsigned_to_nat(0u);
v___x_4003_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4004_ = lean_nat_dec_lt(v___x_3988_, v___x_3986_);
if (v___x_4004_ == 0)
{
v___y_3990_ = v___x_4003_;
goto v___jp_3989_;
}
else
{
uint8_t v___x_4005_; 
v___x_4005_ = lean_nat_dec_le(v___x_3986_, v___x_3986_);
if (v___x_4005_ == 0)
{
if (v___x_4004_ == 0)
{
v___y_3990_ = v___x_4003_;
goto v___jp_3989_;
}
else
{
size_t v___x_4006_; size_t v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = ((size_t)0ULL);
v___x_4007_ = lean_usize_of_nat(v___x_3986_);
v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3921_, v___x_4006_, v___x_4007_, v___x_4003_);
v___y_3990_ = v___x_4008_;
goto v___jp_3989_;
}
}
else
{
size_t v___x_4009_; size_t v___x_4010_; lean_object* v___x_4011_; 
v___x_4009_ = ((size_t)0ULL);
v___x_4010_ = lean_usize_of_nat(v___x_3986_);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3921_, v___x_4009_, v___x_4010_, v___x_4003_);
v___y_3990_ = v___x_4011_;
goto v___jp_3989_;
}
}
v___jp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3991_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3992_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3993_ = l_Lean_indentExpr(v_f_3920_);
v___x_3994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3992_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3996_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_4000_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3990_, v___x_3988_, v___x_3999_);
lean_dec_ref(v___y_3990_);
v___x_4001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3998_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3991_, v___x_4001_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
return v___x_4002_;
}
}
else
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4012_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_4013_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_4012_, v_f_3920_, v_x_3923_, v_x_3925_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
lean_dec_ref(v_x_3925_);
lean_dec_ref(v_x_3923_);
return v___x_4013_;
}
}
else
{
v_x_3924_ = v___x_3981_;
v_x_3926_ = v_a_3984_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3925_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_f_3920_);
return v___x_3983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_4015_, lean_object* v_xs_4016_, lean_object* v_x_4017_, lean_object* v_x_4018_, lean_object* v_x_4019_, lean_object* v_x_4020_, lean_object* v_x_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_4015_, v_xs_4016_, v_x_4017_, v_x_4018_, v_x_4019_, v_x_4020_, v_x_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec_ref(v_xs_4016_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_4028_, lean_object* v_xs_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_4028_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v_fst_4037_; lean_object* v_snd_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
v_fst_4037_ = lean_ctor_get(v_a_4036_, 0);
lean_inc(v_fst_4037_);
v_snd_4038_ = lean_ctor_get(v_a_4036_, 1);
lean_inc(v_snd_4038_);
lean_dec(v_a_4036_);
v___x_4039_ = lean_unsigned_to_nat(0u);
v___x_4040_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4041_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_4037_, v_xs_4029_, v___x_4039_, v___x_4040_, v___x_4039_, v___x_4040_, v_snd_4038_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
return v___x_4041_;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4035_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4035_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4050_, lean_object* v_xs_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4050_, v_xs_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec_ref(v_xs_4051_);
return v_res_4057_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4062_ = l_Lean_MessageData_ofFormat(v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4063_, lean_object* v_a_4064_){
_start:
{
if (lean_obj_tag(v_a_4063_) == 0)
{
lean_object* v___x_4065_; 
v___x_4065_ = l_List_reverse___redArg(v_a_4064_);
return v___x_4065_;
}
else
{
lean_object* v_head_4066_; lean_object* v_tail_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4080_; 
v_head_4066_ = lean_ctor_get(v_a_4063_, 0);
v_tail_4067_ = lean_ctor_get(v_a_4063_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_a_4063_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4069_ = v_a_4063_;
v_isShared_4070_ = v_isSharedCheck_4080_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_tail_4067_);
lean_inc(v_head_4066_);
lean_dec(v_a_4063_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4080_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___y_4072_; 
if (lean_obj_tag(v_head_4066_) == 0)
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4072_ = v___x_4077_;
goto v___jp_4071_;
}
else
{
lean_object* v_val_4078_; lean_object* v___x_4079_; 
v_val_4078_ = lean_ctor_get(v_head_4066_, 0);
lean_inc(v_val_4078_);
lean_dec_ref_known(v_head_4066_, 1);
v___x_4079_ = l_Lean_MessageData_ofExpr(v_val_4078_);
v___y_4072_ = v___x_4079_;
goto v___jp_4071_;
}
v___jp_4071_:
{
lean_object* v___x_4074_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 1, v_a_4064_);
lean_ctor_set(v___x_4069_, 0, v___y_4072_);
v___x_4074_ = v___x_4069_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___y_4072_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_a_4064_);
v___x_4074_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
v_a_4063_ = v_tail_4067_;
v_a_4064_ = v___x_4074_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4081_, lean_object* v_xs_4082_, lean_object* v_x_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4089_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4090_ = l_Lean_MessageData_ofName(v_f_4081_);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_array_to_list(v_xs_4082_);
v___x_4095_ = lean_box(0);
v___x_4096_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4094_, v___x_4095_);
v___x_4097_ = l_Lean_MessageData_ofList(v___x_4096_);
v___x_4098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4093_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4100_, lean_object* v_xs_4101_, lean_object* v_x_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4100_, v_xs_4101_, v_x_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec_ref(v_x_4102_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4109_, lean_object* v_xs_4110_, lean_object* v_k_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v_toCold_4117_; lean_object* v_options_4118_; uint8_t v_hasTrace_4119_; 
v_toCold_4117_ = lean_ctor_get(v_a_4114_, 0);
v_options_4118_ = lean_ctor_get(v_toCold_4117_, 2);
v_hasTrace_4119_ = lean_ctor_get_uint8(v_options_4118_, sizeof(void*)*1);
if (v_hasTrace_4119_ == 0)
{
lean_object* v___x_4120_; 
lean_dec_ref(v_xs_4110_);
lean_dec(v_f_4109_);
lean_inc(v_a_4115_);
lean_inc_ref(v_a_4114_);
lean_inc(v_a_4113_);
lean_inc_ref(v_a_4112_);
v___x_4120_ = lean_apply_5(v_k_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, lean_box(0));
return v___x_4120_;
}
else
{
lean_object* v_inheritedTraceOptions_4121_; lean_object* v___f_4122_; lean_object* v___y_4124_; lean_object* v___y_4125_; uint8_t v___y_4126_; lean_object* v___y_4150_; lean_object* v_a_4151_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v_a_4161_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v_a_4176_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; uint8_t v___y_4182_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v_a_4192_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v_a_4198_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v_a_4203_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v_a_4215_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; uint8_t v___y_4221_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v_a_4231_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v_a_4237_; 
v_inheritedTraceOptions_4121_ = lean_ctor_get(v_toCold_4117_, 11);
v___f_4122_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4122_, 0, v_f_4109_);
lean_closure_set(v___f_4122_, 1, v_xs_4110_);
v___x_4154_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4155_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4156_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4157_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4121_, v_options_4118_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4264_; uint8_t v___x_4265_; 
v___x_4264_ = l_Lean_trace_profiler;
v___x_4265_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4118_, v___x_4264_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; 
lean_dec_ref(v___f_4122_);
lean_inc(v_a_4115_);
lean_inc_ref(v_a_4114_);
lean_inc(v_a_4113_);
lean_inc_ref(v_a_4112_);
v___x_4266_ = lean_apply_5(v_k_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, lean_box(0));
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
v___x_4268_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4269_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4270_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4121_, v_options_4118_, v___x_4269_);
if (v___x_4270_ == 0)
{
lean_dec(v_a_4267_);
return v___x_4266_;
}
else
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
lean_dec_ref_known(v___x_4266_, 1);
lean_inc(v_a_4267_);
v___x_4271_ = l_Lean_MessageData_ofExpr(v_a_4267_);
v___x_4272_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4268_, v___x_4271_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4279_ == 0)
{
lean_object* v_unused_4280_; 
v_unused_4280_ = lean_ctor_get(v___x_4272_, 0);
lean_dec(v_unused_4280_);
v___x_4274_ = v___x_4272_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_dec(v___x_4272_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v_a_4267_);
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4267_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_a_4267_);
v_a_4281_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4272_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4272_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
lean_inc(v_a_4281_);
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
v___y_4150_ = v___x_4286_;
v_a_4151_ = v_a_4281_;
goto v___jp_4149_;
}
}
}
}
}
else
{
lean_object* v_a_4289_; 
v_a_4289_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4289_);
v___y_4150_ = v___x_4266_;
v_a_4151_ = v_a_4289_;
goto v___jp_4149_;
}
}
else
{
goto v___jp_4239_;
}
}
else
{
goto v___jp_4239_;
}
v___jp_4123_:
{
if (v___y_4126_ == 0)
{
lean_object* v___x_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
lean_dec_ref(v___y_4124_);
v___x_4127_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4128_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4129_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4121_, v_options_4118_, v___x_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___y_4125_);
return v___x_4130_;
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_inc_ref(v___y_4125_);
v___x_4131_ = l_Lean_Exception_toMessageData(v___y_4125_);
v___x_4132_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4127_, v___x_4131_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4139_ == 0)
{
lean_object* v_unused_4140_; 
v_unused_4140_ = lean_ctor_get(v___x_4132_, 0);
lean_dec(v_unused_4140_);
v___x_4134_ = v___x_4132_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_dec(v___x_4132_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 1);
lean_ctor_set(v___x_4134_, 0, v___y_4125_);
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___y_4125_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v___y_4125_);
v_a_4141_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4132_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4132_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4125_);
return v___y_4124_;
}
}
v___jp_4149_:
{
uint8_t v___x_4152_; 
v___x_4152_ = l_Lean_Exception_isInterrupt(v_a_4151_);
if (v___x_4152_ == 0)
{
uint8_t v___x_4153_; 
lean_inc_ref(v_a_4151_);
v___x_4153_ = l_Lean_Exception_isRuntime(v_a_4151_);
v___y_4124_ = v___y_4150_;
v___y_4125_ = v_a_4151_;
v___y_4126_ = v___x_4153_;
goto v___jp_4123_;
}
else
{
v___y_4124_ = v___y_4150_;
v___y_4125_ = v_a_4151_;
v___y_4126_ = v___x_4152_;
goto v___jp_4123_;
}
}
v___jp_4158_:
{
lean_object* v___x_4162_; double v___x_4163_; double v___x_4164_; double v___x_4165_; double v___x_4166_; double v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4162_ = lean_io_mono_nanos_now();
v___x_4163_ = lean_float_of_nat(v___y_4159_);
v___x_4164_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4165_ = lean_float_div(v___x_4163_, v___x_4164_);
v___x_4166_ = lean_float_of_nat(v___x_4162_);
v___x_4167_ = lean_float_div(v___x_4166_, v___x_4164_);
v___x_4168_ = lean_box_float(v___x_4165_);
v___x_4169_ = lean_box_float(v___x_4167_);
v___x_4170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4168_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v_a_4161_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4154_, v_hasTrace_4119_, v___x_4155_, v_options_4118_, v___x_4157_, v___y_4160_, v___f_4122_, v___x_4171_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
return v___x_4172_;
}
v___jp_4173_:
{
lean_object* v___x_4177_; 
v___x_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4177_, 0, v_a_4176_);
v___y_4159_ = v___y_4174_;
v___y_4160_ = v___y_4175_;
v_a_4161_ = v___x_4177_;
goto v___jp_4158_;
}
v___jp_4178_:
{
if (v___y_4182_ == 0)
{
lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v___x_4183_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4184_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4185_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4121_, v_options_4118_, v___x_4184_);
if (v___x_4185_ == 0)
{
v___y_4174_ = v___y_4180_;
v___y_4175_ = v___y_4181_;
v_a_4176_ = v___y_4179_;
goto v___jp_4173_;
}
else
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_inc_ref(v___y_4179_);
v___x_4186_ = l_Lean_Exception_toMessageData(v___y_4179_);
v___x_4187_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4183_, v___x_4186_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_dec_ref_known(v___x_4187_, 1);
v___y_4174_ = v___y_4180_;
v___y_4175_ = v___y_4181_;
v_a_4176_ = v___y_4179_;
goto v___jp_4173_;
}
else
{
lean_object* v_a_4188_; 
lean_dec_ref(v___y_4179_);
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v___x_4187_, 1);
v___y_4174_ = v___y_4180_;
v___y_4175_ = v___y_4181_;
v_a_4176_ = v_a_4188_;
goto v___jp_4173_;
}
}
}
else
{
v___y_4174_ = v___y_4180_;
v___y_4175_ = v___y_4181_;
v_a_4176_ = v___y_4179_;
goto v___jp_4173_;
}
}
v___jp_4189_:
{
uint8_t v___x_4193_; 
v___x_4193_ = l_Lean_Exception_isInterrupt(v_a_4192_);
if (v___x_4193_ == 0)
{
uint8_t v___x_4194_; 
lean_inc_ref(v_a_4192_);
v___x_4194_ = l_Lean_Exception_isRuntime(v_a_4192_);
v___y_4179_ = v_a_4192_;
v___y_4180_ = v___y_4190_;
v___y_4181_ = v___y_4191_;
v___y_4182_ = v___x_4194_;
goto v___jp_4178_;
}
else
{
v___y_4179_ = v_a_4192_;
v___y_4180_ = v___y_4190_;
v___y_4181_ = v___y_4191_;
v___y_4182_ = v___x_4193_;
goto v___jp_4178_;
}
}
v___jp_4195_:
{
lean_object* v___x_4199_; 
v___x_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4199_, 0, v_a_4198_);
v___y_4159_ = v___y_4196_;
v___y_4160_ = v___y_4197_;
v_a_4161_ = v___x_4199_;
goto v___jp_4158_;
}
v___jp_4200_:
{
lean_object* v___x_4204_; double v___x_4205_; double v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4204_ = lean_io_get_num_heartbeats();
v___x_4205_ = lean_float_of_nat(v___y_4201_);
v___x_4206_ = lean_float_of_nat(v___x_4204_);
v___x_4207_ = lean_box_float(v___x_4205_);
v___x_4208_ = lean_box_float(v___x_4206_);
v___x_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4207_);
lean_ctor_set(v___x_4209_, 1, v___x_4208_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v_a_4203_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
v___x_4211_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4154_, v_hasTrace_4119_, v___x_4155_, v_options_4118_, v___x_4157_, v___y_4202_, v___f_4122_, v___x_4210_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
return v___x_4211_;
}
v___jp_4212_:
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v_a_4215_);
v___y_4201_ = v___y_4213_;
v___y_4202_ = v___y_4214_;
v_a_4203_ = v___x_4216_;
goto v___jp_4200_;
}
v___jp_4217_:
{
if (v___y_4221_ == 0)
{
lean_object* v___x_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v___x_4222_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4223_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4121_, v_options_4118_, v___x_4223_);
if (v___x_4224_ == 0)
{
v___y_4213_ = v___y_4218_;
v___y_4214_ = v___y_4220_;
v_a_4215_ = v___y_4219_;
goto v___jp_4212_;
}
else
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
lean_inc_ref(v___y_4219_);
v___x_4225_ = l_Lean_Exception_toMessageData(v___y_4219_);
v___x_4226_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4222_, v___x_4225_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_dec_ref_known(v___x_4226_, 1);
v___y_4213_ = v___y_4218_;
v___y_4214_ = v___y_4220_;
v_a_4215_ = v___y_4219_;
goto v___jp_4212_;
}
else
{
lean_object* v_a_4227_; 
lean_dec_ref(v___y_4219_);
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___x_4226_, 1);
v___y_4213_ = v___y_4218_;
v___y_4214_ = v___y_4220_;
v_a_4215_ = v_a_4227_;
goto v___jp_4212_;
}
}
}
else
{
v___y_4213_ = v___y_4218_;
v___y_4214_ = v___y_4220_;
v_a_4215_ = v___y_4219_;
goto v___jp_4212_;
}
}
v___jp_4228_:
{
uint8_t v___x_4232_; 
v___x_4232_ = l_Lean_Exception_isInterrupt(v_a_4231_);
if (v___x_4232_ == 0)
{
uint8_t v___x_4233_; 
lean_inc_ref(v_a_4231_);
v___x_4233_ = l_Lean_Exception_isRuntime(v_a_4231_);
v___y_4218_ = v___y_4229_;
v___y_4219_ = v_a_4231_;
v___y_4220_ = v___y_4230_;
v___y_4221_ = v___x_4233_;
goto v___jp_4217_;
}
else
{
v___y_4218_ = v___y_4229_;
v___y_4219_ = v_a_4231_;
v___y_4220_ = v___y_4230_;
v___y_4221_ = v___x_4232_;
goto v___jp_4217_;
}
}
v___jp_4234_:
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_a_4237_);
v___y_4201_ = v___y_4235_;
v___y_4202_ = v___y_4236_;
v_a_4203_ = v___x_4238_;
goto v___jp_4200_;
}
v___jp_4239_:
{
lean_object* v___x_4240_; lean_object* v_a_4241_; lean_object* v___x_4242_; uint8_t v___x_4243_; 
v___x_4240_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4115_);
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref(v___x_4240_);
v___x_4242_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4243_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4118_, v___x_4242_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4244_ = lean_io_mono_nanos_now();
lean_inc(v_a_4115_);
lean_inc_ref(v_a_4114_);
lean_inc(v_a_4113_);
lean_inc_ref(v_a_4112_);
v___x_4245_ = lean_apply_5(v_k_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, lean_box(0));
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; uint8_t v___x_4249_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4245_, 1);
v___x_4247_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4248_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4249_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4121_, v_options_4118_, v___x_4248_);
if (v___x_4249_ == 0)
{
v___y_4196_ = v___x_4244_;
v___y_4197_ = v_a_4241_;
v_a_4198_ = v_a_4246_;
goto v___jp_4195_;
}
else
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
lean_inc(v_a_4246_);
v___x_4250_ = l_Lean_MessageData_ofExpr(v_a_4246_);
v___x_4251_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4247_, v___x_4250_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_dec_ref_known(v___x_4251_, 1);
v___y_4196_ = v___x_4244_;
v___y_4197_ = v_a_4241_;
v_a_4198_ = v_a_4246_;
goto v___jp_4195_;
}
else
{
lean_object* v_a_4252_; 
lean_dec(v_a_4246_);
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___x_4251_, 1);
v___y_4190_ = v___x_4244_;
v___y_4191_ = v_a_4241_;
v_a_4192_ = v_a_4252_;
goto v___jp_4189_;
}
}
}
else
{
lean_object* v_a_4253_; 
v_a_4253_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4253_);
lean_dec_ref_known(v___x_4245_, 1);
v___y_4190_ = v___x_4244_;
v___y_4191_ = v_a_4241_;
v_a_4192_ = v_a_4253_;
goto v___jp_4189_;
}
}
else
{
lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4254_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4115_);
lean_inc_ref(v_a_4114_);
lean_inc(v_a_4113_);
lean_inc_ref(v_a_4112_);
v___x_4255_ = lean_apply_5(v_k_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, lean_box(0));
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___x_4257_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4258_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4259_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4121_, v_options_4118_, v___x_4258_);
if (v___x_4259_ == 0)
{
v___y_4235_ = v___x_4254_;
v___y_4236_ = v_a_4241_;
v_a_4237_ = v_a_4256_;
goto v___jp_4234_;
}
else
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_inc(v_a_4256_);
v___x_4260_ = l_Lean_MessageData_ofExpr(v_a_4256_);
v___x_4261_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4257_, v___x_4260_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_dec_ref_known(v___x_4261_, 1);
v___y_4235_ = v___x_4254_;
v___y_4236_ = v_a_4241_;
v_a_4237_ = v_a_4256_;
goto v___jp_4234_;
}
else
{
lean_object* v_a_4262_; 
lean_dec(v_a_4256_);
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___x_4261_, 1);
v___y_4229_ = v___x_4254_;
v___y_4230_ = v_a_4241_;
v_a_4231_ = v_a_4262_;
goto v___jp_4228_;
}
}
}
else
{
lean_object* v_a_4263_; 
v_a_4263_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4255_, 1);
v___y_4229_ = v___x_4254_;
v___y_4230_ = v_a_4241_;
v_a_4231_ = v_a_4263_;
goto v___jp_4228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4290_, lean_object* v_xs_4291_, lean_object* v_k_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4290_, v_xs_4291_, v_k_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4299_, lean_object* v_xs_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___f_4306_; uint8_t v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
lean_inc_ref(v_xs_4300_);
lean_inc(v_constName_4299_);
v___f_4306_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4306_, 0, v_constName_4299_);
lean_closure_set(v___f_4306_, 1, v_xs_4300_);
v___x_4307_ = 0;
v___x_4308_ = lean_box(v___x_4307_);
v___x_4309_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4309_, 0, lean_box(0));
lean_closure_set(v___x_4309_, 1, v___f_4306_);
lean_closure_set(v___x_4309_, 2, v___x_4308_);
v___x_4310_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4299_, v_xs_4300_, v___x_4309_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4311_, lean_object* v_xs_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Lean_Meta_mkAppOptM(v_constName_4311_, v_xs_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4319_, lean_object* v_xs_4320_, lean_object* v_x_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4327_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4328_ = l_Lean_MessageData_ofExpr(v_f_4319_);
v___x_4329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
v___x_4332_ = lean_array_to_list(v_xs_4320_);
v___x_4333_ = lean_box(0);
v___x_4334_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4332_, v___x_4333_);
v___x_4335_ = l_Lean_MessageData_ofList(v___x_4334_);
v___x_4336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4331_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4338_, lean_object* v_xs_4339_, lean_object* v_x_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4338_, v_xs_4339_, v_x_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec_ref(v_x_4340_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4347_, lean_object* v_xs_4348_, lean_object* v_k_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v_toCold_4355_; lean_object* v_options_4356_; uint8_t v_hasTrace_4357_; 
v_toCold_4355_ = lean_ctor_get(v_a_4352_, 0);
v_options_4356_ = lean_ctor_get(v_toCold_4355_, 2);
v_hasTrace_4357_ = lean_ctor_get_uint8(v_options_4356_, sizeof(void*)*1);
if (v_hasTrace_4357_ == 0)
{
lean_object* v___x_4358_; 
lean_dec_ref(v_xs_4348_);
lean_dec_ref(v_f_4347_);
lean_inc(v_a_4353_);
lean_inc_ref(v_a_4352_);
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
v___x_4358_ = lean_apply_5(v_k_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, lean_box(0));
return v___x_4358_;
}
else
{
lean_object* v_inheritedTraceOptions_4359_; lean_object* v___f_4360_; lean_object* v___y_4362_; lean_object* v___y_4363_; uint8_t v___y_4364_; lean_object* v___y_4388_; lean_object* v_a_4389_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v_a_4399_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v_a_4414_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; uint8_t v___y_4420_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v_a_4430_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v_a_4436_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v_a_4441_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v_a_4453_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; uint8_t v___y_4459_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v_a_4469_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v_a_4475_; 
v_inheritedTraceOptions_4359_ = lean_ctor_get(v_toCold_4355_, 11);
v___f_4360_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4360_, 0, v_f_4347_);
lean_closure_set(v___f_4360_, 1, v_xs_4348_);
v___x_4392_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4393_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4394_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4395_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4356_, v___x_4394_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4502_; uint8_t v___x_4503_; 
v___x_4502_ = l_Lean_trace_profiler;
v___x_4503_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4356_, v___x_4502_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4504_; 
lean_dec_ref(v___f_4360_);
lean_inc(v_a_4353_);
lean_inc_ref(v_a_4352_);
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
v___x_4504_ = lean_apply_5(v_k_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, lean_box(0));
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
v___x_4506_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4507_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4508_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4356_, v___x_4507_);
if (v___x_4508_ == 0)
{
lean_dec(v_a_4505_);
return v___x_4504_;
}
else
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec_ref_known(v___x_4504_, 1);
lean_inc(v_a_4505_);
v___x_4509_ = l_Lean_MessageData_ofExpr(v_a_4505_);
v___x_4510_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4506_, v___x_4509_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4517_ == 0)
{
lean_object* v_unused_4518_; 
v_unused_4518_ = lean_ctor_get(v___x_4510_, 0);
lean_dec(v_unused_4518_);
v___x_4512_ = v___x_4510_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_dec(v___x_4510_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 0, v_a_4505_);
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4505_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v_a_4505_);
v_a_4519_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4510_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4510_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
lean_inc(v_a_4519_);
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
v___y_4388_ = v___x_4524_;
v_a_4389_ = v_a_4519_;
goto v___jp_4387_;
}
}
}
}
}
else
{
lean_object* v_a_4527_; 
v_a_4527_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4527_);
v___y_4388_ = v___x_4504_;
v_a_4389_ = v_a_4527_;
goto v___jp_4387_;
}
}
else
{
goto v___jp_4477_;
}
}
else
{
goto v___jp_4477_;
}
v___jp_4361_:
{
if (v___y_4364_ == 0)
{
lean_object* v___x_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; 
lean_dec_ref(v___y_4362_);
v___x_4365_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4366_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4367_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4356_, v___x_4366_);
if (v___x_4367_ == 0)
{
lean_object* v___x_4368_; 
v___x_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4368_, 0, v___y_4363_);
return v___x_4368_;
}
else
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
lean_inc_ref(v___y_4363_);
v___x_4369_ = l_Lean_Exception_toMessageData(v___y_4363_);
v___x_4370_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4365_, v___x_4369_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4377_ == 0)
{
lean_object* v_unused_4378_; 
v_unused_4378_ = lean_ctor_get(v___x_4370_, 0);
lean_dec(v_unused_4378_);
v___x_4372_ = v___x_4370_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_dec(v___x_4370_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
lean_ctor_set_tag(v___x_4372_, 1);
lean_ctor_set(v___x_4372_, 0, v___y_4363_);
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___y_4363_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec_ref(v___y_4363_);
v_a_4379_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4370_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4370_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4363_);
return v___y_4362_;
}
}
v___jp_4387_:
{
uint8_t v___x_4390_; 
v___x_4390_ = l_Lean_Exception_isInterrupt(v_a_4389_);
if (v___x_4390_ == 0)
{
uint8_t v___x_4391_; 
lean_inc_ref(v_a_4389_);
v___x_4391_ = l_Lean_Exception_isRuntime(v_a_4389_);
v___y_4362_ = v___y_4388_;
v___y_4363_ = v_a_4389_;
v___y_4364_ = v___x_4391_;
goto v___jp_4361_;
}
else
{
v___y_4362_ = v___y_4388_;
v___y_4363_ = v_a_4389_;
v___y_4364_ = v___x_4390_;
goto v___jp_4361_;
}
}
v___jp_4396_:
{
lean_object* v___x_4400_; double v___x_4401_; double v___x_4402_; double v___x_4403_; double v___x_4404_; double v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4400_ = lean_io_mono_nanos_now();
v___x_4401_ = lean_float_of_nat(v___y_4397_);
v___x_4402_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4403_ = lean_float_div(v___x_4401_, v___x_4402_);
v___x_4404_ = lean_float_of_nat(v___x_4400_);
v___x_4405_ = lean_float_div(v___x_4404_, v___x_4402_);
v___x_4406_ = lean_box_float(v___x_4403_);
v___x_4407_ = lean_box_float(v___x_4405_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4409_, 0, v_a_4399_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
v___x_4410_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4392_, v_hasTrace_4357_, v___x_4393_, v_options_4356_, v___x_4395_, v___y_4398_, v___f_4360_, v___x_4409_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
return v___x_4410_;
}
v___jp_4411_:
{
lean_object* v___x_4415_; 
v___x_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4415_, 0, v_a_4414_);
v___y_4397_ = v___y_4412_;
v___y_4398_ = v___y_4413_;
v_a_4399_ = v___x_4415_;
goto v___jp_4396_;
}
v___jp_4416_:
{
if (v___y_4420_ == 0)
{
lean_object* v___x_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; 
v___x_4421_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4422_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4423_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4356_, v___x_4422_);
if (v___x_4423_ == 0)
{
v___y_4412_ = v___y_4417_;
v___y_4413_ = v___y_4418_;
v_a_4414_ = v___y_4419_;
goto v___jp_4411_;
}
else
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
lean_inc_ref(v___y_4419_);
v___x_4424_ = l_Lean_Exception_toMessageData(v___y_4419_);
v___x_4425_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4421_, v___x_4424_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_dec_ref_known(v___x_4425_, 1);
v___y_4412_ = v___y_4417_;
v___y_4413_ = v___y_4418_;
v_a_4414_ = v___y_4419_;
goto v___jp_4411_;
}
else
{
lean_object* v_a_4426_; 
lean_dec_ref(v___y_4419_);
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4425_, 1);
v___y_4412_ = v___y_4417_;
v___y_4413_ = v___y_4418_;
v_a_4414_ = v_a_4426_;
goto v___jp_4411_;
}
}
}
else
{
v___y_4412_ = v___y_4417_;
v___y_4413_ = v___y_4418_;
v_a_4414_ = v___y_4419_;
goto v___jp_4411_;
}
}
v___jp_4427_:
{
uint8_t v___x_4431_; 
v___x_4431_ = l_Lean_Exception_isInterrupt(v_a_4430_);
if (v___x_4431_ == 0)
{
uint8_t v___x_4432_; 
lean_inc_ref(v_a_4430_);
v___x_4432_ = l_Lean_Exception_isRuntime(v_a_4430_);
v___y_4417_ = v___y_4428_;
v___y_4418_ = v___y_4429_;
v___y_4419_ = v_a_4430_;
v___y_4420_ = v___x_4432_;
goto v___jp_4416_;
}
else
{
v___y_4417_ = v___y_4428_;
v___y_4418_ = v___y_4429_;
v___y_4419_ = v_a_4430_;
v___y_4420_ = v___x_4431_;
goto v___jp_4416_;
}
}
v___jp_4433_:
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4437_, 0, v_a_4436_);
v___y_4397_ = v___y_4434_;
v___y_4398_ = v___y_4435_;
v_a_4399_ = v___x_4437_;
goto v___jp_4396_;
}
v___jp_4438_:
{
lean_object* v___x_4442_; double v___x_4443_; double v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4442_ = lean_io_get_num_heartbeats();
v___x_4443_ = lean_float_of_nat(v___y_4440_);
v___x_4444_ = lean_float_of_nat(v___x_4442_);
v___x_4445_ = lean_box_float(v___x_4443_);
v___x_4446_ = lean_box_float(v___x_4444_);
v___x_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4445_);
lean_ctor_set(v___x_4447_, 1, v___x_4446_);
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v_a_4441_);
lean_ctor_set(v___x_4448_, 1, v___x_4447_);
v___x_4449_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4392_, v_hasTrace_4357_, v___x_4393_, v_options_4356_, v___x_4395_, v___y_4439_, v___f_4360_, v___x_4448_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
return v___x_4449_;
}
v___jp_4450_:
{
lean_object* v___x_4454_; 
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v_a_4453_);
v___y_4439_ = v___y_4451_;
v___y_4440_ = v___y_4452_;
v_a_4441_ = v___x_4454_;
goto v___jp_4438_;
}
v___jp_4455_:
{
if (v___y_4459_ == 0)
{
lean_object* v___x_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4460_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4461_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4462_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4356_, v___x_4461_);
if (v___x_4462_ == 0)
{
v___y_4451_ = v___y_4456_;
v___y_4452_ = v___y_4457_;
v_a_4453_ = v___y_4458_;
goto v___jp_4450_;
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
lean_inc_ref(v___y_4458_);
v___x_4463_ = l_Lean_Exception_toMessageData(v___y_4458_);
v___x_4464_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4460_, v___x_4463_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_dec_ref_known(v___x_4464_, 1);
v___y_4451_ = v___y_4456_;
v___y_4452_ = v___y_4457_;
v_a_4453_ = v___y_4458_;
goto v___jp_4450_;
}
else
{
lean_object* v_a_4465_; 
lean_dec_ref(v___y_4458_);
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4465_);
lean_dec_ref_known(v___x_4464_, 1);
v___y_4451_ = v___y_4456_;
v___y_4452_ = v___y_4457_;
v_a_4453_ = v_a_4465_;
goto v___jp_4450_;
}
}
}
else
{
v___y_4451_ = v___y_4456_;
v___y_4452_ = v___y_4457_;
v_a_4453_ = v___y_4458_;
goto v___jp_4450_;
}
}
v___jp_4466_:
{
uint8_t v___x_4470_; 
v___x_4470_ = l_Lean_Exception_isInterrupt(v_a_4469_);
if (v___x_4470_ == 0)
{
uint8_t v___x_4471_; 
lean_inc_ref(v_a_4469_);
v___x_4471_ = l_Lean_Exception_isRuntime(v_a_4469_);
v___y_4456_ = v___y_4467_;
v___y_4457_ = v___y_4468_;
v___y_4458_ = v_a_4469_;
v___y_4459_ = v___x_4471_;
goto v___jp_4455_;
}
else
{
v___y_4456_ = v___y_4467_;
v___y_4457_ = v___y_4468_;
v___y_4458_ = v_a_4469_;
v___y_4459_ = v___x_4470_;
goto v___jp_4455_;
}
}
v___jp_4472_:
{
lean_object* v___x_4476_; 
v___x_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4476_, 0, v_a_4475_);
v___y_4439_ = v___y_4473_;
v___y_4440_ = v___y_4474_;
v_a_4441_ = v___x_4476_;
goto v___jp_4438_;
}
v___jp_4477_:
{
lean_object* v___x_4478_; lean_object* v_a_4479_; lean_object* v___x_4480_; uint8_t v___x_4481_; 
v___x_4478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4353_);
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref(v___x_4478_);
v___x_4480_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4481_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4356_, v___x_4480_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = lean_io_mono_nanos_now();
lean_inc(v_a_4353_);
lean_inc_ref(v_a_4352_);
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
v___x_4483_ = lean_apply_5(v_k_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, lean_box(0));
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; uint8_t v___x_4487_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4485_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4486_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4356_, v___x_4486_);
if (v___x_4487_ == 0)
{
v___y_4434_ = v___x_4482_;
v___y_4435_ = v_a_4479_;
v_a_4436_ = v_a_4484_;
goto v___jp_4433_;
}
else
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
lean_inc(v_a_4484_);
v___x_4488_ = l_Lean_MessageData_ofExpr(v_a_4484_);
v___x_4489_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4485_, v___x_4488_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_dec_ref_known(v___x_4489_, 1);
v___y_4434_ = v___x_4482_;
v___y_4435_ = v_a_4479_;
v_a_4436_ = v_a_4484_;
goto v___jp_4433_;
}
else
{
lean_object* v_a_4490_; 
lean_dec(v_a_4484_);
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___y_4428_ = v___x_4482_;
v___y_4429_ = v_a_4479_;
v_a_4430_ = v_a_4490_;
goto v___jp_4427_;
}
}
}
else
{
lean_object* v_a_4491_; 
v_a_4491_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4483_, 1);
v___y_4428_ = v___x_4482_;
v___y_4429_ = v_a_4479_;
v_a_4430_ = v_a_4491_;
goto v___jp_4427_;
}
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4353_);
lean_inc_ref(v_a_4352_);
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
v___x_4493_ = lean_apply_5(v_k_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, lean_box(0));
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; uint8_t v___x_4497_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
v___x_4495_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4496_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4497_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4356_, v___x_4496_);
if (v___x_4497_ == 0)
{
v___y_4473_ = v_a_4479_;
v___y_4474_ = v___x_4492_;
v_a_4475_ = v_a_4494_;
goto v___jp_4472_;
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
lean_inc(v_a_4494_);
v___x_4498_ = l_Lean_MessageData_ofExpr(v_a_4494_);
v___x_4499_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4495_, v___x_4498_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_dec_ref_known(v___x_4499_, 1);
v___y_4473_ = v_a_4479_;
v___y_4474_ = v___x_4492_;
v_a_4475_ = v_a_4494_;
goto v___jp_4472_;
}
else
{
lean_object* v_a_4500_; 
lean_dec(v_a_4494_);
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_a_4500_);
lean_dec_ref_known(v___x_4499_, 1);
v___y_4467_ = v_a_4479_;
v___y_4468_ = v___x_4492_;
v_a_4469_ = v_a_4500_;
goto v___jp_4466_;
}
}
}
else
{
lean_object* v_a_4501_; 
v_a_4501_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v___x_4493_, 1);
v___y_4467_ = v_a_4479_;
v___y_4468_ = v___x_4492_;
v_a_4469_ = v_a_4501_;
goto v___jp_4466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4528_, lean_object* v_xs_4529_, lean_object* v_k_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4528_, v_xs_4529_, v_k_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4537_, lean_object* v_xs_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v___x_4544_; 
lean_inc(v_a_4542_);
lean_inc_ref(v_a_4541_);
lean_inc(v_a_4540_);
lean_inc_ref(v_a_4539_);
lean_inc_ref(v_f_4537_);
v___x_4544_ = lean_infer_type(v_f_4537_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; uint8_t v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc(v_a_4545_);
lean_dec_ref_known(v___x_4544_, 1);
v___x_4546_ = lean_unsigned_to_nat(0u);
v___x_4547_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4538_);
lean_inc_ref(v_f_4537_);
v___x_4548_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4548_, 0, v_f_4537_);
lean_closure_set(v___x_4548_, 1, v_xs_4538_);
lean_closure_set(v___x_4548_, 2, v___x_4546_);
lean_closure_set(v___x_4548_, 3, v___x_4547_);
lean_closure_set(v___x_4548_, 4, v___x_4546_);
lean_closure_set(v___x_4548_, 5, v___x_4547_);
lean_closure_set(v___x_4548_, 6, v_a_4545_);
v___x_4549_ = 0;
v___x_4550_ = lean_box(v___x_4549_);
v___x_4551_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4551_, 0, lean_box(0));
lean_closure_set(v___x_4551_, 1, v___x_4548_);
lean_closure_set(v___x_4551_, 2, v___x_4550_);
v___x_4552_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4537_, v_xs_4538_, v___x_4551_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
return v___x_4552_;
}
else
{
lean_dec_ref(v_xs_4538_);
lean_dec_ref(v_f_4537_);
return v___x_4544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4553_, lean_object* v_xs_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_Lean_Meta_mkAppOptM_x27(v_f_4553_, v_xs_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_);
lean_dec(v_a_4558_);
lean_dec_ref(v_a_4557_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
return v_res_4560_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4569_ = l_Lean_MessageData_ofFormat(v___x_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4570_, lean_object* v_h1_4571_, lean_object* v_h2_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___x_4588_; uint8_t v___x_4589_; 
v___x_4588_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4589_ = l_Lean_Expr_isAppOf(v_h2_4572_, v___x_4588_);
if (v___x_4589_ == 0)
{
lean_object* v___x_4590_; 
lean_inc_ref(v_h2_4572_);
v___x_4590_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref_known(v___x_4590_, 1);
v___x_4592_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4593_ = lean_unsigned_to_nat(3u);
v___x_4594_ = l_Lean_Expr_isAppOfArity(v_a_4591_, v___x_4592_, v___x_4593_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
lean_dec_ref(v_h1_4571_);
lean_dec_ref(v_motive_4570_);
v___x_4595_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4596_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4597_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4572_, v_a_4591_);
v___x_4598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4596_);
lean_ctor_set(v___x_4598_, 1, v___x_4597_);
v___x_4599_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4595_, v___x_4598_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
return v___x_4599_;
}
else
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4600_ = l_Lean_Expr_appFn_x21(v_a_4591_);
v___x_4601_ = l_Lean_Expr_appFn_x21(v___x_4600_);
v___x_4602_ = l_Lean_Expr_appArg_x21(v___x_4601_);
lean_dec_ref(v___x_4601_);
v___x_4603_ = l_Lean_Expr_appArg_x21(v___x_4600_);
lean_dec_ref(v___x_4600_);
v___x_4604_ = l_Lean_Expr_appArg_x21(v_a_4591_);
lean_dec(v_a_4591_);
lean_inc_ref(v___x_4602_);
v___x_4605_ = l_Lean_Meta_getLevel(v___x_4602_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v___x_4607_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref_known(v___x_4605_, 1);
lean_inc_ref(v_motive_4570_);
v___x_4607_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4570_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4631_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4610_ = v___x_4607_;
v_isShared_4611_ = v_isSharedCheck_4631_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4607_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4631_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
if (lean_obj_tag(v_a_4608_) == 7)
{
lean_object* v_body_4612_; 
v_body_4612_ = lean_ctor_get(v_a_4608_, 2);
lean_inc_ref(v_body_4612_);
lean_dec_ref_known(v_a_4608_, 3);
if (lean_obj_tag(v_body_4612_) == 3)
{
lean_object* v_u_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4629_; 
v_u_4613_ = lean_ctor_get(v_body_4612_, 0);
lean_inc(v_u_4613_);
lean_dec_ref_known(v_body_4612_, 1);
v___x_4614_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4615_ = lean_box(0);
v___x_4616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4616_, 0, v_a_4606_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
v___x_4617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4617_, 0, v_u_4613_);
lean_ctor_set(v___x_4617_, 1, v___x_4616_);
v___x_4618_ = l_Lean_mkConst(v___x_4614_, v___x_4617_);
v___x_4619_ = lean_unsigned_to_nat(6u);
v___x_4620_ = lean_mk_empty_array_with_capacity(v___x_4619_);
v___x_4621_ = lean_array_push(v___x_4620_, v___x_4602_);
v___x_4622_ = lean_array_push(v___x_4621_, v___x_4603_);
v___x_4623_ = lean_array_push(v___x_4622_, v_motive_4570_);
v___x_4624_ = lean_array_push(v___x_4623_, v_h1_4571_);
v___x_4625_ = lean_array_push(v___x_4624_, v___x_4604_);
v___x_4626_ = lean_array_push(v___x_4625_, v_h2_4572_);
v___x_4627_ = l_Lean_mkAppN(v___x_4618_, v___x_4626_);
lean_dec_ref(v___x_4626_);
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 0, v___x_4627_);
v___x_4629_ = v___x_4610_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4627_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
else
{
lean_dec_ref(v_body_4612_);
lean_del_object(v___x_4610_);
lean_dec(v_a_4606_);
lean_dec_ref(v___x_4604_);
lean_dec_ref(v___x_4603_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v_h2_4572_);
lean_dec_ref(v_h1_4571_);
v___y_4579_ = v_a_4573_;
v___y_4580_ = v_a_4574_;
v___y_4581_ = v_a_4575_;
v___y_4582_ = v_a_4576_;
goto v___jp_4578_;
}
}
else
{
lean_del_object(v___x_4610_);
lean_dec(v_a_4608_);
lean_dec(v_a_4606_);
lean_dec_ref(v___x_4604_);
lean_dec_ref(v___x_4603_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v_h2_4572_);
lean_dec_ref(v_h1_4571_);
v___y_4579_ = v_a_4573_;
v___y_4580_ = v_a_4574_;
v___y_4581_ = v_a_4575_;
v___y_4582_ = v_a_4576_;
goto v___jp_4578_;
}
}
}
else
{
lean_dec(v_a_4606_);
lean_dec_ref(v___x_4604_);
lean_dec_ref(v___x_4603_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v_h2_4572_);
lean_dec_ref(v_h1_4571_);
lean_dec_ref(v_motive_4570_);
return v___x_4607_;
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
lean_dec_ref(v___x_4604_);
lean_dec_ref(v___x_4603_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v_h2_4572_);
lean_dec_ref(v_h1_4571_);
lean_dec_ref(v_motive_4570_);
v_a_4632_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4605_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4605_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4572_);
lean_dec_ref(v_h1_4571_);
lean_dec_ref(v_motive_4570_);
return v___x_4590_;
}
}
else
{
lean_object* v___x_4640_; 
lean_dec_ref(v_h2_4572_);
lean_dec_ref(v_motive_4570_);
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v_h1_4571_);
return v___x_4640_;
}
v___jp_4578_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4583_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4584_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4585_ = l_Lean_indentExpr(v_motive_4570_);
v___x_4586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4584_);
lean_ctor_set(v___x_4586_, 1, v___x_4585_);
v___x_4587_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4583_, v___x_4586_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
return v___x_4587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4641_, lean_object* v_h1_4642_, lean_object* v_h2_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Lean_Meta_mkEqNDRec(v_motive_4641_, v_h1_4642_, v_h2_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4654_, lean_object* v_h1_4655_, lean_object* v_h2_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_){
_start:
{
lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4672_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4673_ = l_Lean_Expr_isAppOf(v_h2_4656_, v___x_4672_);
if (v___x_4673_ == 0)
{
lean_object* v___x_4674_; 
lean_inc_ref(v_h2_4656_);
v___x_4674_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v___x_4676_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4677_ = lean_unsigned_to_nat(3u);
v___x_4678_ = l_Lean_Expr_isAppOfArity(v_a_4675_, v___x_4676_, v___x_4677_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
lean_dec(v_a_4675_);
lean_dec_ref(v_h1_4655_);
lean_dec_ref(v_motive_4654_);
v___x_4679_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4680_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4681_ = l_Lean_indentExpr(v_h2_4656_);
v___x_4682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4682_, 0, v___x_4680_);
lean_ctor_set(v___x_4682_, 1, v___x_4681_);
v___x_4683_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4679_, v___x_4682_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
return v___x_4683_;
}
else
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4684_ = l_Lean_Expr_appFn_x21(v_a_4675_);
v___x_4685_ = l_Lean_Expr_appFn_x21(v___x_4684_);
v___x_4686_ = l_Lean_Expr_appArg_x21(v___x_4685_);
lean_dec_ref(v___x_4685_);
v___x_4687_ = l_Lean_Expr_appArg_x21(v___x_4684_);
lean_dec_ref(v___x_4684_);
v___x_4688_ = l_Lean_Expr_appArg_x21(v_a_4675_);
lean_dec(v_a_4675_);
lean_inc_ref(v___x_4686_);
v___x_4689_ = l_Lean_Meta_getLevel(v___x_4686_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v_a_4690_; lean_object* v___x_4691_; 
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_a_4690_);
lean_dec_ref_known(v___x_4689_, 1);
lean_inc_ref(v_motive_4654_);
v___x_4691_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4654_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4716_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4694_ = v___x_4691_;
v_isShared_4695_ = v_isSharedCheck_4716_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4691_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4716_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
if (lean_obj_tag(v_a_4692_) == 7)
{
lean_object* v_body_4696_; 
v_body_4696_ = lean_ctor_get(v_a_4692_, 2);
lean_inc_ref(v_body_4696_);
lean_dec_ref_known(v_a_4692_, 3);
if (lean_obj_tag(v_body_4696_) == 7)
{
lean_object* v_body_4697_; 
v_body_4697_ = lean_ctor_get(v_body_4696_, 2);
lean_inc_ref(v_body_4697_);
lean_dec_ref_known(v_body_4696_, 3);
if (lean_obj_tag(v_body_4697_) == 3)
{
lean_object* v_u_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4714_; 
v_u_4698_ = lean_ctor_get(v_body_4697_, 0);
lean_inc(v_u_4698_);
lean_dec_ref_known(v_body_4697_, 1);
v___x_4699_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4700_ = lean_box(0);
v___x_4701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4701_, 0, v_a_4690_);
lean_ctor_set(v___x_4701_, 1, v___x_4700_);
v___x_4702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4702_, 0, v_u_4698_);
lean_ctor_set(v___x_4702_, 1, v___x_4701_);
v___x_4703_ = l_Lean_mkConst(v___x_4699_, v___x_4702_);
v___x_4704_ = lean_unsigned_to_nat(6u);
v___x_4705_ = lean_mk_empty_array_with_capacity(v___x_4704_);
v___x_4706_ = lean_array_push(v___x_4705_, v___x_4686_);
v___x_4707_ = lean_array_push(v___x_4706_, v___x_4687_);
v___x_4708_ = lean_array_push(v___x_4707_, v_motive_4654_);
v___x_4709_ = lean_array_push(v___x_4708_, v_h1_4655_);
v___x_4710_ = lean_array_push(v___x_4709_, v___x_4688_);
v___x_4711_ = lean_array_push(v___x_4710_, v_h2_4656_);
v___x_4712_ = l_Lean_mkAppN(v___x_4703_, v___x_4711_);
lean_dec_ref(v___x_4711_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 0, v___x_4712_);
v___x_4714_ = v___x_4694_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4712_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
else
{
lean_dec_ref(v_body_4697_);
lean_del_object(v___x_4694_);
lean_dec(v_a_4690_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v___x_4687_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v_h2_4656_);
lean_dec_ref(v_h1_4655_);
v___y_4663_ = v_a_4657_;
v___y_4664_ = v_a_4658_;
v___y_4665_ = v_a_4659_;
v___y_4666_ = v_a_4660_;
goto v___jp_4662_;
}
}
else
{
lean_dec_ref(v_body_4696_);
lean_del_object(v___x_4694_);
lean_dec(v_a_4690_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v___x_4687_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v_h2_4656_);
lean_dec_ref(v_h1_4655_);
v___y_4663_ = v_a_4657_;
v___y_4664_ = v_a_4658_;
v___y_4665_ = v_a_4659_;
v___y_4666_ = v_a_4660_;
goto v___jp_4662_;
}
}
else
{
lean_del_object(v___x_4694_);
lean_dec(v_a_4692_);
lean_dec(v_a_4690_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v___x_4687_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v_h2_4656_);
lean_dec_ref(v_h1_4655_);
v___y_4663_ = v_a_4657_;
v___y_4664_ = v_a_4658_;
v___y_4665_ = v_a_4659_;
v___y_4666_ = v_a_4660_;
goto v___jp_4662_;
}
}
}
else
{
lean_dec(v_a_4690_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v___x_4687_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v_h2_4656_);
lean_dec_ref(v_h1_4655_);
lean_dec_ref(v_motive_4654_);
return v___x_4691_;
}
}
else
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
lean_dec_ref(v___x_4688_);
lean_dec_ref(v___x_4687_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v_h2_4656_);
lean_dec_ref(v_h1_4655_);
lean_dec_ref(v_motive_4654_);
v_a_4717_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4719_ = v___x_4689_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4689_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4656_);
lean_dec_ref(v_h1_4655_);
lean_dec_ref(v_motive_4654_);
return v___x_4674_;
}
}
else
{
lean_object* v___x_4725_; 
lean_dec_ref(v_h2_4656_);
lean_dec_ref(v_motive_4654_);
v___x_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4725_, 0, v_h1_4655_);
return v___x_4725_;
}
v___jp_4662_:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4667_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4668_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4669_ = l_Lean_indentExpr(v_motive_4654_);
v___x_4670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4668_);
lean_ctor_set(v___x_4670_, 1, v___x_4669_);
v___x_4671_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4667_, v___x_4670_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
return v___x_4671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4726_, lean_object* v_h1_4727_, lean_object* v_h2_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Lean_Meta_mkEqRec(v_motive_4726_, v_h1_4727_, v_h2_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore(lean_object* v_00_u03b1_4739_, lean_object* v_00_u03b2_4740_, lean_object* v_h_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v___x_4748_; 
lean_inc_ref(v_00_u03b1_4739_);
v___x_4748_ = l_Lean_Meta_getLevel(v_00_u03b1_4739_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4761_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4751_ = v___x_4748_;
v_isShared_4752_ = v_isSharedCheck_4761_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4748_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4761_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4759_; 
v___x_4753_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4754_ = lean_box(0);
v___x_4755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4755_, 0, v_a_4749_);
lean_ctor_set(v___x_4755_, 1, v___x_4754_);
v___x_4756_ = l_Lean_mkConst(v___x_4753_, v___x_4755_);
v___x_4757_ = l_Lean_mkApp4(v___x_4756_, v_00_u03b1_4739_, v_00_u03b2_4740_, v_h_4741_, v_a_4742_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4757_);
v___x_4759_ = v___x_4751_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___x_4757_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_dec_ref(v_a_4742_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_00_u03b2_4740_);
lean_dec_ref(v_00_u03b1_4739_);
v_a_4762_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4748_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4748_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore___boxed(lean_object* v_00_u03b1_4770_, lean_object* v_00_u03b2_4771_, lean_object* v_h_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Lean_Meta_mkEqMPCore(v_00_u03b1_4770_, v_00_u03b2_4771_, v_h_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4780_, lean_object* v_pr_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v___x_4787_; 
lean_inc_ref(v_eqProof_4780_);
v___x_4787_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_eqProof_4780_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref_known(v___x_4787_, 1);
v___x_4789_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4790_ = lean_unsigned_to_nat(3u);
v___x_4791_ = l_Lean_Expr_isAppOfArity(v_a_4788_, v___x_4789_, v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_dec_ref(v_pr_4781_);
v___x_4792_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4793_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4794_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_eqProof_4780_, v_a_4788_);
v___x_4795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4793_);
lean_ctor_set(v___x_4795_, 1, v___x_4794_);
v___x_4796_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4792_, v___x_4795_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
return v___x_4796_;
}
else
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4797_ = l_Lean_Expr_appFn_x21(v_a_4788_);
v___x_4798_ = l_Lean_Expr_appArg_x21(v___x_4797_);
lean_dec_ref(v___x_4797_);
v___x_4799_ = l_Lean_Expr_appArg_x21(v_a_4788_);
lean_dec(v_a_4788_);
v___x_4800_ = l_Lean_Meta_mkEqMPCore(v___x_4798_, v___x_4799_, v_eqProof_4780_, v_pr_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
return v___x_4800_;
}
}
else
{
lean_dec_ref(v_pr_4781_);
lean_dec_ref(v_eqProof_4780_);
return v___x_4787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4801_, lean_object* v_pr_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Lean_Meta_mkEqMP(v_eqProof_4801_, v_pr_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4813_, lean_object* v_pr_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4820_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4821_ = lean_unsigned_to_nat(2u);
v___x_4822_ = lean_mk_empty_array_with_capacity(v___x_4821_);
v___x_4823_ = lean_array_push(v___x_4822_, v_eqProof_4813_);
v___x_4824_ = lean_array_push(v___x_4823_, v_pr_4814_);
v___x_4825_ = l_Lean_Meta_mkAppM(v___x_4820_, v___x_4824_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4826_, lean_object* v_pr_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_Meta_mkEqMPR(v_eqProof_4826_, v_pr_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v___f_4840_; lean_object* v___x_12329__overap_4841_; lean_object* v___x_4842_; 
v___f_4840_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12329__overap_4841_ = lean_panic_fn_borrowed(v___f_4840_, v_msg_4834_);
lean_inc(v___y_4838_);
lean_inc_ref(v___y_4837_);
lean_inc(v___y_4836_);
lean_inc_ref(v___y_4835_);
v___x_4842_ = lean_apply_5(v___x_12329__overap_4841_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, lean_box(0));
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4850_, uint8_t v_skipRealize_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v___x_4854_; lean_object* v_env_4855_; uint8_t v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4854_ = lean_st_ref_get(v___y_4852_);
v_env_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc_ref(v_env_4855_);
lean_dec(v___x_4854_);
v___x_4856_ = l_Lean_Environment_contains(v_env_4855_, v_constName_4850_, v_skipRealize_4851_);
v___x_4857_ = lean_box(v___x_4856_);
v___x_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4857_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4859_, lean_object* v_skipRealize_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
uint8_t v_skipRealize_boxed_4863_; lean_object* v_res_4864_; 
v_skipRealize_boxed_4863_ = lean_unbox(v_skipRealize_4860_);
v_res_4864_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4859_, v_skipRealize_boxed_4863_, v___y_4861_);
lean_dec(v___y_4861_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4865_, uint8_t v_skipRealize_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4865_, v_skipRealize_4866_, v___y_4870_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4873_, lean_object* v_skipRealize_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
uint8_t v_skipRealize_boxed_4880_; lean_object* v_res_4881_; 
v_skipRealize_boxed_4880_ = lean_unbox(v_skipRealize_4874_);
v_res_4881_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4873_, v_skipRealize_boxed_4880_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___y_4882_, uint8_t v___x_4883_, lean_object* v_P_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; uint8_t v___x_4893_; lean_object* v___x_4894_; 
v___x_4890_ = lean_unsigned_to_nat(1u);
v___x_4891_ = lean_mk_empty_array_with_capacity(v___x_4890_);
lean_inc_ref(v_P_4884_);
v___x_4892_ = lean_array_push(v___x_4891_, v_P_4884_);
v___x_4893_ = 1;
v___x_4894_ = l_Lean_Meta_mkLambdaFVars(v___x_4892_, v_P_4884_, v___y_4882_, v___x_4883_, v___y_4882_, v___x_4883_, v___x_4893_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
lean_dec_ref(v___x_4892_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___y_4895_, lean_object* v___x_4896_, lean_object* v_P_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
uint8_t v___y_13587__boxed_4903_; uint8_t v___x_13588__boxed_4904_; lean_object* v_res_4905_; 
v___y_13587__boxed_4903_ = lean_unbox(v___y_4895_);
v___x_13588__boxed_4904_ = lean_unbox(v___x_4896_);
v_res_4905_ = l_Lean_Meta_mkNoConfusion___lam__0(v___y_13587__boxed_4903_, v___x_13588__boxed_4904_, v_P_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
return v_res_4905_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4907_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4908_ = l_Lean_stringToMessageData(v___x_4907_);
return v___x_4908_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4911_ = l_Lean_stringToMessageData(v___x_4910_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4912_, lean_object* v_b_4913_, lean_object* v_i_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v_stop_4920_; lean_object* v_step_4921_; lean_object* v_a_4923_; uint8_t v___x_4926_; 
v_stop_4920_ = lean_ctor_get(v_range_4912_, 1);
v_step_4921_ = lean_ctor_get(v_range_4912_, 2);
v___x_4926_ = lean_nat_dec_lt(v_i_4914_, v_stop_4920_);
if (v___x_4926_ == 0)
{
lean_object* v___x_4927_; 
lean_dec(v_i_4914_);
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v_b_4913_);
return v___x_4927_;
}
else
{
lean_object* v___x_4928_; 
lean_inc(v___y_4918_);
lean_inc_ref(v___y_4917_);
lean_inc(v___y_4916_);
lean_inc_ref(v___y_4915_);
lean_inc_ref(v_b_4913_);
v___x_4928_ = lean_infer_type(v_b_4913_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
v___x_4930_ = l_Lean_Meta_whnfForall(v_a_4929_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = l_Lean_Expr_bindingDomain_x21(v_a_4931_);
lean_dec(v_a_4931_);
lean_inc(v___y_4918_);
lean_inc_ref(v___y_4917_);
lean_inc(v___y_4916_);
lean_inc_ref(v___y_4915_);
v___x_4933_ = lean_whnf(v___x_4932_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v_a_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; uint8_t v___x_4937_; 
v_a_4934_ = lean_ctor_get(v___x_4933_, 0);
lean_inc(v_a_4934_);
lean_dec_ref_known(v___x_4933_, 1);
v___x_4935_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4936_ = lean_unsigned_to_nat(4u);
v___x_4937_ = l_Lean_Expr_isAppOfArity(v_a_4934_, v___x_4935_, v___x_4936_);
if (v___x_4937_ == 0)
{
lean_object* v___x_4938_; lean_object* v___x_4939_; uint8_t v___x_4940_; 
v___x_4938_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4939_ = lean_unsigned_to_nat(3u);
v___x_4940_ = l_Lean_Expr_isAppOfArity(v_a_4934_, v___x_4938_, v___x_4939_);
if (v___x_4940_ == 0)
{
lean_object* v___x_4941_; 
lean_dec(v_i_4914_);
lean_inc(v___y_4918_);
lean_inc_ref(v___y_4917_);
lean_inc(v___y_4916_);
lean_inc_ref(v___y_4915_);
v___x_4941_ = lean_infer_type(v_b_4913_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v_a_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
lean_inc(v_a_4942_);
lean_dec_ref_known(v___x_4941_, 1);
v___x_4943_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4944_ = l_Lean_MessageData_ofExpr(v_a_4934_);
v___x_4945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4943_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
v___x_4946_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4945_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
v___x_4948_ = lean_unsigned_to_nat(30u);
v___x_4949_ = l_Lean_inlineExpr(v_a_4942_, v___x_4948_);
v___x_4950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4947_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4950_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4951_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4951_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
else
{
lean_dec(v_a_4934_);
return v___x_4941_;
}
}
else
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4960_ = l_Lean_Expr_appFn_x21(v_a_4934_);
lean_dec(v_a_4934_);
v___x_4961_ = l_Lean_Expr_appArg_x21(v___x_4960_);
lean_dec_ref(v___x_4960_);
v___x_4962_ = l_Lean_Meta_mkEqRefl(v___x_4961_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4964_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v___x_4964_ = l_Lean_Expr_app___override(v_b_4913_, v_a_4963_);
v_a_4923_ = v___x_4964_;
goto v___jp_4922_;
}
else
{
lean_dec(v_i_4914_);
lean_dec_ref(v_b_4913_);
return v___x_4962_;
}
}
}
else
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4965_ = l_Lean_Expr_appFn_x21(v_a_4934_);
lean_dec(v_a_4934_);
v___x_4966_ = l_Lean_Expr_appFn_x21(v___x_4965_);
lean_dec_ref(v___x_4965_);
v___x_4967_ = l_Lean_Expr_appArg_x21(v___x_4966_);
lean_dec_ref(v___x_4966_);
v___x_4968_ = l_Lean_Meta_mkHEqRefl(v___x_4967_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
if (lean_obj_tag(v___x_4968_) == 0)
{
lean_object* v_a_4969_; lean_object* v___x_4970_; 
v_a_4969_ = lean_ctor_get(v___x_4968_, 0);
lean_inc(v_a_4969_);
lean_dec_ref_known(v___x_4968_, 1);
v___x_4970_ = l_Lean_Expr_app___override(v_b_4913_, v_a_4969_);
v_a_4923_ = v___x_4970_;
goto v___jp_4922_;
}
else
{
lean_dec(v_i_4914_);
lean_dec_ref(v_b_4913_);
return v___x_4968_;
}
}
}
else
{
lean_dec(v_i_4914_);
lean_dec_ref(v_b_4913_);
return v___x_4933_;
}
}
else
{
lean_dec(v_i_4914_);
lean_dec_ref(v_b_4913_);
return v___x_4930_;
}
}
else
{
lean_dec(v_i_4914_);
lean_dec_ref(v_b_4913_);
return v___x_4928_;
}
}
v___jp_4922_:
{
lean_object* v___x_4924_; 
v___x_4924_ = lean_nat_add(v_i_4914_, v_step_4921_);
lean_dec(v_i_4914_);
v_b_4913_ = v_a_4923_;
v_i_4914_ = v___x_4924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4971_, lean_object* v_b_4972_, lean_object* v_i_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4971_, v_b_4972_, v_i_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec_ref(v_range_4971_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4980_, lean_object* v_b_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v___x_4987_; 
lean_inc(v___y_4985_);
lean_inc_ref(v___y_4984_);
lean_inc(v___y_4983_);
lean_inc_ref(v___y_4982_);
v___x_4987_ = lean_apply_6(v_k_4980_, v_b_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, lean_box(0));
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4988_, lean_object* v_b_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4988_, v_b_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec(v___y_4991_);
lean_dec_ref(v___y_4990_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4996_, uint8_t v_bi_4997_, lean_object* v_type_4998_, lean_object* v_k_4999_, uint8_t v_kind_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v___f_5006_; lean_object* v___x_5007_; 
v___f_5006_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5006_, 0, v_k_4999_);
v___x_5007_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4996_, v_bi_4997_, v_type_4998_, v___f_5006_, v_kind_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_5007_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_5007_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
v_a_5016_ = lean_ctor_get(v___x_5007_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_5007_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_5007_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_5024_, lean_object* v_bi_5025_, lean_object* v_type_5026_, lean_object* v_k_5027_, lean_object* v_kind_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
uint8_t v_bi_boxed_5034_; uint8_t v_kind_boxed_5035_; lean_object* v_res_5036_; 
v_bi_boxed_5034_ = lean_unbox(v_bi_5025_);
v_kind_boxed_5035_ = lean_unbox(v_kind_5028_);
v_res_5036_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5024_, v_bi_boxed_5034_, v_type_5026_, v_k_5027_, v_kind_boxed_5035_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_5037_, lean_object* v_type_5038_, lean_object* v_k_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
uint8_t v___x_5045_; uint8_t v___x_5046_; lean_object* v___x_5047_; 
v___x_5045_ = 0;
v___x_5046_ = 0;
v___x_5047_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5037_, v___x_5045_, v_type_5038_, v_k_5039_, v___x_5046_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_5048_, lean_object* v_type_5049_, lean_object* v_k_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5048_, v_type_5049_, v_k_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
return v_res_5056_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_5064_ = l_Lean_MessageData_ofFormat(v___x_5063_);
return v___x_5064_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6(void){
_start:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5066_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__5));
v___x_5067_ = l_Lean_stringToMessageData(v___x_5066_);
return v___x_5067_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8(void){
_start:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__7));
v___x_5070_ = l_Lean_stringToMessageData(v___x_5069_);
return v___x_5070_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___x_5074_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_5075_ = l_Lean_MessageData_ofFormat(v___x_5074_);
return v___x_5075_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__14(void){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5078_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__13));
v___x_5079_ = lean_unsigned_to_nat(10u);
v___x_5080_ = lean_unsigned_to_nat(511u);
v___x_5081_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5082_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5083_ = l_mkPanicMessageWithDecl(v___x_5082_, v___x_5081_, v___x_5080_, v___x_5079_, v___x_5078_);
return v___x_5083_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5086_ = l_Lean_stringToMessageData(v___x_5085_);
return v___x_5086_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__23(void){
_start:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5095_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__22));
v___x_5096_ = l_Lean_stringToMessageData(v___x_5095_);
return v___x_5096_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__24(void){
_start:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5098_ = l_Lean_MessageData_ofName(v___x_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5099_, lean_object* v_h_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v___x_5106_; 
lean_inc(v_a_5104_);
lean_inc_ref(v_a_5103_);
lean_inc(v_a_5102_);
lean_inc_ref(v_a_5101_);
lean_inc_ref(v_h_5100_);
v___x_5106_ = lean_infer_type(v_h_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; lean_object* v___x_5108_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5107_);
lean_dec_ref_known(v___x_5106_, 1);
lean_inc(v_a_5104_);
lean_inc_ref(v_a_5103_);
lean_inc(v_a_5102_);
lean_inc_ref(v_a_5101_);
v___x_5108_ = lean_whnf(v_a_5107_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; uint8_t v___x_5112_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___x_5108_, 1);
v___x_5110_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5111_ = lean_unsigned_to_nat(3u);
v___x_5112_ = l_Lean_Expr_isAppOfArity(v_a_5109_, v___x_5110_, v___x_5111_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_dec_ref(v_target_5099_);
v___x_5113_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5114_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5115_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5100_, v_a_5109_);
v___x_5116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5116_, 0, v___x_5114_);
lean_ctor_set(v___x_5116_, 1, v___x_5115_);
v___x_5117_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5113_, v___x_5116_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
return v___x_5117_;
}
else
{
lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___y_5124_; lean_object* v___y_5125_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v___x_5136_; 
v___x_5118_ = l_Lean_Expr_appFn_x21(v_a_5109_);
v___x_5119_ = l_Lean_Expr_appFn_x21(v___x_5118_);
v___x_5120_ = l_Lean_Expr_appArg_x21(v___x_5119_);
lean_dec_ref(v___x_5119_);
v___x_5121_ = l_Lean_Expr_appArg_x21(v___x_5118_);
lean_dec_ref(v___x_5118_);
v___x_5122_ = l_Lean_Expr_appArg_x21(v_a_5109_);
lean_dec(v_a_5109_);
v___x_5136_ = l_Lean_Meta_whnfD(v___x_5120_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
if (lean_obj_tag(v___x_5136_) == 0)
{
lean_object* v_a_5137_; lean_object* v___y_5139_; lean_object* v___y_5140_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v___x_5148_; 
v_a_5137_ = lean_ctor_get(v___x_5136_, 0);
lean_inc(v_a_5137_);
lean_dec_ref_known(v___x_5136_, 1);
v___x_5148_ = l_Lean_Expr_getAppFn(v_a_5137_);
if (lean_obj_tag(v___x_5148_) == 4)
{
lean_object* v_declName_5149_; lean_object* v_us_5150_; lean_object* v___x_5151_; lean_object* v_env_5152_; uint8_t v___x_5153_; lean_object* v___x_5154_; 
v_declName_5149_ = lean_ctor_get(v___x_5148_, 0);
lean_inc(v_declName_5149_);
v_us_5150_ = lean_ctor_get(v___x_5148_, 1);
lean_inc(v_us_5150_);
lean_dec_ref_known(v___x_5148_, 2);
v___x_5151_ = lean_st_ref_get(v_a_5104_);
v_env_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc_ref(v_env_5152_);
lean_dec(v___x_5151_);
v___x_5153_ = 0;
v___x_5154_ = l_Lean_Environment_find_x3f(v_env_5152_, v_declName_5149_, v___x_5153_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_dec(v_us_5150_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v___y_5139_ = v_a_5101_;
v___y_5140_ = v_a_5102_;
v___y_5141_ = v_a_5103_;
v___y_5142_ = v_a_5104_;
goto v___jp_5138_;
}
else
{
lean_object* v_val_5155_; 
v_val_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_val_5155_);
lean_dec_ref_known(v___x_5154_, 1);
if (lean_obj_tag(v_val_5155_) == 5)
{
lean_object* v_val_5156_; lean_object* v___x_5157_; 
v_val_5156_ = lean_ctor_get(v_val_5155_, 0);
lean_inc_ref(v_val_5156_);
lean_dec_ref_known(v_val_5155_, 1);
lean_inc_ref(v_target_5099_);
v___x_5157_ = l_Lean_Meta_getLevel(v_target_5099_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_object* v_a_5158_; lean_object* v___x_5159_; 
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc(v_a_5158_);
lean_dec_ref_known(v___x_5157_, 1);
lean_inc_ref(v___x_5121_);
v___x_5159_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5121_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5159_, 1);
if (lean_obj_tag(v_a_5160_) == 1)
{
lean_object* v_val_5161_; lean_object* v_fst_5162_; lean_object* v_snd_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5377_; 
v_val_5161_ = lean_ctor_get(v_a_5160_, 0);
lean_inc(v_val_5161_);
lean_dec_ref_known(v_a_5160_, 1);
v_fst_5162_ = lean_ctor_get(v_val_5161_, 0);
v_snd_5163_ = lean_ctor_get(v_val_5161_, 1);
v_isSharedCheck_5377_ = !lean_is_exclusive(v_val_5161_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5165_ = v_val_5161_;
v_isShared_5166_ = v_isSharedCheck_5377_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_snd_5163_);
lean_inc(v_fst_5162_);
lean_dec(v_val_5161_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5377_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5167_; 
lean_inc_ref(v___x_5122_);
v___x_5167_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5122_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
if (lean_obj_tag(v_a_5168_) == 1)
{
lean_object* v_val_5169_; lean_object* v_fst_5170_; lean_object* v_snd_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5368_; 
v_val_5169_ = lean_ctor_get(v_a_5168_, 0);
lean_inc(v_val_5169_);
lean_dec_ref_known(v_a_5168_, 1);
v_fst_5170_ = lean_ctor_get(v_val_5169_, 0);
v_snd_5171_ = lean_ctor_get(v_val_5169_, 1);
v_isSharedCheck_5368_ = !lean_is_exclusive(v_val_5169_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5173_ = v_val_5169_;
v_isShared_5174_ = v_isSharedCheck_5368_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_snd_5171_);
lean_inc(v_fst_5170_);
lean_dec(v_val_5169_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5368_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v_toConstantVal_5175_; lean_object* v_cidx_5176_; lean_object* v_numParams_5177_; lean_object* v_numFields_5178_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___y_5184_; lean_object* v___y_5185_; uint8_t v___y_5270_; lean_object* v_cidx_5298_; uint8_t v___x_5299_; 
v_toConstantVal_5175_ = lean_ctor_get(v_fst_5162_, 0);
lean_inc_ref(v_toConstantVal_5175_);
v_cidx_5176_ = lean_ctor_get(v_fst_5162_, 2);
lean_inc(v_cidx_5176_);
v_numParams_5177_ = lean_ctor_get(v_fst_5162_, 3);
lean_inc(v_numParams_5177_);
v_numFields_5178_ = lean_ctor_get(v_fst_5162_, 4);
lean_inc(v_numFields_5178_);
lean_dec(v_fst_5162_);
v_cidx_5298_ = lean_ctor_get(v_fst_5170_, 2);
lean_inc(v_cidx_5298_);
lean_dec(v_fst_5170_);
v___x_5299_ = lean_nat_dec_eq(v_cidx_5176_, v_cidx_5298_);
lean_dec(v_cidx_5298_);
lean_dec(v_cidx_5176_);
if (v___x_5299_ == 0)
{
if (v___x_5112_ == 0)
{
lean_dec_ref(v_val_5156_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
v___y_5270_ = v___x_5112_;
goto v___jp_5269_;
}
else
{
lean_object* v_toConstantVal_5300_; lean_object* v_name_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v_a_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v_a_5308_; uint8_t v___x_5326_; 
lean_dec(v_numFields_5178_);
lean_dec(v_numParams_5177_);
lean_dec_ref(v_toConstantVal_5175_);
lean_del_object(v___x_5173_);
lean_dec(v_snd_5171_);
lean_del_object(v___x_5165_);
lean_dec(v_snd_5163_);
v_toConstantVal_5300_ = lean_ctor_get(v_val_5156_, 0);
lean_inc_ref(v_toConstantVal_5300_);
lean_dec_ref(v_val_5156_);
v_name_5301_ = lean_ctor_get(v_toConstantVal_5300_, 0);
lean_inc(v_name_5301_);
lean_dec_ref(v_toConstantVal_5300_);
v___x_5302_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__19));
v___x_5303_ = l_Lean_Name_str___override(v_name_5301_, v___x_5302_);
lean_inc(v___x_5303_);
v___x_5304_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5303_, v___x_5112_, v_a_5104_);
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
lean_inc(v_a_5305_);
lean_dec_ref(v___x_5304_);
v___x_5306_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5307_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5306_, v___x_5112_, v_a_5104_);
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref(v___x_5307_);
v___x_5326_ = lean_unbox(v_a_5305_);
lean_dec(v_a_5305_);
if (v___x_5326_ == 0)
{
lean_dec(v_a_5308_);
lean_dec(v_a_5158_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
goto v___jp_5309_;
}
else
{
uint8_t v___x_5327_; 
v___x_5327_ = lean_unbox(v_a_5308_);
lean_dec(v_a_5308_);
if (v___x_5327_ == 0)
{
lean_dec(v_a_5158_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
goto v___jp_5309_;
}
else
{
lean_object* v___x_5328_; lean_object* v_dummy_5329_; lean_object* v_nargs_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5328_ = l_Lean_mkConst(v___x_5303_, v_us_5150_);
v_dummy_5329_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5330_ = l_Lean_Expr_getAppNumArgs(v_a_5137_);
lean_inc(v_nargs_5330_);
v___x_5331_ = lean_mk_array(v_nargs_5330_, v_dummy_5329_);
v___x_5332_ = lean_unsigned_to_nat(1u);
v___x_5333_ = lean_nat_sub(v_nargs_5330_, v___x_5332_);
lean_dec(v_nargs_5330_);
lean_inc_n(v_a_5137_, 2);
v___x_5334_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5137_, v___x_5331_, v___x_5333_);
v___x_5335_ = l_Lean_mkAppN(v___x_5328_, v___x_5334_);
lean_dec_ref(v___x_5334_);
v___x_5336_ = l_Lean_Meta_getLevel(v_a_5137_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v_a_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5359_; 
v_a_5337_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5339_ = v___x_5336_;
v_isShared_5340_ = v_isSharedCheck_5359_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_a_5337_);
lean_dec(v___x_5336_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5359_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5357_; 
v___x_5341_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5342_ = lean_box(0);
v___x_5343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5343_, 0, v_a_5158_);
lean_ctor_set(v___x_5343_, 1, v___x_5342_);
v___x_5344_ = l_Lean_mkConst(v___x_5341_, v___x_5343_);
v___x_5345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5345_, 0, v_a_5337_);
lean_ctor_set(v___x_5345_, 1, v___x_5342_);
v___x_5346_ = l_Lean_mkConst(v___x_5306_, v___x_5345_);
v___x_5347_ = lean_unsigned_to_nat(5u);
v___x_5348_ = lean_mk_empty_array_with_capacity(v___x_5347_);
v___x_5349_ = lean_array_push(v___x_5348_, v_a_5137_);
v___x_5350_ = lean_array_push(v___x_5349_, v___x_5335_);
v___x_5351_ = lean_array_push(v___x_5350_, v___x_5121_);
v___x_5352_ = lean_array_push(v___x_5351_, v___x_5122_);
v___x_5353_ = lean_array_push(v___x_5352_, v_h_5100_);
v___x_5354_ = l_Lean_mkAppN(v___x_5346_, v___x_5353_);
lean_dec_ref(v___x_5353_);
v___x_5355_ = l_Lean_mkAppB(v___x_5344_, v_target_5099_, v___x_5354_);
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 0, v___x_5355_);
v___x_5357_ = v___x_5339_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v___x_5355_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec_ref(v___x_5335_);
lean_dec(v_a_5158_);
lean_dec(v_a_5137_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v_a_5360_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5336_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5336_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
v___jp_5309_:
{
lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
v___x_5310_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5311_ = l_Lean_MessageData_ofName(v___x_5303_);
v___x_5312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5312_, 0, v___x_5310_);
lean_ctor_set(v___x_5312_, 1, v___x_5311_);
v___x_5313_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__23, &l_Lean_Meta_mkNoConfusion___closed__23_once, _init_l_Lean_Meta_mkNoConfusion___closed__23);
v___x_5314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5312_);
lean_ctor_set(v___x_5314_, 1, v___x_5313_);
v___x_5315_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__24, &l_Lean_Meta_mkNoConfusion___closed__24_once, _init_l_Lean_Meta_mkNoConfusion___closed__24);
v___x_5316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5316_, 0, v___x_5314_);
lean_ctor_set(v___x_5316_, 1, v___x_5315_);
v___x_5317_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5316_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5320_ = v___x_5317_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5317_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
}
else
{
lean_dec_ref(v_val_5156_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
v___y_5270_ = v___x_5153_;
goto v___jp_5269_;
}
v___jp_5179_:
{
lean_object* v___x_5186_; 
lean_inc(v___y_5181_);
v___x_5186_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; lean_object* v_nargs_5188_; lean_object* v_type_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5258_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref_known(v___x_5186_, 1);
v_nargs_5188_ = l_Lean_Expr_getAppNumArgs(v_a_5137_);
v_type_5189_ = lean_ctor_get(v_a_5187_, 2);
v_isSharedCheck_5258_ = !lean_is_exclusive(v_a_5187_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; lean_object* v_unused_5260_; 
v_unused_5259_ = lean_ctor_get(v_a_5187_, 1);
lean_dec(v_unused_5259_);
v_unused_5260_ = lean_ctor_get(v_a_5187_, 0);
lean_dec(v_unused_5260_);
v___x_5191_ = v_a_5187_;
v_isShared_5192_ = v_isSharedCheck_5258_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_type_5189_);
lean_dec(v_a_5187_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5258_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v_dummy_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v_start_5199_; lean_object* v_stop_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; uint8_t v___x_5214_; 
v_dummy_5193_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
lean_inc(v_nargs_5188_);
v___x_5194_ = lean_mk_array(v_nargs_5188_, v_dummy_5193_);
v___x_5195_ = lean_unsigned_to_nat(1u);
v___x_5196_ = lean_nat_sub(v_nargs_5188_, v___x_5195_);
lean_dec(v_nargs_5188_);
v___x_5197_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5137_, v___x_5194_, v___x_5196_);
lean_inc_n(v_numParams_5177_, 2);
lean_inc(v___y_5180_);
v___x_5198_ = l_Array_toSubarray___redArg(v___x_5197_, v___y_5180_, v_numParams_5177_);
v_start_5199_ = lean_ctor_get(v___x_5198_, 1);
v_stop_5200_ = lean_ctor_get(v___x_5198_, 2);
v___x_5201_ = lean_array_get_size(v_snd_5163_);
v___x_5202_ = l_Array_toSubarray___redArg(v_snd_5163_, v_numParams_5177_, v___x_5201_);
v___x_5203_ = lean_array_get_size(v_snd_5171_);
v___x_5204_ = l_Subarray_copy___redArg(v___x_5202_);
v___x_5205_ = l_Array_toSubarray___redArg(v_snd_5171_, v_numParams_5177_, v___x_5203_);
v___x_5206_ = l_Subarray_copy___redArg(v___x_5205_);
v___x_5207_ = l_Lean_Expr_getNumHeadForalls(v_type_5189_);
lean_dec_ref(v_type_5189_);
v___x_5208_ = lean_nat_sub(v_stop_5200_, v_start_5199_);
v___x_5209_ = lean_array_get_size(v___x_5204_);
v___x_5210_ = lean_nat_add(v___x_5208_, v___x_5209_);
lean_dec(v___x_5208_);
v___x_5211_ = lean_array_get_size(v___x_5206_);
v___x_5212_ = lean_nat_add(v___x_5210_, v___x_5211_);
lean_dec(v___x_5210_);
v___x_5213_ = lean_nat_add(v___x_5212_, v___x_5111_);
lean_dec(v___x_5212_);
v___x_5214_ = lean_nat_dec_le(v___x_5213_, v___x_5207_);
if (v___x_5214_ == 0)
{
lean_object* v___x_5215_; lean_object* v___x_5216_; 
lean_dec(v___x_5213_);
lean_dec(v___x_5207_);
lean_dec_ref(v___x_5206_);
lean_dec_ref(v___x_5204_);
lean_dec_ref(v___x_5198_);
lean_del_object(v___x_5191_);
lean_dec(v___y_5181_);
lean_dec(v___y_5180_);
lean_del_object(v___x_5173_);
lean_dec(v_a_5158_);
lean_dec(v_us_5150_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v___x_5215_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__14, &l_Lean_Meta_mkNoConfusion___closed__14_once, _init_l_Lean_Meta_mkNoConfusion___closed__14);
v___x_5216_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5215_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
return v___x_5216_;
}
else
{
lean_object* v___x_5218_; 
if (v_isShared_5174_ == 0)
{
lean_ctor_set_tag(v___x_5173_, 1);
lean_ctor_set(v___x_5173_, 1, v_us_5150_);
lean_ctor_set(v___x_5173_, 0, v_a_5158_);
v___x_5218_ = v___x_5173_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5158_);
lean_ctor_set(v_reuseFailAlloc_5257_, 1, v_us_5150_);
v___x_5218_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5229_; 
v___x_5219_ = l_Lean_mkConst(v___y_5181_, v___x_5218_);
v___x_5220_ = l_Subarray_copy___redArg(v___x_5198_);
v___x_5221_ = l_Lean_mkAppN(v___x_5219_, v___x_5220_);
lean_dec_ref(v___x_5220_);
v___x_5222_ = lean_mk_empty_array_with_capacity(v___x_5195_);
v___x_5223_ = lean_array_push(v___x_5222_, v_target_5099_);
v___x_5224_ = l_Array_append___redArg(v___x_5223_, v___x_5204_);
lean_dec_ref(v___x_5204_);
v___x_5225_ = l_Array_append___redArg(v___x_5224_, v___x_5206_);
lean_dec_ref(v___x_5206_);
v___x_5226_ = l_Lean_mkAppN(v___x_5221_, v___x_5225_);
lean_dec_ref(v___x_5225_);
v___x_5227_ = lean_nat_sub(v___x_5207_, v___x_5213_);
lean_dec(v___x_5213_);
lean_dec(v___x_5207_);
lean_inc(v___y_5180_);
if (v_isShared_5192_ == 0)
{
lean_ctor_set(v___x_5191_, 2, v___x_5195_);
lean_ctor_set(v___x_5191_, 1, v___x_5227_);
lean_ctor_set(v___x_5191_, 0, v___y_5180_);
v___x_5229_ = v___x_5191_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v___y_5180_);
lean_ctor_set(v_reuseFailAlloc_5256_, 1, v___x_5227_);
lean_ctor_set(v_reuseFailAlloc_5256_, 2, v___x_5195_);
v___x_5229_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
lean_object* v___x_5230_; 
v___x_5230_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5229_, v___x_5226_, v___y_5180_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
lean_dec_ref(v___x_5229_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5232_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc_n(v_a_5231_, 2);
lean_dec_ref_known(v___x_5230_, 1);
lean_inc(v___y_5185_);
lean_inc_ref(v___y_5184_);
lean_inc(v___y_5183_);
lean_inc_ref(v___y_5182_);
v___x_5232_ = lean_infer_type(v_a_5231_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v___x_5234_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_a_5233_);
lean_dec_ref_known(v___x_5232_, 1);
v___x_5234_ = l_Lean_Meta_whnfForall(v_a_5233_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
if (lean_obj_tag(v___x_5234_) == 0)
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5255_; 
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5234_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5237_ = v___x_5234_;
v_isShared_5238_ = v_isSharedCheck_5255_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5234_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5255_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5239_; uint8_t v___x_5240_; 
v___x_5239_ = l_Lean_Expr_bindingDomain_x21(v_a_5235_);
lean_dec(v_a_5235_);
v___x_5240_ = l_Lean_Expr_isHEq(v___x_5239_);
lean_dec_ref(v___x_5239_);
if (v___x_5240_ == 0)
{
lean_object* v___x_5241_; lean_object* v___x_5243_; 
v___x_5241_ = l_Lean_Expr_app___override(v_a_5231_, v_h_5100_);
if (v_isShared_5238_ == 0)
{
lean_ctor_set(v___x_5237_, 0, v___x_5241_);
v___x_5243_ = v___x_5237_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5241_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
else
{
lean_object* v___x_5245_; 
lean_del_object(v___x_5237_);
v___x_5245_ = l_Lean_Meta_mkHEqOfEq(v_h_5100_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5254_; 
v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5248_ = v___x_5245_;
v_isShared_5249_ = v_isSharedCheck_5254_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5245_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5254_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5250_; lean_object* v___x_5252_; 
v___x_5250_ = l_Lean_Expr_app___override(v_a_5231_, v_a_5246_);
if (v_isShared_5249_ == 0)
{
lean_ctor_set(v___x_5248_, 0, v___x_5250_);
v___x_5252_ = v___x_5248_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v___x_5250_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
else
{
lean_dec(v_a_5231_);
return v___x_5245_;
}
}
}
}
else
{
lean_dec(v_a_5231_);
lean_dec_ref(v_h_5100_);
return v___x_5234_;
}
}
else
{
lean_dec(v_a_5231_);
lean_dec_ref(v_h_5100_);
return v___x_5232_;
}
}
else
{
lean_dec_ref(v_h_5100_);
return v___x_5230_;
}
}
}
}
}
}
else
{
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5268_; 
lean_dec(v___y_5181_);
lean_dec(v___y_5180_);
lean_dec(v_numParams_5177_);
lean_del_object(v___x_5173_);
lean_dec(v_snd_5171_);
lean_dec(v_snd_5163_);
lean_dec(v_a_5158_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v_a_5261_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5263_ = v___x_5186_;
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_5186_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5266_; 
if (v_isShared_5264_ == 0)
{
v___x_5266_ = v___x_5263_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
v___jp_5269_:
{
lean_object* v___x_5271_; uint8_t v___x_5272_; 
v___x_5271_ = lean_unsigned_to_nat(0u);
v___x_5272_ = lean_nat_dec_eq(v_numFields_5178_, v___x_5271_);
lean_dec(v_numFields_5178_);
if (v___x_5272_ == 0)
{
lean_object* v_name_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v_a_5277_; uint8_t v___x_5278_; 
v_name_5273_ = lean_ctor_get(v_toConstantVal_5175_, 0);
lean_inc(v_name_5273_);
lean_dec_ref(v_toConstantVal_5175_);
v___x_5274_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5275_ = l_Lean_Name_str___override(v_name_5273_, v___x_5274_);
lean_inc(v___x_5275_);
v___x_5276_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5275_, v___x_5112_, v_a_5104_);
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
lean_inc(v_a_5277_);
lean_dec_ref(v___x_5276_);
v___x_5278_ = lean_unbox(v_a_5277_);
lean_dec(v_a_5277_);
if (v___x_5278_ == 0)
{
lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5282_; 
lean_dec(v_numParams_5177_);
lean_del_object(v___x_5173_);
lean_dec(v_snd_5171_);
lean_dec(v_snd_5163_);
lean_dec(v_a_5158_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v___x_5279_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5280_ = l_Lean_MessageData_ofName(v___x_5275_);
if (v_isShared_5166_ == 0)
{
lean_ctor_set_tag(v___x_5165_, 7);
lean_ctor_set(v___x_5165_, 1, v___x_5280_);
lean_ctor_set(v___x_5165_, 0, v___x_5279_);
v___x_5282_ = v___x_5165_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5279_);
lean_ctor_set(v_reuseFailAlloc_5292_, 1, v___x_5280_);
v___x_5282_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
lean_object* v___x_5283_; lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
v___x_5283_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5282_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5286_ = v___x_5283_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5283_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
else
{
lean_del_object(v___x_5165_);
v___y_5180_ = v___x_5271_;
v___y_5181_ = v___x_5275_;
v___y_5182_ = v_a_5101_;
v___y_5183_ = v_a_5102_;
v___y_5184_ = v_a_5103_;
v___y_5185_ = v_a_5104_;
goto v___jp_5179_;
}
}
else
{
lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___f_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
lean_dec(v_numParams_5177_);
lean_dec_ref(v_toConstantVal_5175_);
lean_del_object(v___x_5173_);
lean_dec(v_snd_5171_);
lean_del_object(v___x_5165_);
lean_dec(v_snd_5163_);
lean_dec(v_a_5158_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v_h_5100_);
v___x_5293_ = lean_box(v___y_5270_);
v___x_5294_ = lean_box(v___x_5272_);
v___f_5295_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5295_, 0, v___x_5293_);
lean_closure_set(v___f_5295_, 1, v___x_5294_);
v___x_5296_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__18));
v___x_5297_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5296_, v_target_5099_, v___f_5295_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
return v___x_5297_;
}
}
}
}
else
{
lean_dec(v_a_5168_);
lean_del_object(v___x_5165_);
lean_dec(v_snd_5163_);
lean_dec(v_fst_5162_);
lean_dec(v_a_5158_);
lean_dec_ref(v_val_5156_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v___y_5124_ = v_a_5101_;
v___y_5125_ = v_a_5102_;
v___y_5126_ = v_a_5103_;
v___y_5127_ = v_a_5104_;
goto v___jp_5123_;
}
}
else
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
lean_del_object(v___x_5165_);
lean_dec(v_snd_5163_);
lean_dec(v_fst_5162_);
lean_dec(v_a_5158_);
lean_dec_ref(v_val_5156_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v_a_5369_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v___x_5167_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5167_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
}
else
{
lean_dec(v_a_5160_);
lean_dec(v_a_5158_);
lean_dec_ref(v_val_5156_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v___y_5124_ = v_a_5101_;
v___y_5125_ = v_a_5102_;
v___y_5126_ = v_a_5103_;
v___y_5127_ = v_a_5104_;
goto v___jp_5123_;
}
}
else
{
lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
lean_dec(v_a_5158_);
lean_dec_ref(v_val_5156_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v_a_5378_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5159_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5159_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5383_; 
if (v_isShared_5381_ == 0)
{
v___x_5383_ = v___x_5380_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
}
else
{
lean_object* v_a_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5393_; 
lean_dec_ref(v_val_5156_);
lean_dec(v_us_5150_);
lean_dec(v_a_5137_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v_a_5386_ = lean_ctor_get(v___x_5157_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5388_ = v___x_5157_;
v_isShared_5389_ = v_isSharedCheck_5393_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_a_5386_);
lean_dec(v___x_5157_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5393_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v___x_5391_; 
if (v_isShared_5389_ == 0)
{
v___x_5391_ = v___x_5388_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_a_5386_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
else
{
lean_dec(v_val_5155_);
lean_dec(v_us_5150_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v___y_5139_ = v_a_5101_;
v___y_5140_ = v_a_5102_;
v___y_5141_ = v_a_5103_;
v___y_5142_ = v_a_5104_;
goto v___jp_5138_;
}
}
}
else
{
lean_dec_ref(v___x_5148_);
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
v___y_5139_ = v_a_5101_;
v___y_5140_ = v_a_5102_;
v___y_5141_ = v_a_5103_;
v___y_5142_ = v_a_5104_;
goto v___jp_5138_;
}
v___jp_5138_:
{
lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5143_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5144_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5145_ = l_Lean_indentExpr(v_a_5137_);
v___x_5146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5146_, 0, v___x_5144_);
lean_ctor_set(v___x_5146_, 1, v___x_5145_);
v___x_5147_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5143_, v___x_5146_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
return v___x_5147_;
}
}
else
{
lean_dec_ref(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
return v___x_5136_;
}
v___jp_5123_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
v___x_5128_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__6, &l_Lean_Meta_mkNoConfusion___closed__6_once, _init_l_Lean_Meta_mkNoConfusion___closed__6);
v___x_5129_ = l_Lean_MessageData_ofExpr(v___x_5121_);
v___x_5130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5128_);
lean_ctor_set(v___x_5130_, 1, v___x_5129_);
v___x_5131_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__8, &l_Lean_Meta_mkNoConfusion___closed__8_once, _init_l_Lean_Meta_mkNoConfusion___closed__8);
v___x_5132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5132_, 0, v___x_5130_);
lean_ctor_set(v___x_5132_, 1, v___x_5131_);
v___x_5133_ = l_Lean_MessageData_ofExpr(v___x_5122_);
v___x_5134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5134_, 0, v___x_5132_);
lean_ctor_set(v___x_5134_, 1, v___x_5133_);
v___x_5135_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5134_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
return v___x_5135_;
}
}
}
else
{
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
return v___x_5108_;
}
}
else
{
lean_dec_ref(v_h_5100_);
lean_dec_ref(v_target_5099_);
return v___x_5106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5394_, lean_object* v_h_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_){
_start:
{
lean_object* v_res_5401_; 
v_res_5401_ = l_Lean_Meta_mkNoConfusion(v_target_5394_, v_h_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5402_, lean_object* v_b_5403_, lean_object* v_i_5404_, lean_object* v_hs_5405_, lean_object* v_hl_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v___x_5412_; 
v___x_5412_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5402_, v_b_5403_, v_i_5404_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5413_, lean_object* v_b_5414_, lean_object* v_i_5415_, lean_object* v_hs_5416_, lean_object* v_hl_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5413_, v_b_5414_, v_i_5415_, v_hs_5416_, v_hl_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
lean_dec_ref(v_range_5413_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5424_, lean_object* v_name_5425_, uint8_t v_bi_5426_, lean_object* v_type_5427_, lean_object* v_k_5428_, uint8_t v_kind_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v___x_5435_; 
v___x_5435_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5425_, v_bi_5426_, v_type_5427_, v_k_5428_, v_kind_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5436_, lean_object* v_name_5437_, lean_object* v_bi_5438_, lean_object* v_type_5439_, lean_object* v_k_5440_, lean_object* v_kind_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_){
_start:
{
uint8_t v_bi_boxed_5447_; uint8_t v_kind_boxed_5448_; lean_object* v_res_5449_; 
v_bi_boxed_5447_ = lean_unbox(v_bi_5438_);
v_kind_boxed_5448_ = lean_unbox(v_kind_5441_);
v_res_5449_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5436_, v_name_5437_, v_bi_boxed_5447_, v_type_5439_, v_k_5440_, v_kind_boxed_5448_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec(v___y_5443_);
lean_dec_ref(v___y_5442_);
return v_res_5449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5450_, lean_object* v_name_5451_, lean_object* v_type_5452_, lean_object* v_k_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v___x_5459_; 
v___x_5459_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5451_, v_type_5452_, v_k_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5460_, lean_object* v_name_5461_, lean_object* v_type_5462_, lean_object* v_k_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5460_, v_name_5461_, v_type_5462_, v_k_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5475_, lean_object* v_e_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_){
_start:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5482_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5483_, 0, v_monad_5475_);
v___x_5484_ = lean_box(0);
v___x_5485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5485_, 0, v_e_5476_);
v___x_5486_ = lean_unsigned_to_nat(4u);
v___x_5487_ = lean_mk_empty_array_with_capacity(v___x_5486_);
v___x_5488_ = lean_array_push(v___x_5487_, v___x_5483_);
v___x_5489_ = lean_array_push(v___x_5488_, v___x_5484_);
v___x_5490_ = lean_array_push(v___x_5489_, v___x_5484_);
v___x_5491_ = lean_array_push(v___x_5490_, v___x_5485_);
v___x_5492_ = l_Lean_Meta_mkAppOptM(v___x_5482_, v___x_5491_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_);
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5493_, lean_object* v_e_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_){
_start:
{
lean_object* v_res_5500_; 
v_res_5500_ = l_Lean_Meta_mkPure(v_monad_5493_, v_e_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
return v_res_5500_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5511_ = l_Lean_MessageData_ofFormat(v___x_5510_);
return v___x_5511_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5515_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5516_ = l_Lean_MessageData_ofFormat(v___x_5515_);
return v___x_5516_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5520_; lean_object* v___x_5521_; 
v___x_5520_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5521_ = l_Lean_MessageData_ofFormat(v___x_5520_);
return v___x_5521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5522_, lean_object* v_fieldName_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_){
_start:
{
lean_object* v___x_5529_; 
lean_inc(v_a_5527_);
lean_inc_ref(v_a_5526_);
lean_inc(v_a_5525_);
lean_inc_ref(v_a_5524_);
lean_inc_ref(v_s_5522_);
v___x_5529_ = lean_infer_type(v_s_5522_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_);
if (lean_obj_tag(v___x_5529_) == 0)
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5626_; 
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5532_ = v___x_5529_;
v_isShared_5533_ = v_isSharedCheck_5626_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5529_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5626_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5534_; 
lean_inc(v_a_5527_);
lean_inc_ref(v_a_5526_);
lean_inc(v_a_5525_);
lean_inc_ref(v_a_5524_);
v___x_5534_ = lean_whnf(v_a_5530_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_);
if (lean_obj_tag(v___x_5534_) == 0)
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5625_; 
v_a_5535_ = lean_ctor_get(v___x_5534_, 0);
v_isSharedCheck_5625_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5625_ == 0)
{
v___x_5537_ = v___x_5534_;
v_isShared_5538_ = v_isSharedCheck_5625_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5534_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5625_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___x_5558_; 
v___x_5558_ = l_Lean_Expr_getAppFn(v_a_5535_);
if (lean_obj_tag(v___x_5558_) == 4)
{
lean_object* v_declName_5559_; lean_object* v_us_5560_; lean_object* v___x_5561_; lean_object* v_env_5562_; lean_object* v___y_5564_; lean_object* v___y_5565_; lean_object* v___y_5566_; lean_object* v___y_5567_; uint8_t v___x_5606_; 
v_declName_5559_ = lean_ctor_get(v___x_5558_, 0);
lean_inc_n(v_declName_5559_, 2);
v_us_5560_ = lean_ctor_get(v___x_5558_, 1);
lean_inc(v_us_5560_);
lean_dec_ref_known(v___x_5558_, 2);
v___x_5561_ = lean_st_ref_get(v_a_5527_);
v_env_5562_ = lean_ctor_get(v___x_5561_, 0);
lean_inc_ref_n(v_env_5562_, 2);
lean_dec(v___x_5561_);
v___x_5606_ = l_Lean_isStructure(v_env_5562_, v_declName_5559_);
if (v___x_5606_ == 0)
{
lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
v___x_5607_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5608_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5535_);
lean_inc_ref(v_s_5522_);
v___x_5609_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5522_, v_a_5535_);
v___x_5610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5608_);
lean_ctor_set(v___x_5610_, 1, v___x_5609_);
v___x_5611_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5607_, v___x_5610_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_dec_ref_known(v___x_5611_, 1);
v___y_5564_ = v_a_5524_;
v___y_5565_ = v_a_5525_;
v___y_5566_ = v_a_5526_;
v___y_5567_ = v_a_5527_;
goto v___jp_5563_;
}
else
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5619_; 
lean_dec_ref(v_env_5562_);
lean_dec(v_us_5560_);
lean_dec(v_declName_5559_);
lean_del_object(v___x_5537_);
lean_dec(v_a_5535_);
lean_del_object(v___x_5532_);
lean_dec(v_fieldName_5523_);
lean_dec_ref(v_s_5522_);
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5614_ = v___x_5611_;
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5611_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5612_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
}
else
{
v___y_5564_ = v_a_5524_;
v___y_5565_ = v_a_5525_;
v___y_5566_ = v_a_5526_;
v___y_5567_ = v_a_5527_;
goto v___jp_5563_;
}
v___jp_5563_:
{
lean_object* v___x_5568_; 
lean_inc(v_fieldName_5523_);
lean_inc(v_declName_5559_);
lean_inc_ref(v_env_5562_);
v___x_5568_ = l_Lean_getProjFnForField_x3f(v_env_5562_, v_declName_5559_, v_fieldName_5523_);
if (lean_obj_tag(v___x_5568_) == 0)
{
lean_object* v___x_5569_; lean_object* v___x_5570_; size_t v_sz_5571_; size_t v___x_5572_; lean_object* v___x_5573_; 
lean_dec(v_us_5560_);
lean_del_object(v___x_5537_);
lean_inc(v_declName_5559_);
lean_inc_ref(v_env_5562_);
v___x_5569_ = l_Lean_getStructureFields(v_env_5562_, v_declName_5559_);
v___x_5570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5571_ = lean_array_size(v___x_5569_);
v___x_5572_ = ((size_t)0ULL);
lean_inc(v_fieldName_5523_);
lean_inc_ref(v_s_5522_);
v___x_5573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5562_, v_declName_5559_, v_s_5522_, v_fieldName_5523_, v___x_5569_, v_sz_5571_, v___x_5572_, v___x_5570_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_);
lean_dec_ref(v___x_5569_);
if (lean_obj_tag(v___x_5573_) == 0)
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5584_; 
v_a_5574_ = lean_ctor_get(v___x_5573_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5573_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5576_ = v___x_5573_;
v_isShared_5577_ = v_isSharedCheck_5584_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___x_5573_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5584_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v_fst_5578_; 
v_fst_5578_ = lean_ctor_get(v_a_5574_, 0);
lean_inc(v_fst_5578_);
lean_dec(v_a_5574_);
if (lean_obj_tag(v_fst_5578_) == 0)
{
lean_del_object(v___x_5576_);
v___y_5540_ = v___y_5564_;
v___y_5541_ = v___y_5567_;
v___y_5542_ = v___y_5566_;
v___y_5543_ = v___y_5565_;
goto v___jp_5539_;
}
else
{
lean_object* v_val_5579_; 
v_val_5579_ = lean_ctor_get(v_fst_5578_, 0);
lean_inc(v_val_5579_);
lean_dec_ref_known(v_fst_5578_, 1);
if (lean_obj_tag(v_val_5579_) == 0)
{
lean_del_object(v___x_5576_);
v___y_5540_ = v___y_5564_;
v___y_5541_ = v___y_5567_;
v___y_5542_ = v___y_5566_;
v___y_5543_ = v___y_5565_;
goto v___jp_5539_;
}
else
{
lean_object* v_val_5580_; lean_object* v___x_5582_; 
lean_dec(v_a_5535_);
lean_del_object(v___x_5532_);
lean_dec(v_fieldName_5523_);
lean_dec_ref(v_s_5522_);
v_val_5580_ = lean_ctor_get(v_val_5579_, 0);
lean_inc(v_val_5580_);
lean_dec_ref_known(v_val_5579_, 1);
if (v_isShared_5577_ == 0)
{
lean_ctor_set(v___x_5576_, 0, v_val_5580_);
v___x_5582_ = v___x_5576_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_val_5580_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
}
else
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
lean_dec(v_a_5535_);
lean_del_object(v___x_5532_);
lean_dec(v_fieldName_5523_);
lean_dec_ref(v_s_5522_);
v_a_5585_ = lean_ctor_get(v___x_5573_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5573_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5587_ = v___x_5573_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v___x_5573_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
else
{
lean_object* v_val_5593_; lean_object* v_dummy_5594_; lean_object* v_nargs_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5604_; 
lean_dec_ref(v_env_5562_);
lean_dec(v_declName_5559_);
lean_del_object(v___x_5532_);
lean_dec(v_fieldName_5523_);
v_val_5593_ = lean_ctor_get(v___x_5568_, 0);
lean_inc(v_val_5593_);
lean_dec_ref_known(v___x_5568_, 1);
v_dummy_5594_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5595_ = l_Lean_Expr_getAppNumArgs(v_a_5535_);
lean_inc(v_nargs_5595_);
v___x_5596_ = lean_mk_array(v_nargs_5595_, v_dummy_5594_);
v___x_5597_ = lean_unsigned_to_nat(1u);
v___x_5598_ = lean_nat_sub(v_nargs_5595_, v___x_5597_);
lean_dec(v_nargs_5595_);
v___x_5599_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5535_, v___x_5596_, v___x_5598_);
v___x_5600_ = l_Lean_mkConst(v_val_5593_, v_us_5560_);
v___x_5601_ = l_Lean_mkAppN(v___x_5600_, v___x_5599_);
lean_dec_ref(v___x_5599_);
v___x_5602_ = l_Lean_Expr_app___override(v___x_5601_, v_s_5522_);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 0, v___x_5602_);
v___x_5604_ = v___x_5537_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
}
else
{
lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
lean_dec_ref(v___x_5558_);
lean_del_object(v___x_5537_);
lean_del_object(v___x_5532_);
lean_dec(v_fieldName_5523_);
v___x_5620_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5621_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5622_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5522_, v_a_5535_);
v___x_5623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5621_);
lean_ctor_set(v___x_5623_, 1, v___x_5622_);
v___x_5624_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5620_, v___x_5623_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_);
return v___x_5624_;
}
v___jp_5539_:
{
lean_object* v___x_5544_; lean_object* v___x_5545_; uint8_t v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5549_; 
v___x_5544_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5545_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5546_ = 1;
v___x_5547_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5523_, v___x_5546_);
if (v_isShared_5533_ == 0)
{
lean_ctor_set_tag(v___x_5532_, 3);
lean_ctor_set(v___x_5532_, 0, v___x_5547_);
v___x_5549_ = v___x_5532_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5547_);
v___x_5549_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; 
v___x_5550_ = l_Lean_MessageData_ofFormat(v___x_5549_);
v___x_5551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5551_, 0, v___x_5545_);
lean_ctor_set(v___x_5551_, 1, v___x_5550_);
v___x_5552_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5553_, 0, v___x_5551_);
lean_ctor_set(v___x_5553_, 1, v___x_5552_);
v___x_5554_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5522_, v_a_5535_);
v___x_5555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5553_);
lean_ctor_set(v___x_5555_, 1, v___x_5554_);
v___x_5556_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5544_, v___x_5555_, v___y_5540_, v___y_5543_, v___y_5542_, v___y_5541_);
return v___x_5556_;
}
}
}
}
else
{
lean_del_object(v___x_5532_);
lean_dec(v_fieldName_5523_);
lean_dec_ref(v_s_5522_);
return v___x_5534_;
}
}
}
else
{
lean_dec(v_fieldName_5523_);
lean_dec_ref(v_s_5522_);
return v___x_5529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5627_, lean_object* v_declName_5628_, lean_object* v_s_5629_, lean_object* v_fieldName_5630_, lean_object* v_as_5631_, size_t v_sz_5632_, size_t v_i_5633_, lean_object* v_b_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v_a_5641_; uint8_t v___x_5645_; 
v___x_5645_ = lean_usize_dec_lt(v_i_5633_, v_sz_5632_);
if (v___x_5645_ == 0)
{
lean_object* v___x_5646_; 
lean_dec(v_fieldName_5630_);
lean_dec_ref(v_s_5629_);
lean_dec(v_declName_5628_);
lean_dec_ref(v___x_5627_);
v___x_5646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5646_, 0, v_b_5634_);
return v___x_5646_;
}
else
{
lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v_a_5649_; lean_object* v___x_5650_; 
lean_dec_ref(v_b_5634_);
v___x_5647_ = lean_box(0);
v___x_5648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5649_ = lean_array_uget_borrowed(v_as_5631_, v_i_5633_);
lean_inc(v_a_5649_);
lean_inc(v_declName_5628_);
lean_inc_ref(v___x_5627_);
v___x_5650_ = l_Lean_isSubobjectField_x3f(v___x_5627_, v_declName_5628_, v_a_5649_);
if (lean_obj_tag(v___x_5650_) == 0)
{
v_a_5641_ = v___x_5648_;
goto v___jp_5640_;
}
else
{
lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5709_; 
v_isSharedCheck_5709_ = !lean_is_exclusive(v___x_5650_);
if (v_isSharedCheck_5709_ == 0)
{
lean_object* v_unused_5710_; 
v_unused_5710_ = lean_ctor_get(v___x_5650_, 0);
lean_dec(v_unused_5710_);
v___x_5652_ = v___x_5650_;
v_isShared_5653_ = v_isSharedCheck_5709_;
goto v_resetjp_5651_;
}
else
{
lean_dec(v___x_5650_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5709_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___x_5654_; 
lean_inc(v_a_5649_);
lean_inc_ref(v_s_5629_);
v___x_5654_ = l_Lean_Meta_mkProjection(v_s_5629_, v_a_5649_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_);
if (lean_obj_tag(v___x_5654_) == 0)
{
lean_object* v_a_5655_; lean_object* v___x_5656_; 
v_a_5655_ = lean_ctor_get(v___x_5654_, 0);
lean_inc(v_a_5655_);
lean_dec_ref_known(v___x_5654_, 1);
v___x_5656_ = l_Lean_Meta_saveState___redArg(v___y_5636_, v___y_5638_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; lean_object* v___x_5658_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref_known(v___x_5656_, 1);
lean_inc(v_fieldName_5630_);
v___x_5658_ = l_Lean_Meta_mkProjection(v_a_5655_, v_fieldName_5630_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5671_; 
lean_dec(v_a_5657_);
lean_dec(v_fieldName_5630_);
lean_dec_ref(v_s_5629_);
lean_dec(v_declName_5628_);
lean_dec_ref(v___x_5627_);
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5661_ = v___x_5658_;
v_isShared_5662_ = v_isSharedCheck_5671_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5658_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5671_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5653_ == 0)
{
lean_ctor_set(v___x_5652_, 0, v_a_5659_);
v___x_5664_ = v___x_5652_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5659_);
v___x_5664_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5668_; 
v___x_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5664_);
v___x_5666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5665_);
lean_ctor_set(v___x_5666_, 1, v___x_5647_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 0, v___x_5666_);
v___x_5668_ = v___x_5661_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v___x_5666_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
}
else
{
lean_object* v_a_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5692_; 
lean_del_object(v___x_5652_);
v_a_5672_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5692_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5692_ == 0)
{
v___x_5674_ = v___x_5658_;
v_isShared_5675_ = v_isSharedCheck_5692_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_a_5672_);
lean_dec(v___x_5658_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5692_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
uint8_t v___y_5677_; uint8_t v___x_5690_; 
v___x_5690_ = l_Lean_Exception_isInterrupt(v_a_5672_);
if (v___x_5690_ == 0)
{
uint8_t v___x_5691_; 
lean_inc(v_a_5672_);
v___x_5691_ = l_Lean_Exception_isRuntime(v_a_5672_);
v___y_5677_ = v___x_5691_;
goto v___jp_5676_;
}
else
{
v___y_5677_ = v___x_5690_;
goto v___jp_5676_;
}
v___jp_5676_:
{
if (v___y_5677_ == 0)
{
lean_object* v___x_5678_; 
lean_del_object(v___x_5674_);
lean_dec(v_a_5672_);
v___x_5678_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5657_, v___y_5636_, v___y_5638_);
if (lean_obj_tag(v___x_5678_) == 0)
{
lean_dec_ref_known(v___x_5678_, 1);
v_a_5641_ = v___x_5648_;
goto v___jp_5640_;
}
else
{
lean_object* v_a_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5686_; 
lean_dec(v_fieldName_5630_);
lean_dec_ref(v_s_5629_);
lean_dec(v_declName_5628_);
lean_dec_ref(v___x_5627_);
v_a_5679_ = lean_ctor_get(v___x_5678_, 0);
v_isSharedCheck_5686_ = !lean_is_exclusive(v___x_5678_);
if (v_isSharedCheck_5686_ == 0)
{
v___x_5681_ = v___x_5678_;
v_isShared_5682_ = v_isSharedCheck_5686_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_a_5679_);
lean_dec(v___x_5678_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5686_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v___x_5684_; 
if (v_isShared_5682_ == 0)
{
v___x_5684_ = v___x_5681_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5685_; 
v_reuseFailAlloc_5685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_a_5679_);
v___x_5684_ = v_reuseFailAlloc_5685_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
return v___x_5684_;
}
}
}
}
else
{
lean_object* v___x_5688_; 
lean_dec(v_a_5657_);
lean_dec(v_fieldName_5630_);
lean_dec_ref(v_s_5629_);
lean_dec(v_declName_5628_);
lean_dec_ref(v___x_5627_);
if (v_isShared_5675_ == 0)
{
v___x_5688_ = v___x_5674_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5672_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
}
}
}
}
else
{
lean_object* v_a_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5700_; 
lean_dec(v_a_5655_);
lean_del_object(v___x_5652_);
lean_dec(v_fieldName_5630_);
lean_dec_ref(v_s_5629_);
lean_dec(v_declName_5628_);
lean_dec_ref(v___x_5627_);
v_a_5693_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5700_ == 0)
{
v___x_5695_ = v___x_5656_;
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_a_5693_);
lean_dec(v___x_5656_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v___x_5698_; 
if (v_isShared_5696_ == 0)
{
v___x_5698_ = v___x_5695_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_a_5693_);
v___x_5698_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
return v___x_5698_;
}
}
}
}
else
{
lean_object* v_a_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5708_; 
lean_del_object(v___x_5652_);
lean_dec(v_fieldName_5630_);
lean_dec_ref(v_s_5629_);
lean_dec(v_declName_5628_);
lean_dec_ref(v___x_5627_);
v_a_5701_ = lean_ctor_get(v___x_5654_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5654_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5703_ = v___x_5654_;
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_a_5701_);
lean_dec(v___x_5654_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5706_; 
if (v_isShared_5704_ == 0)
{
v___x_5706_ = v___x_5703_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v_a_5701_);
v___x_5706_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
return v___x_5706_;
}
}
}
}
}
}
v___jp_5640_:
{
size_t v___x_5642_; size_t v___x_5643_; 
v___x_5642_ = ((size_t)1ULL);
v___x_5643_ = lean_usize_add(v_i_5633_, v___x_5642_);
lean_inc_ref(v_a_5641_);
v_i_5633_ = v___x_5643_;
v_b_5634_ = v_a_5641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5711_, lean_object* v_declName_5712_, lean_object* v_s_5713_, lean_object* v_fieldName_5714_, lean_object* v_as_5715_, lean_object* v_sz_5716_, lean_object* v_i_5717_, lean_object* v_b_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_){
_start:
{
size_t v_sz_boxed_5724_; size_t v_i_boxed_5725_; lean_object* v_res_5726_; 
v_sz_boxed_5724_ = lean_unbox_usize(v_sz_5716_);
lean_dec(v_sz_5716_);
v_i_boxed_5725_ = lean_unbox_usize(v_i_5717_);
lean_dec(v_i_5717_);
v_res_5726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5711_, v_declName_5712_, v_s_5713_, v_fieldName_5714_, v_as_5715_, v_sz_boxed_5724_, v_i_boxed_5725_, v_b_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec_ref(v_as_5715_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5727_, lean_object* v_fieldName_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l_Lean_Meta_mkProjection(v_s_5727_, v_fieldName_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_);
lean_dec(v_a_5732_);
lean_dec_ref(v_a_5731_);
lean_dec(v_a_5730_);
lean_dec_ref(v_a_5729_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5735_, lean_object* v_cons_5736_, lean_object* v_x_5737_){
_start:
{
if (lean_obj_tag(v_x_5737_) == 0)
{
lean_dec_ref(v_cons_5736_);
lean_inc_ref(v_nil_5735_);
return v_nil_5735_;
}
else
{
lean_object* v_head_5738_; lean_object* v_tail_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; 
v_head_5738_ = lean_ctor_get(v_x_5737_, 0);
lean_inc(v_head_5738_);
v_tail_5739_ = lean_ctor_get(v_x_5737_, 1);
lean_inc(v_tail_5739_);
lean_dec_ref_known(v_x_5737_, 2);
lean_inc_ref(v_cons_5736_);
v___x_5740_ = l_Lean_Expr_app___override(v_cons_5736_, v_head_5738_);
v___x_5741_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5735_, v_cons_5736_, v_tail_5739_);
v___x_5742_ = l_Lean_Expr_app___override(v___x_5740_, v___x_5741_);
return v___x_5742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5743_, lean_object* v_cons_5744_, lean_object* v_x_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5743_, v_cons_5744_, v_x_5745_);
lean_dec_ref(v_nil_5743_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5756_, lean_object* v_xs_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_){
_start:
{
lean_object* v___x_5763_; 
lean_inc_ref(v_type_5756_);
v___x_5763_ = l_Lean_Meta_getDecLevel(v_type_5756_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_);
if (lean_obj_tag(v___x_5763_) == 0)
{
lean_object* v_a_5764_; lean_object* v___x_5766_; uint8_t v_isShared_5767_; uint8_t v_isSharedCheck_5783_; 
v_a_5764_ = lean_ctor_get(v___x_5763_, 0);
v_isSharedCheck_5783_ = !lean_is_exclusive(v___x_5763_);
if (v_isSharedCheck_5783_ == 0)
{
v___x_5766_ = v___x_5763_;
v_isShared_5767_ = v_isSharedCheck_5783_;
goto v_resetjp_5765_;
}
else
{
lean_inc(v_a_5764_);
lean_dec(v___x_5763_);
v___x_5766_ = lean_box(0);
v_isShared_5767_ = v_isSharedCheck_5783_;
goto v_resetjp_5765_;
}
v_resetjp_5765_:
{
lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; 
v___x_5768_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5769_ = lean_box(0);
v___x_5770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5770_, 0, v_a_5764_);
lean_ctor_set(v___x_5770_, 1, v___x_5769_);
lean_inc_ref(v___x_5770_);
v___x_5771_ = l_Lean_mkConst(v___x_5768_, v___x_5770_);
lean_inc_ref(v_type_5756_);
v___x_5772_ = l_Lean_Expr_app___override(v___x_5771_, v_type_5756_);
if (lean_obj_tag(v_xs_5757_) == 0)
{
lean_object* v___x_5774_; 
lean_dec_ref_known(v___x_5770_, 2);
lean_dec_ref(v_type_5756_);
if (v_isShared_5767_ == 0)
{
lean_ctor_set(v___x_5766_, 0, v___x_5772_);
v___x_5774_ = v___x_5766_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
else
{
lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5781_; 
v___x_5776_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5777_ = l_Lean_mkConst(v___x_5776_, v___x_5770_);
v___x_5778_ = l_Lean_Expr_app___override(v___x_5777_, v_type_5756_);
v___x_5779_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5772_, v___x_5778_, v_xs_5757_);
lean_dec_ref(v___x_5772_);
if (v_isShared_5767_ == 0)
{
lean_ctor_set(v___x_5766_, 0, v___x_5779_);
v___x_5781_ = v___x_5766_;
goto v_reusejp_5780_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5779_);
v___x_5781_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5780_;
}
v_reusejp_5780_:
{
return v___x_5781_;
}
}
}
}
else
{
lean_object* v_a_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5791_; 
lean_dec(v_xs_5757_);
lean_dec_ref(v_type_5756_);
v_a_5784_ = lean_ctor_get(v___x_5763_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v___x_5763_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5786_ = v___x_5763_;
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_a_5784_);
lean_dec(v___x_5763_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5789_; 
if (v_isShared_5787_ == 0)
{
v___x_5789_ = v___x_5786_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5792_, lean_object* v_xs_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_){
_start:
{
lean_object* v_res_5799_; 
v_res_5799_ = l_Lean_Meta_mkListLit(v_type_5792_, v_xs_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_);
lean_dec(v_a_5797_);
lean_dec_ref(v_a_5796_);
lean_dec(v_a_5795_);
lean_dec_ref(v_a_5794_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5804_, lean_object* v_xs_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_){
_start:
{
lean_object* v___x_5811_; 
lean_inc_ref(v_type_5804_);
v___x_5811_ = l_Lean_Meta_getDecLevel(v_type_5804_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_);
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5812_; lean_object* v___x_5813_; 
v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
lean_inc(v_a_5812_);
lean_dec_ref_known(v___x_5811_, 1);
lean_inc_ref(v_type_5804_);
v___x_5813_ = l_Lean_Meta_mkListLit(v_type_5804_, v_xs_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_5827_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5827_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5827_ == 0)
{
v___x_5816_ = v___x_5813_;
v_isShared_5817_ = v_isSharedCheck_5827_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_a_5814_);
lean_dec(v___x_5813_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_5827_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5825_; 
v___x_5818_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5819_ = lean_box(0);
v___x_5820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5820_, 0, v_a_5812_);
lean_ctor_set(v___x_5820_, 1, v___x_5819_);
v___x_5821_ = l_Lean_mkConst(v___x_5818_, v___x_5820_);
v___x_5822_ = l_Lean_Expr_app___override(v___x_5821_, v_type_5804_);
v___x_5823_ = l_Lean_Expr_app___override(v___x_5822_, v_a_5814_);
if (v_isShared_5817_ == 0)
{
lean_ctor_set(v___x_5816_, 0, v___x_5823_);
v___x_5825_ = v___x_5816_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v___x_5823_);
v___x_5825_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
return v___x_5825_;
}
}
}
else
{
lean_dec(v_a_5812_);
lean_dec_ref(v_type_5804_);
return v___x_5813_;
}
}
else
{
lean_object* v_a_5828_; lean_object* v___x_5830_; uint8_t v_isShared_5831_; uint8_t v_isSharedCheck_5835_; 
lean_dec(v_xs_5805_);
lean_dec_ref(v_type_5804_);
v_a_5828_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5835_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5835_ == 0)
{
v___x_5830_ = v___x_5811_;
v_isShared_5831_ = v_isSharedCheck_5835_;
goto v_resetjp_5829_;
}
else
{
lean_inc(v_a_5828_);
lean_dec(v___x_5811_);
v___x_5830_ = lean_box(0);
v_isShared_5831_ = v_isSharedCheck_5835_;
goto v_resetjp_5829_;
}
v_resetjp_5829_:
{
lean_object* v___x_5833_; 
if (v_isShared_5831_ == 0)
{
v___x_5833_ = v___x_5830_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5828_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5836_, lean_object* v_xs_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_){
_start:
{
lean_object* v_res_5843_; 
v_res_5843_ = l_Lean_Meta_mkArrayLit(v_type_5836_, v_xs_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_);
lean_dec(v_a_5841_);
lean_dec_ref(v_a_5840_);
lean_dec(v_a_5839_);
lean_dec_ref(v_a_5838_);
return v_res_5843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_){
_start:
{
lean_object* v___x_5855_; 
lean_inc_ref(v_type_5849_);
v___x_5855_ = l_Lean_Meta_getDecLevel(v_type_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_);
if (lean_obj_tag(v___x_5855_) == 0)
{
lean_object* v_a_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5868_; 
v_a_5856_ = lean_ctor_get(v___x_5855_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5855_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5858_ = v___x_5855_;
v_isShared_5859_ = v_isSharedCheck_5868_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_a_5856_);
lean_dec(v___x_5855_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5868_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5866_; 
v___x_5860_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5861_ = lean_box(0);
v___x_5862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5862_, 0, v_a_5856_);
lean_ctor_set(v___x_5862_, 1, v___x_5861_);
v___x_5863_ = l_Lean_mkConst(v___x_5860_, v___x_5862_);
v___x_5864_ = l_Lean_Expr_app___override(v___x_5863_, v_type_5849_);
if (v_isShared_5859_ == 0)
{
lean_ctor_set(v___x_5858_, 0, v___x_5864_);
v___x_5866_ = v___x_5858_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v___x_5864_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
else
{
lean_object* v_a_5869_; lean_object* v___x_5871_; uint8_t v_isShared_5872_; uint8_t v_isSharedCheck_5876_; 
lean_dec_ref(v_type_5849_);
v_a_5869_ = lean_ctor_get(v___x_5855_, 0);
v_isSharedCheck_5876_ = !lean_is_exclusive(v___x_5855_);
if (v_isSharedCheck_5876_ == 0)
{
v___x_5871_ = v___x_5855_;
v_isShared_5872_ = v_isSharedCheck_5876_;
goto v_resetjp_5870_;
}
else
{
lean_inc(v_a_5869_);
lean_dec(v___x_5855_);
v___x_5871_ = lean_box(0);
v_isShared_5872_ = v_isSharedCheck_5876_;
goto v_resetjp_5870_;
}
v_resetjp_5870_:
{
lean_object* v___x_5874_; 
if (v_isShared_5872_ == 0)
{
v___x_5874_ = v___x_5871_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_a_5869_);
v___x_5874_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
return v___x_5874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_){
_start:
{
lean_object* v_res_5883_; 
v_res_5883_ = l_Lean_Meta_mkNone(v_type_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
lean_dec(v_a_5881_);
lean_dec_ref(v_a_5880_);
lean_dec(v_a_5879_);
lean_dec_ref(v_a_5878_);
return v_res_5883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5888_, lean_object* v_value_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_, lean_object* v_a_5892_, lean_object* v_a_5893_){
_start:
{
lean_object* v___x_5895_; 
lean_inc_ref(v_type_5888_);
v___x_5895_ = l_Lean_Meta_getDecLevel(v_type_5888_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
if (lean_obj_tag(v___x_5895_) == 0)
{
lean_object* v_a_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5908_; 
v_a_5896_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5908_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5908_ == 0)
{
v___x_5898_ = v___x_5895_;
v_isShared_5899_ = v_isSharedCheck_5908_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_a_5896_);
lean_dec(v___x_5895_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5908_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5906_; 
v___x_5900_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5901_ = lean_box(0);
v___x_5902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5902_, 0, v_a_5896_);
lean_ctor_set(v___x_5902_, 1, v___x_5901_);
v___x_5903_ = l_Lean_mkConst(v___x_5900_, v___x_5902_);
v___x_5904_ = l_Lean_mkAppB(v___x_5903_, v_type_5888_, v_value_5889_);
if (v_isShared_5899_ == 0)
{
lean_ctor_set(v___x_5898_, 0, v___x_5904_);
v___x_5906_ = v___x_5898_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5907_; 
v_reuseFailAlloc_5907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5907_, 0, v___x_5904_);
v___x_5906_ = v_reuseFailAlloc_5907_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
return v___x_5906_;
}
}
}
else
{
lean_object* v_a_5909_; lean_object* v___x_5911_; uint8_t v_isShared_5912_; uint8_t v_isSharedCheck_5916_; 
lean_dec_ref(v_value_5889_);
lean_dec_ref(v_type_5888_);
v_a_5909_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5916_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5916_ == 0)
{
v___x_5911_ = v___x_5895_;
v_isShared_5912_ = v_isSharedCheck_5916_;
goto v_resetjp_5910_;
}
else
{
lean_inc(v_a_5909_);
lean_dec(v___x_5895_);
v___x_5911_ = lean_box(0);
v_isShared_5912_ = v_isSharedCheck_5916_;
goto v_resetjp_5910_;
}
v_resetjp_5910_:
{
lean_object* v___x_5914_; 
if (v_isShared_5912_ == 0)
{
v___x_5914_ = v___x_5911_;
goto v_reusejp_5913_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_a_5909_);
v___x_5914_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5913_;
}
v_reusejp_5913_:
{
return v___x_5914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5917_, lean_object* v_value_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_){
_start:
{
lean_object* v_res_5924_; 
v_res_5924_ = l_Lean_Meta_mkSome(v_type_5917_, v_value_5918_, v_a_5919_, v_a_5920_, v_a_5921_, v_a_5922_);
lean_dec(v_a_5922_);
lean_dec_ref(v_a_5921_);
lean_dec(v_a_5920_);
lean_dec_ref(v_a_5919_);
return v_res_5924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_){
_start:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; 
v___x_5936_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5937_, 0, v_p_5930_);
v___x_5938_ = lean_box(0);
v___x_5939_ = lean_unsigned_to_nat(2u);
v___x_5940_ = lean_mk_empty_array_with_capacity(v___x_5939_);
v___x_5941_ = lean_array_push(v___x_5940_, v___x_5937_);
v___x_5942_ = lean_array_push(v___x_5941_, v___x_5938_);
v___x_5943_ = l_Lean_Meta_mkAppOptM(v___x_5936_, v___x_5942_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_);
return v___x_5943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_){
_start:
{
lean_object* v_res_5950_; 
v_res_5950_ = l_Lean_Meta_mkDecide(v_p_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_);
lean_dec(v_a_5948_);
lean_dec_ref(v_a_5947_);
lean_dec(v_a_5946_);
lean_dec_ref(v_a_5945_);
return v_res_5950_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5956_ = lean_box(0);
v___x_5957_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5958_ = l_Lean_mkConst(v___x_5957_, v___x_5956_);
return v___x_5958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_){
_start:
{
lean_object* v___x_5968_; 
v___x_5968_ = l_Lean_Meta_mkDecide(v_p_5962_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_);
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_object* v_a_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; 
v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
lean_inc(v_a_5969_);
lean_dec_ref_known(v___x_5968_, 1);
v___x_5970_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5971_ = l_Lean_Meta_mkEq(v_a_5969_, v___x_5970_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_);
if (lean_obj_tag(v___x_5971_) == 0)
{
lean_object* v_a_5972_; lean_object* v___x_5973_; 
v_a_5972_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5972_);
lean_dec_ref_known(v___x_5971_, 1);
v___x_5973_ = l_Lean_Meta_mkEqRefl(v___x_5970_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_);
if (lean_obj_tag(v___x_5973_) == 0)
{
lean_object* v_a_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; 
v_a_5974_ = lean_ctor_get(v___x_5973_, 0);
lean_inc(v_a_5974_);
lean_dec_ref_known(v___x_5973_, 1);
v___x_5975_ = l_Lean_Meta_mkExpectedPropHint(v_a_5974_, v_a_5972_);
v___x_5976_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5977_ = lean_unsigned_to_nat(1u);
v___x_5978_ = lean_mk_empty_array_with_capacity(v___x_5977_);
v___x_5979_ = lean_array_push(v___x_5978_, v___x_5975_);
v___x_5980_ = l_Lean_Meta_mkAppM(v___x_5976_, v___x_5979_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_);
return v___x_5980_;
}
else
{
lean_dec(v_a_5972_);
return v___x_5973_;
}
}
else
{
return v___x_5971_;
}
}
else
{
return v___x_5968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_){
_start:
{
lean_object* v_res_5987_; 
v_res_5987_ = l_Lean_Meta_mkDecideProof(v_p_5981_, v_a_5982_, v_a_5983_, v_a_5984_, v_a_5985_);
lean_dec(v_a_5985_);
lean_dec_ref(v_a_5984_);
lean_dec(v_a_5983_);
lean_dec_ref(v_a_5982_);
return v_res_5987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5993_, lean_object* v_b_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_){
_start:
{
lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_6000_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6001_ = lean_unsigned_to_nat(2u);
v___x_6002_ = lean_mk_empty_array_with_capacity(v___x_6001_);
v___x_6003_ = lean_array_push(v___x_6002_, v_a_5993_);
v___x_6004_ = lean_array_push(v___x_6003_, v_b_5994_);
v___x_6005_ = l_Lean_Meta_mkAppM(v___x_6000_, v___x_6004_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_);
return v___x_6005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_6006_, lean_object* v_b_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_){
_start:
{
lean_object* v_res_6013_; 
v_res_6013_ = l_Lean_Meta_mkLt(v_a_6006_, v_b_6007_, v_a_6008_, v_a_6009_, v_a_6010_, v_a_6011_);
lean_dec(v_a_6011_);
lean_dec_ref(v_a_6010_);
lean_dec(v_a_6009_);
lean_dec_ref(v_a_6008_);
return v_res_6013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_6019_, lean_object* v_b_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_){
_start:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; 
v___x_6026_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6027_ = lean_unsigned_to_nat(2u);
v___x_6028_ = lean_mk_empty_array_with_capacity(v___x_6027_);
v___x_6029_ = lean_array_push(v___x_6028_, v_a_6019_);
v___x_6030_ = lean_array_push(v___x_6029_, v_b_6020_);
v___x_6031_ = l_Lean_Meta_mkAppM(v___x_6026_, v___x_6030_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_);
return v___x_6031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_6032_, lean_object* v_b_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_, lean_object* v_a_6036_, lean_object* v_a_6037_, lean_object* v_a_6038_){
_start:
{
lean_object* v_res_6039_; 
v_res_6039_ = l_Lean_Meta_mkLe(v_a_6032_, v_b_6033_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_);
lean_dec(v_a_6037_);
lean_dec_ref(v_a_6036_);
lean_dec(v_a_6035_);
lean_dec_ref(v_a_6034_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_6045_, lean_object* v_a_6046_, lean_object* v_a_6047_, lean_object* v_a_6048_, lean_object* v_a_6049_){
_start:
{
lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; 
v___x_6051_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_6052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6052_, 0, v_00_u03b1_6045_);
v___x_6053_ = lean_box(0);
v___x_6054_ = lean_unsigned_to_nat(2u);
v___x_6055_ = lean_mk_empty_array_with_capacity(v___x_6054_);
v___x_6056_ = lean_array_push(v___x_6055_, v___x_6052_);
v___x_6057_ = lean_array_push(v___x_6056_, v___x_6053_);
v___x_6058_ = l_Lean_Meta_mkAppOptM(v___x_6051_, v___x_6057_, v_a_6046_, v_a_6047_, v_a_6048_, v_a_6049_);
return v___x_6058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_){
_start:
{
lean_object* v_res_6065_; 
v_res_6065_ = l_Lean_Meta_mkDefault(v_00_u03b1_6059_, v_a_6060_, v_a_6061_, v_a_6062_, v_a_6063_);
lean_dec(v_a_6063_);
lean_dec_ref(v_a_6062_);
lean_dec(v_a_6061_);
lean_dec_ref(v_a_6060_);
return v_res_6065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_6071_, lean_object* v_a_6072_, lean_object* v_a_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_){
_start:
{
lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; 
v___x_6077_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_6078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6078_, 0, v_00_u03b1_6071_);
v___x_6079_ = lean_box(0);
v___x_6080_ = lean_unsigned_to_nat(2u);
v___x_6081_ = lean_mk_empty_array_with_capacity(v___x_6080_);
v___x_6082_ = lean_array_push(v___x_6081_, v___x_6078_);
v___x_6083_ = lean_array_push(v___x_6082_, v___x_6079_);
v___x_6084_ = l_Lean_Meta_mkAppOptM(v___x_6077_, v___x_6083_, v_a_6072_, v_a_6073_, v_a_6074_, v_a_6075_);
return v___x_6084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_, lean_object* v_a_6090_){
_start:
{
lean_object* v_res_6091_; 
v_res_6091_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6085_, v_a_6086_, v_a_6087_, v_a_6088_, v_a_6089_);
lean_dec(v_a_6089_);
lean_dec_ref(v_a_6088_);
lean_dec(v_a_6087_);
lean_dec_ref(v_a_6086_);
return v_res_6091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6095_, lean_object* v_a_6096_, lean_object* v_a_6097_, lean_object* v_a_6098_, lean_object* v_a_6099_){
_start:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6101_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6102_ = lean_unsigned_to_nat(1u);
v___x_6103_ = lean_mk_empty_array_with_capacity(v___x_6102_);
v___x_6104_ = lean_array_push(v___x_6103_, v_h_6095_);
v___x_6105_ = l_Lean_Meta_mkAppM(v___x_6101_, v___x_6104_, v_a_6096_, v_a_6097_, v_a_6098_, v_a_6099_);
return v___x_6105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6106_, lean_object* v_a_6107_, lean_object* v_a_6108_, lean_object* v_a_6109_, lean_object* v_a_6110_, lean_object* v_a_6111_){
_start:
{
lean_object* v_res_6112_; 
v_res_6112_ = l_Lean_Meta_mkFunExt(v_h_6106_, v_a_6107_, v_a_6108_, v_a_6109_, v_a_6110_);
lean_dec(v_a_6110_);
lean_dec_ref(v_a_6109_);
lean_dec(v_a_6108_);
lean_dec_ref(v_a_6107_);
return v_res_6112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6116_, lean_object* v_a_6117_, lean_object* v_a_6118_, lean_object* v_a_6119_, lean_object* v_a_6120_){
_start:
{
lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; 
v___x_6122_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6123_ = lean_unsigned_to_nat(1u);
v___x_6124_ = lean_mk_empty_array_with_capacity(v___x_6123_);
v___x_6125_ = lean_array_push(v___x_6124_, v_h_6116_);
v___x_6126_ = l_Lean_Meta_mkAppM(v___x_6122_, v___x_6125_, v_a_6117_, v_a_6118_, v_a_6119_, v_a_6120_);
return v___x_6126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6127_, lean_object* v_a_6128_, lean_object* v_a_6129_, lean_object* v_a_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_){
_start:
{
lean_object* v_res_6133_; 
v_res_6133_ = l_Lean_Meta_mkPropExt(v_h_6127_, v_a_6128_, v_a_6129_, v_a_6130_, v_a_6131_);
lean_dec(v_a_6131_);
lean_dec_ref(v_a_6130_);
lean_dec(v_a_6129_);
lean_dec_ref(v_a_6128_);
return v_res_6133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6137_, lean_object* v_h_u2082_6138_, lean_object* v_a_6139_, lean_object* v_a_6140_, lean_object* v_a_6141_, lean_object* v_a_6142_){
_start:
{
lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; 
v___x_6144_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6145_ = lean_unsigned_to_nat(2u);
v___x_6146_ = lean_mk_empty_array_with_capacity(v___x_6145_);
v___x_6147_ = lean_array_push(v___x_6146_, v_h_u2081_6137_);
v___x_6148_ = lean_array_push(v___x_6147_, v_h_u2082_6138_);
v___x_6149_ = l_Lean_Meta_mkAppM(v___x_6144_, v___x_6148_, v_a_6139_, v_a_6140_, v_a_6141_, v_a_6142_);
return v___x_6149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6150_, lean_object* v_h_u2082_6151_, lean_object* v_a_6152_, lean_object* v_a_6153_, lean_object* v_a_6154_, lean_object* v_a_6155_, lean_object* v_a_6156_){
_start:
{
lean_object* v_res_6157_; 
v_res_6157_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6150_, v_h_u2082_6151_, v_a_6152_, v_a_6153_, v_a_6154_, v_a_6155_);
lean_dec(v_a_6155_);
lean_dec_ref(v_a_6154_);
lean_dec(v_a_6153_);
lean_dec_ref(v_a_6152_);
return v_res_6157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6161_, lean_object* v_h_6162_, lean_object* v_a_6163_, lean_object* v_a_6164_, lean_object* v_a_6165_, lean_object* v_a_6166_){
_start:
{
lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6168_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6169_ = lean_unsigned_to_nat(2u);
v___x_6170_ = lean_mk_empty_array_with_capacity(v___x_6169_);
v___x_6171_ = lean_array_push(v___x_6170_, v_b_6161_);
v___x_6172_ = lean_array_push(v___x_6171_, v_h_6162_);
v___x_6173_ = l_Lean_Meta_mkAppM(v___x_6168_, v___x_6172_, v_a_6163_, v_a_6164_, v_a_6165_, v_a_6166_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6174_, lean_object* v_h_6175_, lean_object* v_a_6176_, lean_object* v_a_6177_, lean_object* v_a_6178_, lean_object* v_a_6179_, lean_object* v_a_6180_){
_start:
{
lean_object* v_res_6181_; 
v_res_6181_ = l_Lean_Meta_mkLetValCongr(v_b_6174_, v_h_6175_, v_a_6176_, v_a_6177_, v_a_6178_, v_a_6179_);
lean_dec(v_a_6179_);
lean_dec_ref(v_a_6178_);
lean_dec(v_a_6177_);
lean_dec_ref(v_a_6176_);
return v_res_6181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6185_, lean_object* v_h_6186_, lean_object* v_a_6187_, lean_object* v_a_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; 
v___x_6192_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6193_ = lean_unsigned_to_nat(2u);
v___x_6194_ = lean_mk_empty_array_with_capacity(v___x_6193_);
v___x_6195_ = lean_array_push(v___x_6194_, v_a_6185_);
v___x_6196_ = lean_array_push(v___x_6195_, v_h_6186_);
v___x_6197_ = l_Lean_Meta_mkAppM(v___x_6192_, v___x_6196_, v_a_6187_, v_a_6188_, v_a_6189_, v_a_6190_);
return v___x_6197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6198_, lean_object* v_h_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_, lean_object* v_a_6202_, lean_object* v_a_6203_, lean_object* v_a_6204_){
_start:
{
lean_object* v_res_6205_; 
v_res_6205_ = l_Lean_Meta_mkLetBodyCongr(v_a_6198_, v_h_6199_, v_a_6200_, v_a_6201_, v_a_6202_, v_a_6203_);
lean_dec(v_a_6203_);
lean_dec_ref(v_a_6202_);
lean_dec(v_a_6201_);
lean_dec_ref(v_a_6200_);
return v_res_6205_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; 
v___x_6209_ = lean_box(0);
v___x_6210_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6211_ = l_Lean_mkConst(v___x_6210_, v___x_6209_);
return v___x_6211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6215_, lean_object* v_h_6216_){
_start:
{
lean_object* v___x_6220_; uint8_t v___x_6221_; 
lean_inc_ref(v_h_6216_);
v___x_6220_ = l_Lean_Expr_cleanupAnnotations(v_h_6216_);
v___x_6221_ = l_Lean_Expr_isApp(v___x_6220_);
if (v___x_6221_ == 0)
{
lean_dec_ref(v___x_6220_);
goto v___jp_6217_;
}
else
{
lean_object* v_arg_6222_; lean_object* v___x_6223_; uint8_t v___x_6224_; 
v_arg_6222_ = lean_ctor_get(v___x_6220_, 1);
lean_inc_ref(v_arg_6222_);
v___x_6223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6220_);
v___x_6224_ = l_Lean_Expr_isApp(v___x_6223_);
if (v___x_6224_ == 0)
{
lean_dec_ref(v___x_6223_);
lean_dec_ref(v_arg_6222_);
goto v___jp_6217_;
}
else
{
lean_object* v___x_6225_; lean_object* v___x_6226_; uint8_t v___x_6227_; 
v___x_6225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6223_);
v___x_6226_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6227_ = l_Lean_Expr_isConstOf(v___x_6225_, v___x_6226_);
lean_dec_ref(v___x_6225_);
if (v___x_6227_ == 0)
{
lean_dec_ref(v_arg_6222_);
goto v___jp_6217_;
}
else
{
lean_dec_ref(v_h_6216_);
lean_dec_ref(v_p_6215_);
return v_arg_6222_;
}
}
}
v___jp_6217_:
{
lean_object* v___x_6218_; lean_object* v___x_6219_; 
v___x_6218_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6219_ = l_Lean_mkAppB(v___x_6218_, v_p_6215_, v_h_6216_);
return v___x_6219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6228_, lean_object* v_a_6229_, lean_object* v_a_6230_, lean_object* v_a_6231_, lean_object* v_a_6232_){
_start:
{
lean_object* v___y_6235_; lean_object* v___y_6236_; lean_object* v___y_6237_; lean_object* v___y_6238_; lean_object* v___x_6244_; 
lean_inc_ref(v_h_6228_);
v___x_6244_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6228_, v_a_6230_);
if (lean_obj_tag(v___x_6244_) == 0)
{
lean_object* v_a_6245_; lean_object* v___x_6247_; uint8_t v_isShared_6248_; uint8_t v_isSharedCheck_6260_; 
v_a_6245_ = lean_ctor_get(v___x_6244_, 0);
v_isSharedCheck_6260_ = !lean_is_exclusive(v___x_6244_);
if (v_isSharedCheck_6260_ == 0)
{
v___x_6247_ = v___x_6244_;
v_isShared_6248_ = v_isSharedCheck_6260_;
goto v_resetjp_6246_;
}
else
{
lean_inc(v_a_6245_);
lean_dec(v___x_6244_);
v___x_6247_ = lean_box(0);
v_isShared_6248_ = v_isSharedCheck_6260_;
goto v_resetjp_6246_;
}
v_resetjp_6246_:
{
lean_object* v___x_6249_; uint8_t v___x_6250_; 
v___x_6249_ = l_Lean_Expr_cleanupAnnotations(v_a_6245_);
v___x_6250_ = l_Lean_Expr_isApp(v___x_6249_);
if (v___x_6250_ == 0)
{
lean_dec_ref(v___x_6249_);
lean_del_object(v___x_6247_);
v___y_6235_ = v_a_6229_;
v___y_6236_ = v_a_6230_;
v___y_6237_ = v_a_6231_;
v___y_6238_ = v_a_6232_;
goto v___jp_6234_;
}
else
{
lean_object* v_arg_6251_; lean_object* v___x_6252_; uint8_t v___x_6253_; 
v_arg_6251_ = lean_ctor_get(v___x_6249_, 1);
lean_inc_ref(v_arg_6251_);
v___x_6252_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6249_);
v___x_6253_ = l_Lean_Expr_isApp(v___x_6252_);
if (v___x_6253_ == 0)
{
lean_dec_ref(v___x_6252_);
lean_dec_ref(v_arg_6251_);
lean_del_object(v___x_6247_);
v___y_6235_ = v_a_6229_;
v___y_6236_ = v_a_6230_;
v___y_6237_ = v_a_6231_;
v___y_6238_ = v_a_6232_;
goto v___jp_6234_;
}
else
{
lean_object* v___x_6254_; lean_object* v___x_6255_; uint8_t v___x_6256_; 
v___x_6254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6252_);
v___x_6255_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6256_ = l_Lean_Expr_isConstOf(v___x_6254_, v___x_6255_);
lean_dec_ref(v___x_6254_);
if (v___x_6256_ == 0)
{
lean_dec_ref(v_arg_6251_);
lean_del_object(v___x_6247_);
v___y_6235_ = v_a_6229_;
v___y_6236_ = v_a_6230_;
v___y_6237_ = v_a_6231_;
v___y_6238_ = v_a_6232_;
goto v___jp_6234_;
}
else
{
lean_object* v___x_6258_; 
lean_dec_ref(v_h_6228_);
if (v_isShared_6248_ == 0)
{
lean_ctor_set(v___x_6247_, 0, v_arg_6251_);
v___x_6258_ = v___x_6247_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6259_; 
v_reuseFailAlloc_6259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6259_, 0, v_arg_6251_);
v___x_6258_ = v_reuseFailAlloc_6259_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
return v___x_6258_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6228_);
return v___x_6244_;
}
v___jp_6234_:
{
lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; 
v___x_6239_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6240_ = lean_unsigned_to_nat(1u);
v___x_6241_ = lean_mk_empty_array_with_capacity(v___x_6240_);
v___x_6242_ = lean_array_push(v___x_6241_, v_h_6228_);
v___x_6243_ = l_Lean_Meta_mkAppM(v___x_6239_, v___x_6242_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
return v___x_6243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6261_, lean_object* v_a_6262_, lean_object* v_a_6263_, lean_object* v_a_6264_, lean_object* v_a_6265_, lean_object* v_a_6266_){
_start:
{
lean_object* v_res_6267_; 
v_res_6267_ = l_Lean_Meta_mkOfEqFalse(v_h_6261_, v_a_6262_, v_a_6263_, v_a_6264_, v_a_6265_);
lean_dec(v_a_6265_);
lean_dec_ref(v_a_6264_);
lean_dec(v_a_6263_);
lean_dec_ref(v_a_6262_);
return v_res_6267_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6271_ = lean_box(0);
v___x_6272_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6273_ = l_Lean_mkConst(v___x_6272_, v___x_6271_);
return v___x_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6277_, lean_object* v_h_6278_){
_start:
{
lean_object* v___x_6282_; uint8_t v___x_6283_; 
lean_inc_ref(v_h_6278_);
v___x_6282_ = l_Lean_Expr_cleanupAnnotations(v_h_6278_);
v___x_6283_ = l_Lean_Expr_isApp(v___x_6282_);
if (v___x_6283_ == 0)
{
lean_dec_ref(v___x_6282_);
goto v___jp_6279_;
}
else
{
lean_object* v_arg_6284_; lean_object* v___x_6285_; uint8_t v___x_6286_; 
v_arg_6284_ = lean_ctor_get(v___x_6282_, 1);
lean_inc_ref(v_arg_6284_);
v___x_6285_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6282_);
v___x_6286_ = l_Lean_Expr_isApp(v___x_6285_);
if (v___x_6286_ == 0)
{
lean_dec_ref(v___x_6285_);
lean_dec_ref(v_arg_6284_);
goto v___jp_6279_;
}
else
{
lean_object* v___x_6287_; lean_object* v___x_6288_; uint8_t v___x_6289_; 
v___x_6287_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6285_);
v___x_6288_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6289_ = l_Lean_Expr_isConstOf(v___x_6287_, v___x_6288_);
lean_dec_ref(v___x_6287_);
if (v___x_6289_ == 0)
{
lean_dec_ref(v_arg_6284_);
goto v___jp_6279_;
}
else
{
lean_dec_ref(v_h_6278_);
lean_dec_ref(v_p_6277_);
return v_arg_6284_;
}
}
}
v___jp_6279_:
{
lean_object* v___x_6280_; lean_object* v___x_6281_; 
v___x_6280_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6281_ = l_Lean_mkAppB(v___x_6280_, v_p_6277_, v_h_6278_);
return v___x_6281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6290_, lean_object* v_a_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_){
_start:
{
lean_object* v___y_6297_; lean_object* v___y_6298_; lean_object* v___y_6299_; lean_object* v___y_6300_; lean_object* v___x_6306_; 
lean_inc_ref(v_h_6290_);
v___x_6306_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6290_, v_a_6292_);
if (lean_obj_tag(v___x_6306_) == 0)
{
lean_object* v_a_6307_; lean_object* v___x_6309_; uint8_t v_isShared_6310_; uint8_t v_isSharedCheck_6322_; 
v_a_6307_ = lean_ctor_get(v___x_6306_, 0);
v_isSharedCheck_6322_ = !lean_is_exclusive(v___x_6306_);
if (v_isSharedCheck_6322_ == 0)
{
v___x_6309_ = v___x_6306_;
v_isShared_6310_ = v_isSharedCheck_6322_;
goto v_resetjp_6308_;
}
else
{
lean_inc(v_a_6307_);
lean_dec(v___x_6306_);
v___x_6309_ = lean_box(0);
v_isShared_6310_ = v_isSharedCheck_6322_;
goto v_resetjp_6308_;
}
v_resetjp_6308_:
{
lean_object* v___x_6311_; uint8_t v___x_6312_; 
v___x_6311_ = l_Lean_Expr_cleanupAnnotations(v_a_6307_);
v___x_6312_ = l_Lean_Expr_isApp(v___x_6311_);
if (v___x_6312_ == 0)
{
lean_dec_ref(v___x_6311_);
lean_del_object(v___x_6309_);
v___y_6297_ = v_a_6291_;
v___y_6298_ = v_a_6292_;
v___y_6299_ = v_a_6293_;
v___y_6300_ = v_a_6294_;
goto v___jp_6296_;
}
else
{
lean_object* v_arg_6313_; lean_object* v___x_6314_; uint8_t v___x_6315_; 
v_arg_6313_ = lean_ctor_get(v___x_6311_, 1);
lean_inc_ref(v_arg_6313_);
v___x_6314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6311_);
v___x_6315_ = l_Lean_Expr_isApp(v___x_6314_);
if (v___x_6315_ == 0)
{
lean_dec_ref(v___x_6314_);
lean_dec_ref(v_arg_6313_);
lean_del_object(v___x_6309_);
v___y_6297_ = v_a_6291_;
v___y_6298_ = v_a_6292_;
v___y_6299_ = v_a_6293_;
v___y_6300_ = v_a_6294_;
goto v___jp_6296_;
}
else
{
lean_object* v___x_6316_; lean_object* v___x_6317_; uint8_t v___x_6318_; 
v___x_6316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6314_);
v___x_6317_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6318_ = l_Lean_Expr_isConstOf(v___x_6316_, v___x_6317_);
lean_dec_ref(v___x_6316_);
if (v___x_6318_ == 0)
{
lean_dec_ref(v_arg_6313_);
lean_del_object(v___x_6309_);
v___y_6297_ = v_a_6291_;
v___y_6298_ = v_a_6292_;
v___y_6299_ = v_a_6293_;
v___y_6300_ = v_a_6294_;
goto v___jp_6296_;
}
else
{
lean_object* v___x_6320_; 
lean_dec_ref(v_h_6290_);
if (v_isShared_6310_ == 0)
{
lean_ctor_set(v___x_6309_, 0, v_arg_6313_);
v___x_6320_ = v___x_6309_;
goto v_reusejp_6319_;
}
else
{
lean_object* v_reuseFailAlloc_6321_; 
v_reuseFailAlloc_6321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6321_, 0, v_arg_6313_);
v___x_6320_ = v_reuseFailAlloc_6321_;
goto v_reusejp_6319_;
}
v_reusejp_6319_:
{
return v___x_6320_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6290_);
return v___x_6306_;
}
v___jp_6296_:
{
lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; 
v___x_6301_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6302_ = lean_unsigned_to_nat(1u);
v___x_6303_ = lean_mk_empty_array_with_capacity(v___x_6302_);
v___x_6304_ = lean_array_push(v___x_6303_, v_h_6290_);
v___x_6305_ = l_Lean_Meta_mkAppM(v___x_6301_, v___x_6304_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_);
return v___x_6305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6323_, lean_object* v_a_6324_, lean_object* v_a_6325_, lean_object* v_a_6326_, lean_object* v_a_6327_, lean_object* v_a_6328_){
_start:
{
lean_object* v_res_6329_; 
v_res_6329_ = l_Lean_Meta_mkOfEqTrue(v_h_6323_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
lean_dec(v_a_6327_);
lean_dec_ref(v_a_6326_);
lean_dec(v_a_6325_);
lean_dec_ref(v_a_6324_);
return v_res_6329_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; 
v___x_6330_ = lean_box(0);
v___x_6331_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6332_ = l_Lean_mkConst(v___x_6331_, v___x_6330_);
return v___x_6332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6333_, lean_object* v_h_6334_){
_start:
{
lean_object* v___x_6338_; uint8_t v___x_6339_; 
lean_inc_ref(v_h_6334_);
v___x_6338_ = l_Lean_Expr_cleanupAnnotations(v_h_6334_);
v___x_6339_ = l_Lean_Expr_isApp(v___x_6338_);
if (v___x_6339_ == 0)
{
lean_dec_ref(v___x_6338_);
goto v___jp_6335_;
}
else
{
lean_object* v_arg_6340_; lean_object* v___x_6341_; uint8_t v___x_6342_; 
v_arg_6340_ = lean_ctor_get(v___x_6338_, 1);
lean_inc_ref(v_arg_6340_);
v___x_6341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6338_);
v___x_6342_ = l_Lean_Expr_isApp(v___x_6341_);
if (v___x_6342_ == 0)
{
lean_dec_ref(v___x_6341_);
lean_dec_ref(v_arg_6340_);
goto v___jp_6335_;
}
else
{
lean_object* v___x_6343_; lean_object* v___x_6344_; uint8_t v___x_6345_; 
v___x_6343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6341_);
v___x_6344_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6345_ = l_Lean_Expr_isConstOf(v___x_6343_, v___x_6344_);
lean_dec_ref(v___x_6343_);
if (v___x_6345_ == 0)
{
lean_dec_ref(v_arg_6340_);
goto v___jp_6335_;
}
else
{
lean_dec_ref(v_h_6334_);
lean_dec_ref(v_p_6333_);
return v_arg_6340_;
}
}
}
v___jp_6335_:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; 
v___x_6336_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6337_ = l_Lean_mkAppB(v___x_6336_, v_p_6333_, v_h_6334_);
return v___x_6337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_, lean_object* v_a_6349_, lean_object* v_a_6350_){
_start:
{
lean_object* v___y_6353_; lean_object* v___y_6354_; lean_object* v___y_6355_; lean_object* v___y_6356_; lean_object* v___x_6368_; 
lean_inc_ref(v_h_6346_);
v___x_6368_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6346_, v_a_6348_);
if (lean_obj_tag(v___x_6368_) == 0)
{
lean_object* v_a_6369_; lean_object* v___x_6371_; uint8_t v_isShared_6372_; uint8_t v_isSharedCheck_6384_; 
v_a_6369_ = lean_ctor_get(v___x_6368_, 0);
v_isSharedCheck_6384_ = !lean_is_exclusive(v___x_6368_);
if (v_isSharedCheck_6384_ == 0)
{
v___x_6371_ = v___x_6368_;
v_isShared_6372_ = v_isSharedCheck_6384_;
goto v_resetjp_6370_;
}
else
{
lean_inc(v_a_6369_);
lean_dec(v___x_6368_);
v___x_6371_ = lean_box(0);
v_isShared_6372_ = v_isSharedCheck_6384_;
goto v_resetjp_6370_;
}
v_resetjp_6370_:
{
lean_object* v___x_6373_; uint8_t v___x_6374_; 
v___x_6373_ = l_Lean_Expr_cleanupAnnotations(v_a_6369_);
v___x_6374_ = l_Lean_Expr_isApp(v___x_6373_);
if (v___x_6374_ == 0)
{
lean_dec_ref(v___x_6373_);
lean_del_object(v___x_6371_);
v___y_6353_ = v_a_6347_;
v___y_6354_ = v_a_6348_;
v___y_6355_ = v_a_6349_;
v___y_6356_ = v_a_6350_;
goto v___jp_6352_;
}
else
{
lean_object* v_arg_6375_; lean_object* v___x_6376_; uint8_t v___x_6377_; 
v_arg_6375_ = lean_ctor_get(v___x_6373_, 1);
lean_inc_ref(v_arg_6375_);
v___x_6376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6373_);
v___x_6377_ = l_Lean_Expr_isApp(v___x_6376_);
if (v___x_6377_ == 0)
{
lean_dec_ref(v___x_6376_);
lean_dec_ref(v_arg_6375_);
lean_del_object(v___x_6371_);
v___y_6353_ = v_a_6347_;
v___y_6354_ = v_a_6348_;
v___y_6355_ = v_a_6349_;
v___y_6356_ = v_a_6350_;
goto v___jp_6352_;
}
else
{
lean_object* v___x_6378_; lean_object* v___x_6379_; uint8_t v___x_6380_; 
v___x_6378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6376_);
v___x_6379_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6380_ = l_Lean_Expr_isConstOf(v___x_6378_, v___x_6379_);
lean_dec_ref(v___x_6378_);
if (v___x_6380_ == 0)
{
lean_dec_ref(v_arg_6375_);
lean_del_object(v___x_6371_);
v___y_6353_ = v_a_6347_;
v___y_6354_ = v_a_6348_;
v___y_6355_ = v_a_6349_;
v___y_6356_ = v_a_6350_;
goto v___jp_6352_;
}
else
{
lean_object* v___x_6382_; 
lean_dec_ref(v_h_6346_);
if (v_isShared_6372_ == 0)
{
lean_ctor_set(v___x_6371_, 0, v_arg_6375_);
v___x_6382_ = v___x_6371_;
goto v_reusejp_6381_;
}
else
{
lean_object* v_reuseFailAlloc_6383_; 
v_reuseFailAlloc_6383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_arg_6375_);
v___x_6382_ = v_reuseFailAlloc_6383_;
goto v_reusejp_6381_;
}
v_reusejp_6381_:
{
return v___x_6382_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6346_);
return v___x_6368_;
}
v___jp_6352_:
{
lean_object* v___x_6357_; 
lean_inc(v___y_6356_);
lean_inc_ref(v___y_6355_);
lean_inc(v___y_6354_);
lean_inc_ref(v___y_6353_);
lean_inc_ref(v_h_6346_);
v___x_6357_ = lean_infer_type(v_h_6346_, v___y_6353_, v___y_6354_, v___y_6355_, v___y_6356_);
if (lean_obj_tag(v___x_6357_) == 0)
{
lean_object* v_a_6358_; lean_object* v___x_6360_; uint8_t v_isShared_6361_; uint8_t v_isSharedCheck_6367_; 
v_a_6358_ = lean_ctor_get(v___x_6357_, 0);
v_isSharedCheck_6367_ = !lean_is_exclusive(v___x_6357_);
if (v_isSharedCheck_6367_ == 0)
{
v___x_6360_ = v___x_6357_;
v_isShared_6361_ = v_isSharedCheck_6367_;
goto v_resetjp_6359_;
}
else
{
lean_inc(v_a_6358_);
lean_dec(v___x_6357_);
v___x_6360_ = lean_box(0);
v_isShared_6361_ = v_isSharedCheck_6367_;
goto v_resetjp_6359_;
}
v_resetjp_6359_:
{
lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6365_; 
v___x_6362_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6363_ = l_Lean_mkAppB(v___x_6362_, v_a_6358_, v_h_6346_);
if (v_isShared_6361_ == 0)
{
lean_ctor_set(v___x_6360_, 0, v___x_6363_);
v___x_6365_ = v___x_6360_;
goto v_reusejp_6364_;
}
else
{
lean_object* v_reuseFailAlloc_6366_; 
v_reuseFailAlloc_6366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6366_, 0, v___x_6363_);
v___x_6365_ = v_reuseFailAlloc_6366_;
goto v_reusejp_6364_;
}
v_reusejp_6364_:
{
return v___x_6365_;
}
}
}
else
{
lean_dec_ref(v_h_6346_);
return v___x_6357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_){
_start:
{
lean_object* v_res_6391_; 
v_res_6391_ = l_Lean_Meta_mkEqTrue(v_h_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_);
lean_dec(v_a_6389_);
lean_dec_ref(v_a_6388_);
lean_dec(v_a_6387_);
lean_dec_ref(v_a_6386_);
return v_res_6391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6392_, lean_object* v_a_6393_, lean_object* v_a_6394_, lean_object* v_a_6395_, lean_object* v_a_6396_){
_start:
{
lean_object* v___y_6399_; lean_object* v___y_6400_; lean_object* v___y_6401_; lean_object* v___y_6402_; lean_object* v___x_6408_; uint8_t v___x_6409_; 
lean_inc_ref(v_h_6392_);
v___x_6408_ = l_Lean_Expr_cleanupAnnotations(v_h_6392_);
v___x_6409_ = l_Lean_Expr_isApp(v___x_6408_);
if (v___x_6409_ == 0)
{
lean_dec_ref(v___x_6408_);
v___y_6399_ = v_a_6393_;
v___y_6400_ = v_a_6394_;
v___y_6401_ = v_a_6395_;
v___y_6402_ = v_a_6396_;
goto v___jp_6398_;
}
else
{
lean_object* v_arg_6410_; lean_object* v___x_6411_; uint8_t v___x_6412_; 
v_arg_6410_ = lean_ctor_get(v___x_6408_, 1);
lean_inc_ref(v_arg_6410_);
v___x_6411_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6408_);
v___x_6412_ = l_Lean_Expr_isApp(v___x_6411_);
if (v___x_6412_ == 0)
{
lean_dec_ref(v___x_6411_);
lean_dec_ref(v_arg_6410_);
v___y_6399_ = v_a_6393_;
v___y_6400_ = v_a_6394_;
v___y_6401_ = v_a_6395_;
v___y_6402_ = v_a_6396_;
goto v___jp_6398_;
}
else
{
lean_object* v___x_6413_; lean_object* v___x_6414_; uint8_t v___x_6415_; 
v___x_6413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6411_);
v___x_6414_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6415_ = l_Lean_Expr_isConstOf(v___x_6413_, v___x_6414_);
lean_dec_ref(v___x_6413_);
if (v___x_6415_ == 0)
{
lean_dec_ref(v_arg_6410_);
v___y_6399_ = v_a_6393_;
v___y_6400_ = v_a_6394_;
v___y_6401_ = v_a_6395_;
v___y_6402_ = v_a_6396_;
goto v___jp_6398_;
}
else
{
lean_object* v___x_6416_; 
lean_dec_ref(v_h_6392_);
v___x_6416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6416_, 0, v_arg_6410_);
return v___x_6416_;
}
}
}
v___jp_6398_:
{
lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6403_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6404_ = lean_unsigned_to_nat(1u);
v___x_6405_ = lean_mk_empty_array_with_capacity(v___x_6404_);
v___x_6406_ = lean_array_push(v___x_6405_, v_h_6392_);
v___x_6407_ = l_Lean_Meta_mkAppM(v___x_6403_, v___x_6406_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_);
return v___x_6407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6417_, lean_object* v_a_6418_, lean_object* v_a_6419_, lean_object* v_a_6420_, lean_object* v_a_6421_, lean_object* v_a_6422_){
_start:
{
lean_object* v_res_6423_; 
v_res_6423_ = l_Lean_Meta_mkEqFalse(v_h_6417_, v_a_6418_, v_a_6419_, v_a_6420_, v_a_6421_);
lean_dec(v_a_6421_);
lean_dec_ref(v_a_6420_);
lean_dec(v_a_6419_);
lean_dec_ref(v_a_6418_);
return v_res_6423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6427_, lean_object* v_a_6428_, lean_object* v_a_6429_, lean_object* v_a_6430_, lean_object* v_a_6431_){
_start:
{
lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; 
v___x_6433_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6434_ = lean_unsigned_to_nat(1u);
v___x_6435_ = lean_mk_empty_array_with_capacity(v___x_6434_);
v___x_6436_ = lean_array_push(v___x_6435_, v_h_6427_);
v___x_6437_ = l_Lean_Meta_mkAppM(v___x_6433_, v___x_6436_, v_a_6428_, v_a_6429_, v_a_6430_, v_a_6431_);
return v___x_6437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6438_, lean_object* v_a_6439_, lean_object* v_a_6440_, lean_object* v_a_6441_, lean_object* v_a_6442_, lean_object* v_a_6443_){
_start:
{
lean_object* v_res_6444_; 
v_res_6444_ = l_Lean_Meta_mkEqFalse_x27(v_h_6438_, v_a_6439_, v_a_6440_, v_a_6441_, v_a_6442_);
lean_dec(v_a_6442_);
lean_dec_ref(v_a_6441_);
lean_dec(v_a_6440_);
lean_dec_ref(v_a_6439_);
return v_res_6444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6448_, lean_object* v_h_u2082_6449_, lean_object* v_a_6450_, lean_object* v_a_6451_, lean_object* v_a_6452_, lean_object* v_a_6453_){
_start:
{
lean_object* v___x_6455_; lean_object* v___x_6456_; lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; 
v___x_6455_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6456_ = lean_unsigned_to_nat(2u);
v___x_6457_ = lean_mk_empty_array_with_capacity(v___x_6456_);
v___x_6458_ = lean_array_push(v___x_6457_, v_h_u2081_6448_);
v___x_6459_ = lean_array_push(v___x_6458_, v_h_u2082_6449_);
v___x_6460_ = l_Lean_Meta_mkAppM(v___x_6455_, v___x_6459_, v_a_6450_, v_a_6451_, v_a_6452_, v_a_6453_);
return v___x_6460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6461_, lean_object* v_h_u2082_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_, lean_object* v_a_6467_){
_start:
{
lean_object* v_res_6468_; 
v_res_6468_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6461_, v_h_u2082_6462_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_);
lean_dec(v_a_6466_);
lean_dec_ref(v_a_6465_);
lean_dec(v_a_6464_);
lean_dec_ref(v_a_6463_);
return v_res_6468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6472_, lean_object* v_h_u2082_6473_, lean_object* v_a_6474_, lean_object* v_a_6475_, lean_object* v_a_6476_, lean_object* v_a_6477_){
_start:
{
lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v___x_6479_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6480_ = lean_unsigned_to_nat(2u);
v___x_6481_ = lean_mk_empty_array_with_capacity(v___x_6480_);
v___x_6482_ = lean_array_push(v___x_6481_, v_h_u2081_6472_);
v___x_6483_ = lean_array_push(v___x_6482_, v_h_u2082_6473_);
v___x_6484_ = l_Lean_Meta_mkAppM(v___x_6479_, v___x_6483_, v_a_6474_, v_a_6475_, v_a_6476_, v_a_6477_);
return v___x_6484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6485_, lean_object* v_h_u2082_6486_, lean_object* v_a_6487_, lean_object* v_a_6488_, lean_object* v_a_6489_, lean_object* v_a_6490_, lean_object* v_a_6491_){
_start:
{
lean_object* v_res_6492_; 
v_res_6492_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6485_, v_h_u2082_6486_, v_a_6487_, v_a_6488_, v_a_6489_, v_a_6490_);
lean_dec(v_a_6490_);
lean_dec_ref(v_a_6489_);
lean_dec(v_a_6488_);
lean_dec_ref(v_a_6487_);
return v_res_6492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6496_, lean_object* v_h_u2082_6497_, lean_object* v_a_6498_, lean_object* v_a_6499_, lean_object* v_a_6500_, lean_object* v_a_6501_){
_start:
{
lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; 
v___x_6503_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6504_ = lean_unsigned_to_nat(2u);
v___x_6505_ = lean_mk_empty_array_with_capacity(v___x_6504_);
v___x_6506_ = lean_array_push(v___x_6505_, v_h_u2081_6496_);
v___x_6507_ = lean_array_push(v___x_6506_, v_h_u2082_6497_);
v___x_6508_ = l_Lean_Meta_mkAppM(v___x_6503_, v___x_6507_, v_a_6498_, v_a_6499_, v_a_6500_, v_a_6501_);
return v___x_6508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6509_, lean_object* v_h_u2082_6510_, lean_object* v_a_6511_, lean_object* v_a_6512_, lean_object* v_a_6513_, lean_object* v_a_6514_, lean_object* v_a_6515_){
_start:
{
lean_object* v_res_6516_; 
v_res_6516_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6509_, v_h_u2082_6510_, v_a_6511_, v_a_6512_, v_a_6513_, v_a_6514_);
lean_dec(v_a_6514_);
lean_dec_ref(v_a_6513_);
lean_dec(v_a_6512_);
lean_dec_ref(v_a_6511_);
return v_res_6516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6520_, lean_object* v_a_6521_, lean_object* v_a_6522_, lean_object* v_a_6523_, lean_object* v_a_6524_){
_start:
{
lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; 
v___x_6526_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6527_ = lean_unsigned_to_nat(1u);
v___x_6528_ = lean_mk_empty_array_with_capacity(v___x_6527_);
v___x_6529_ = lean_array_push(v___x_6528_, v_h_6520_);
v___x_6530_ = l_Lean_Meta_mkAppM(v___x_6526_, v___x_6529_, v_a_6521_, v_a_6522_, v_a_6523_, v_a_6524_);
return v___x_6530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6531_, lean_object* v_a_6532_, lean_object* v_a_6533_, lean_object* v_a_6534_, lean_object* v_a_6535_, lean_object* v_a_6536_){
_start:
{
lean_object* v_res_6537_; 
v_res_6537_ = l_Lean_Meta_mkForallCongr(v_h_6531_, v_a_6532_, v_a_6533_, v_a_6534_, v_a_6535_);
lean_dec(v_a_6535_);
lean_dec_ref(v_a_6534_);
lean_dec(v_a_6533_);
lean_dec_ref(v_a_6532_);
return v_res_6537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6541_, lean_object* v_a_6542_, lean_object* v_a_6543_, lean_object* v_a_6544_, lean_object* v_a_6545_){
_start:
{
lean_object* v___y_6548_; uint8_t v___y_6549_; lean_object* v___y_6553_; lean_object* v_a_6554_; lean_object* v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; 
v___x_6557_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6558_ = lean_unsigned_to_nat(1u);
v___x_6559_ = lean_mk_empty_array_with_capacity(v___x_6558_);
v___x_6560_ = lean_array_push(v___x_6559_, v_m_6541_);
v___x_6561_ = l_Lean_Meta_mkAppM(v___x_6557_, v___x_6560_, v_a_6542_, v_a_6543_, v_a_6544_, v_a_6545_);
if (lean_obj_tag(v___x_6561_) == 0)
{
lean_object* v_a_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; 
v_a_6562_ = lean_ctor_get(v___x_6561_, 0);
lean_inc(v_a_6562_);
lean_dec_ref_known(v___x_6561_, 1);
v___x_6563_ = lean_box(0);
v___x_6564_ = l_Lean_Meta_trySynthInstance(v_a_6562_, v___x_6563_, v_a_6542_, v_a_6543_, v_a_6544_, v_a_6545_);
if (lean_obj_tag(v___x_6564_) == 0)
{
lean_object* v_a_6565_; lean_object* v___x_6567_; uint8_t v_isShared_6568_; uint8_t v_isSharedCheck_6583_; 
v_a_6565_ = lean_ctor_get(v___x_6564_, 0);
v_isSharedCheck_6583_ = !lean_is_exclusive(v___x_6564_);
if (v_isSharedCheck_6583_ == 0)
{
v___x_6567_ = v___x_6564_;
v_isShared_6568_ = v_isSharedCheck_6583_;
goto v_resetjp_6566_;
}
else
{
lean_inc(v_a_6565_);
lean_dec(v___x_6564_);
v___x_6567_ = lean_box(0);
v_isShared_6568_ = v_isSharedCheck_6583_;
goto v_resetjp_6566_;
}
v_resetjp_6566_:
{
if (lean_obj_tag(v_a_6565_) == 1)
{
lean_object* v_a_6569_; lean_object* v___x_6571_; uint8_t v_isShared_6572_; uint8_t v_isSharedCheck_6579_; 
v_a_6569_ = lean_ctor_get(v_a_6565_, 0);
v_isSharedCheck_6579_ = !lean_is_exclusive(v_a_6565_);
if (v_isSharedCheck_6579_ == 0)
{
v___x_6571_ = v_a_6565_;
v_isShared_6572_ = v_isSharedCheck_6579_;
goto v_resetjp_6570_;
}
else
{
lean_inc(v_a_6569_);
lean_dec(v_a_6565_);
v___x_6571_ = lean_box(0);
v_isShared_6572_ = v_isSharedCheck_6579_;
goto v_resetjp_6570_;
}
v_resetjp_6570_:
{
lean_object* v___x_6574_; 
if (v_isShared_6572_ == 0)
{
v___x_6574_ = v___x_6571_;
goto v_reusejp_6573_;
}
else
{
lean_object* v_reuseFailAlloc_6578_; 
v_reuseFailAlloc_6578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6578_, 0, v_a_6569_);
v___x_6574_ = v_reuseFailAlloc_6578_;
goto v_reusejp_6573_;
}
v_reusejp_6573_:
{
lean_object* v___x_6576_; 
if (v_isShared_6568_ == 0)
{
lean_ctor_set(v___x_6567_, 0, v___x_6574_);
v___x_6576_ = v___x_6567_;
goto v_reusejp_6575_;
}
else
{
lean_object* v_reuseFailAlloc_6577_; 
v_reuseFailAlloc_6577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6577_, 0, v___x_6574_);
v___x_6576_ = v_reuseFailAlloc_6577_;
goto v_reusejp_6575_;
}
v_reusejp_6575_:
{
return v___x_6576_;
}
}
}
}
else
{
lean_object* v___x_6581_; 
lean_dec(v_a_6565_);
if (v_isShared_6568_ == 0)
{
lean_ctor_set(v___x_6567_, 0, v___x_6563_);
v___x_6581_ = v___x_6567_;
goto v_reusejp_6580_;
}
else
{
lean_object* v_reuseFailAlloc_6582_; 
v_reuseFailAlloc_6582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6582_, 0, v___x_6563_);
v___x_6581_ = v_reuseFailAlloc_6582_;
goto v_reusejp_6580_;
}
v_reusejp_6580_:
{
return v___x_6581_;
}
}
}
}
else
{
lean_object* v_a_6584_; lean_object* v___x_6586_; uint8_t v_isShared_6587_; uint8_t v_isSharedCheck_6591_; 
v_a_6584_ = lean_ctor_get(v___x_6564_, 0);
v_isSharedCheck_6591_ = !lean_is_exclusive(v___x_6564_);
if (v_isSharedCheck_6591_ == 0)
{
v___x_6586_ = v___x_6564_;
v_isShared_6587_ = v_isSharedCheck_6591_;
goto v_resetjp_6585_;
}
else
{
lean_inc(v_a_6584_);
lean_dec(v___x_6564_);
v___x_6586_ = lean_box(0);
v_isShared_6587_ = v_isSharedCheck_6591_;
goto v_resetjp_6585_;
}
v_resetjp_6585_:
{
lean_object* v___x_6589_; 
lean_inc(v_a_6584_);
if (v_isShared_6587_ == 0)
{
v___x_6589_ = v___x_6586_;
goto v_reusejp_6588_;
}
else
{
lean_object* v_reuseFailAlloc_6590_; 
v_reuseFailAlloc_6590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
v___x_6589_ = v_reuseFailAlloc_6590_;
goto v_reusejp_6588_;
}
v_reusejp_6588_:
{
v___y_6553_ = v___x_6589_;
v_a_6554_ = v_a_6584_;
goto v___jp_6552_;
}
}
}
}
else
{
lean_object* v_a_6592_; lean_object* v___x_6594_; uint8_t v_isShared_6595_; uint8_t v_isSharedCheck_6599_; 
v_a_6592_ = lean_ctor_get(v___x_6561_, 0);
v_isSharedCheck_6599_ = !lean_is_exclusive(v___x_6561_);
if (v_isSharedCheck_6599_ == 0)
{
v___x_6594_ = v___x_6561_;
v_isShared_6595_ = v_isSharedCheck_6599_;
goto v_resetjp_6593_;
}
else
{
lean_inc(v_a_6592_);
lean_dec(v___x_6561_);
v___x_6594_ = lean_box(0);
v_isShared_6595_ = v_isSharedCheck_6599_;
goto v_resetjp_6593_;
}
v_resetjp_6593_:
{
lean_object* v___x_6597_; 
lean_inc(v_a_6592_);
if (v_isShared_6595_ == 0)
{
v___x_6597_ = v___x_6594_;
goto v_reusejp_6596_;
}
else
{
lean_object* v_reuseFailAlloc_6598_; 
v_reuseFailAlloc_6598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6598_, 0, v_a_6592_);
v___x_6597_ = v_reuseFailAlloc_6598_;
goto v_reusejp_6596_;
}
v_reusejp_6596_:
{
v___y_6553_ = v___x_6597_;
v_a_6554_ = v_a_6592_;
goto v___jp_6552_;
}
}
}
v___jp_6547_:
{
if (v___y_6549_ == 0)
{
lean_object* v___x_6550_; lean_object* v___x_6551_; 
lean_dec_ref(v___y_6548_);
v___x_6550_ = lean_box(0);
v___x_6551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6551_, 0, v___x_6550_);
return v___x_6551_;
}
else
{
return v___y_6548_;
}
}
v___jp_6552_:
{
uint8_t v___x_6555_; 
v___x_6555_ = l_Lean_Exception_isInterrupt(v_a_6554_);
if (v___x_6555_ == 0)
{
uint8_t v___x_6556_; 
v___x_6556_ = l_Lean_Exception_isRuntime(v_a_6554_);
v___y_6548_ = v___y_6553_;
v___y_6549_ = v___x_6556_;
goto v___jp_6547_;
}
else
{
lean_dec_ref(v_a_6554_);
v___y_6548_ = v___y_6553_;
v___y_6549_ = v___x_6555_;
goto v___jp_6547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6600_, lean_object* v_a_6601_, lean_object* v_a_6602_, lean_object* v_a_6603_, lean_object* v_a_6604_, lean_object* v_a_6605_){
_start:
{
lean_object* v_res_6606_; 
v_res_6606_ = l_Lean_Meta_isMonad_x3f(v_m_6600_, v_a_6601_, v_a_6602_, v_a_6603_, v_a_6604_);
lean_dec(v_a_6604_);
lean_dec_ref(v_a_6603_);
lean_dec(v_a_6602_);
lean_dec_ref(v_a_6601_);
return v_res_6606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6614_, lean_object* v_n_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_){
_start:
{
lean_object* v___x_6621_; 
lean_inc_ref(v_type_6614_);
v___x_6621_ = l_Lean_Meta_getDecLevel(v_type_6614_, v_a_6616_, v_a_6617_, v_a_6618_, v_a_6619_);
if (lean_obj_tag(v___x_6621_) == 0)
{
lean_object* v_a_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6630_; 
v_a_6622_ = lean_ctor_get(v___x_6621_, 0);
lean_inc(v_a_6622_);
lean_dec_ref_known(v___x_6621_, 1);
v___x_6623_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6624_ = lean_box(0);
v___x_6625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6625_, 0, v_a_6622_);
lean_ctor_set(v___x_6625_, 1, v___x_6624_);
lean_inc_ref(v___x_6625_);
v___x_6626_ = l_Lean_mkConst(v___x_6623_, v___x_6625_);
v___x_6627_ = l_Lean_mkRawNatLit(v_n_6615_);
lean_inc_ref(v___x_6627_);
lean_inc_ref(v_type_6614_);
v___x_6628_ = l_Lean_mkAppB(v___x_6626_, v_type_6614_, v___x_6627_);
v___x_6629_ = lean_box(0);
v___x_6630_ = l_Lean_Meta_synthInstance(v___x_6628_, v___x_6629_, v_a_6616_, v_a_6617_, v_a_6618_, v_a_6619_);
if (lean_obj_tag(v___x_6630_) == 0)
{
lean_object* v_a_6631_; lean_object* v___x_6633_; uint8_t v_isShared_6634_; uint8_t v_isSharedCheck_6641_; 
v_a_6631_ = lean_ctor_get(v___x_6630_, 0);
v_isSharedCheck_6641_ = !lean_is_exclusive(v___x_6630_);
if (v_isSharedCheck_6641_ == 0)
{
v___x_6633_ = v___x_6630_;
v_isShared_6634_ = v_isSharedCheck_6641_;
goto v_resetjp_6632_;
}
else
{
lean_inc(v_a_6631_);
lean_dec(v___x_6630_);
v___x_6633_ = lean_box(0);
v_isShared_6634_ = v_isSharedCheck_6641_;
goto v_resetjp_6632_;
}
v_resetjp_6632_:
{
lean_object* v___x_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; lean_object* v___x_6639_; 
v___x_6635_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6636_ = l_Lean_mkConst(v___x_6635_, v___x_6625_);
v___x_6637_ = l_Lean_mkApp3(v___x_6636_, v_type_6614_, v___x_6627_, v_a_6631_);
if (v_isShared_6634_ == 0)
{
lean_ctor_set(v___x_6633_, 0, v___x_6637_);
v___x_6639_ = v___x_6633_;
goto v_reusejp_6638_;
}
else
{
lean_object* v_reuseFailAlloc_6640_; 
v_reuseFailAlloc_6640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6640_, 0, v___x_6637_);
v___x_6639_ = v_reuseFailAlloc_6640_;
goto v_reusejp_6638_;
}
v_reusejp_6638_:
{
return v___x_6639_;
}
}
}
else
{
lean_dec_ref(v___x_6627_);
lean_dec_ref_known(v___x_6625_, 2);
lean_dec_ref(v_type_6614_);
return v___x_6630_;
}
}
else
{
lean_object* v_a_6642_; lean_object* v___x_6644_; uint8_t v_isShared_6645_; uint8_t v_isSharedCheck_6649_; 
lean_dec(v_n_6615_);
lean_dec_ref(v_type_6614_);
v_a_6642_ = lean_ctor_get(v___x_6621_, 0);
v_isSharedCheck_6649_ = !lean_is_exclusive(v___x_6621_);
if (v_isSharedCheck_6649_ == 0)
{
v___x_6644_ = v___x_6621_;
v_isShared_6645_ = v_isSharedCheck_6649_;
goto v_resetjp_6643_;
}
else
{
lean_inc(v_a_6642_);
lean_dec(v___x_6621_);
v___x_6644_ = lean_box(0);
v_isShared_6645_ = v_isSharedCheck_6649_;
goto v_resetjp_6643_;
}
v_resetjp_6643_:
{
lean_object* v___x_6647_; 
if (v_isShared_6645_ == 0)
{
v___x_6647_ = v___x_6644_;
goto v_reusejp_6646_;
}
else
{
lean_object* v_reuseFailAlloc_6648_; 
v_reuseFailAlloc_6648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6648_, 0, v_a_6642_);
v___x_6647_ = v_reuseFailAlloc_6648_;
goto v_reusejp_6646_;
}
v_reusejp_6646_:
{
return v___x_6647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6650_, lean_object* v_n_6651_, lean_object* v_a_6652_, lean_object* v_a_6653_, lean_object* v_a_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_){
_start:
{
lean_object* v_res_6657_; 
v_res_6657_ = l_Lean_Meta_mkNumeral(v_type_6650_, v_n_6651_, v_a_6652_, v_a_6653_, v_a_6654_, v_a_6655_);
lean_dec(v_a_6655_);
lean_dec_ref(v_a_6654_);
lean_dec(v_a_6653_);
lean_dec_ref(v_a_6652_);
return v_res_6657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6658_, lean_object* v_opName_6659_, lean_object* v_a_6660_, lean_object* v_b_6661_, lean_object* v_a_6662_, lean_object* v_a_6663_, lean_object* v_a_6664_, lean_object* v_a_6665_){
_start:
{
lean_object* v___x_6667_; 
lean_inc(v_a_6665_);
lean_inc_ref(v_a_6664_);
lean_inc(v_a_6663_);
lean_inc_ref(v_a_6662_);
lean_inc_ref(v_a_6660_);
v___x_6667_ = lean_infer_type(v_a_6660_, v_a_6662_, v_a_6663_, v_a_6664_, v_a_6665_);
if (lean_obj_tag(v___x_6667_) == 0)
{
lean_object* v_a_6668_; lean_object* v___x_6669_; 
v_a_6668_ = lean_ctor_get(v___x_6667_, 0);
lean_inc_n(v_a_6668_, 2);
lean_dec_ref_known(v___x_6667_, 1);
v___x_6669_ = l_Lean_Meta_getDecLevel(v_a_6668_, v_a_6662_, v_a_6663_, v_a_6664_, v_a_6665_);
if (lean_obj_tag(v___x_6669_) == 0)
{
lean_object* v_a_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; 
v_a_6670_ = lean_ctor_get(v___x_6669_, 0);
lean_inc_n(v_a_6670_, 3);
lean_dec_ref_known(v___x_6669_, 1);
v___x_6671_ = lean_box(0);
v___x_6672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6672_, 0, v_a_6670_);
lean_ctor_set(v___x_6672_, 1, v___x_6671_);
v___x_6673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6673_, 0, v_a_6670_);
lean_ctor_set(v___x_6673_, 1, v___x_6672_);
v___x_6674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6674_, 0, v_a_6670_);
lean_ctor_set(v___x_6674_, 1, v___x_6673_);
lean_inc_ref(v___x_6674_);
v___x_6675_ = l_Lean_mkConst(v_className_6658_, v___x_6674_);
lean_inc_n(v_a_6668_, 3);
v___x_6676_ = l_Lean_mkApp3(v___x_6675_, v_a_6668_, v_a_6668_, v_a_6668_);
v___x_6677_ = lean_box(0);
v___x_6678_ = l_Lean_Meta_synthInstance(v___x_6676_, v___x_6677_, v_a_6662_, v_a_6663_, v_a_6664_, v_a_6665_);
if (lean_obj_tag(v___x_6678_) == 0)
{
lean_object* v_a_6679_; lean_object* v___x_6681_; uint8_t v_isShared_6682_; uint8_t v_isSharedCheck_6688_; 
v_a_6679_ = lean_ctor_get(v___x_6678_, 0);
v_isSharedCheck_6688_ = !lean_is_exclusive(v___x_6678_);
if (v_isSharedCheck_6688_ == 0)
{
v___x_6681_ = v___x_6678_;
v_isShared_6682_ = v_isSharedCheck_6688_;
goto v_resetjp_6680_;
}
else
{
lean_inc(v_a_6679_);
lean_dec(v___x_6678_);
v___x_6681_ = lean_box(0);
v_isShared_6682_ = v_isSharedCheck_6688_;
goto v_resetjp_6680_;
}
v_resetjp_6680_:
{
lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6686_; 
v___x_6683_ = l_Lean_mkConst(v_opName_6659_, v___x_6674_);
lean_inc_n(v_a_6668_, 2);
v___x_6684_ = l_Lean_mkApp6(v___x_6683_, v_a_6668_, v_a_6668_, v_a_6668_, v_a_6679_, v_a_6660_, v_b_6661_);
if (v_isShared_6682_ == 0)
{
lean_ctor_set(v___x_6681_, 0, v___x_6684_);
v___x_6686_ = v___x_6681_;
goto v_reusejp_6685_;
}
else
{
lean_object* v_reuseFailAlloc_6687_; 
v_reuseFailAlloc_6687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6687_, 0, v___x_6684_);
v___x_6686_ = v_reuseFailAlloc_6687_;
goto v_reusejp_6685_;
}
v_reusejp_6685_:
{
return v___x_6686_;
}
}
}
else
{
lean_dec_ref_known(v___x_6674_, 2);
lean_dec(v_a_6668_);
lean_dec_ref(v_b_6661_);
lean_dec_ref(v_a_6660_);
lean_dec(v_opName_6659_);
return v___x_6678_;
}
}
else
{
lean_object* v_a_6689_; lean_object* v___x_6691_; uint8_t v_isShared_6692_; uint8_t v_isSharedCheck_6696_; 
lean_dec(v_a_6668_);
lean_dec_ref(v_b_6661_);
lean_dec_ref(v_a_6660_);
lean_dec(v_opName_6659_);
lean_dec(v_className_6658_);
v_a_6689_ = lean_ctor_get(v___x_6669_, 0);
v_isSharedCheck_6696_ = !lean_is_exclusive(v___x_6669_);
if (v_isSharedCheck_6696_ == 0)
{
v___x_6691_ = v___x_6669_;
v_isShared_6692_ = v_isSharedCheck_6696_;
goto v_resetjp_6690_;
}
else
{
lean_inc(v_a_6689_);
lean_dec(v___x_6669_);
v___x_6691_ = lean_box(0);
v_isShared_6692_ = v_isSharedCheck_6696_;
goto v_resetjp_6690_;
}
v_resetjp_6690_:
{
lean_object* v___x_6694_; 
if (v_isShared_6692_ == 0)
{
v___x_6694_ = v___x_6691_;
goto v_reusejp_6693_;
}
else
{
lean_object* v_reuseFailAlloc_6695_; 
v_reuseFailAlloc_6695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6695_, 0, v_a_6689_);
v___x_6694_ = v_reuseFailAlloc_6695_;
goto v_reusejp_6693_;
}
v_reusejp_6693_:
{
return v___x_6694_;
}
}
}
}
else
{
lean_dec_ref(v_b_6661_);
lean_dec_ref(v_a_6660_);
lean_dec(v_opName_6659_);
lean_dec(v_className_6658_);
return v___x_6667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6697_, lean_object* v_opName_6698_, lean_object* v_a_6699_, lean_object* v_b_6700_, lean_object* v_a_6701_, lean_object* v_a_6702_, lean_object* v_a_6703_, lean_object* v_a_6704_, lean_object* v_a_6705_){
_start:
{
lean_object* v_res_6706_; 
v_res_6706_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6697_, v_opName_6698_, v_a_6699_, v_b_6700_, v_a_6701_, v_a_6702_, v_a_6703_, v_a_6704_);
lean_dec(v_a_6704_);
lean_dec_ref(v_a_6703_);
lean_dec(v_a_6702_);
lean_dec_ref(v_a_6701_);
return v_res_6706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6714_, lean_object* v_b_6715_, lean_object* v_a_6716_, lean_object* v_a_6717_, lean_object* v_a_6718_, lean_object* v_a_6719_){
_start:
{
lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; 
v___x_6721_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6722_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6723_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6721_, v___x_6722_, v_a_6714_, v_b_6715_, v_a_6716_, v_a_6717_, v_a_6718_, v_a_6719_);
return v___x_6723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6724_, lean_object* v_b_6725_, lean_object* v_a_6726_, lean_object* v_a_6727_, lean_object* v_a_6728_, lean_object* v_a_6729_, lean_object* v_a_6730_){
_start:
{
lean_object* v_res_6731_; 
v_res_6731_ = l_Lean_Meta_mkAdd(v_a_6724_, v_b_6725_, v_a_6726_, v_a_6727_, v_a_6728_, v_a_6729_);
lean_dec(v_a_6729_);
lean_dec_ref(v_a_6728_);
lean_dec(v_a_6727_);
lean_dec_ref(v_a_6726_);
return v_res_6731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6739_, lean_object* v_b_6740_, lean_object* v_a_6741_, lean_object* v_a_6742_, lean_object* v_a_6743_, lean_object* v_a_6744_){
_start:
{
lean_object* v___x_6746_; lean_object* v___x_6747_; lean_object* v___x_6748_; 
v___x_6746_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6747_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6748_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6746_, v___x_6747_, v_a_6739_, v_b_6740_, v_a_6741_, v_a_6742_, v_a_6743_, v_a_6744_);
return v___x_6748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6749_, lean_object* v_b_6750_, lean_object* v_a_6751_, lean_object* v_a_6752_, lean_object* v_a_6753_, lean_object* v_a_6754_, lean_object* v_a_6755_){
_start:
{
lean_object* v_res_6756_; 
v_res_6756_ = l_Lean_Meta_mkSub(v_a_6749_, v_b_6750_, v_a_6751_, v_a_6752_, v_a_6753_, v_a_6754_);
lean_dec(v_a_6754_);
lean_dec_ref(v_a_6753_);
lean_dec(v_a_6752_);
lean_dec_ref(v_a_6751_);
return v_res_6756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6764_, lean_object* v_b_6765_, lean_object* v_a_6766_, lean_object* v_a_6767_, lean_object* v_a_6768_, lean_object* v_a_6769_){
_start:
{
lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; 
v___x_6771_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6772_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6773_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6771_, v___x_6772_, v_a_6764_, v_b_6765_, v_a_6766_, v_a_6767_, v_a_6768_, v_a_6769_);
return v___x_6773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6774_, lean_object* v_b_6775_, lean_object* v_a_6776_, lean_object* v_a_6777_, lean_object* v_a_6778_, lean_object* v_a_6779_, lean_object* v_a_6780_){
_start:
{
lean_object* v_res_6781_; 
v_res_6781_ = l_Lean_Meta_mkMul(v_a_6774_, v_b_6775_, v_a_6776_, v_a_6777_, v_a_6778_, v_a_6779_);
lean_dec(v_a_6779_);
lean_dec_ref(v_a_6778_);
lean_dec(v_a_6777_);
lean_dec_ref(v_a_6776_);
return v_res_6781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6782_, lean_object* v_rName_6783_, lean_object* v_a_6784_, lean_object* v_b_6785_, lean_object* v_a_6786_, lean_object* v_a_6787_, lean_object* v_a_6788_, lean_object* v_a_6789_){
_start:
{
lean_object* v___x_6791_; 
lean_inc(v_a_6789_);
lean_inc_ref(v_a_6788_);
lean_inc(v_a_6787_);
lean_inc_ref(v_a_6786_);
lean_inc_ref(v_a_6784_);
v___x_6791_ = lean_infer_type(v_a_6784_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_);
if (lean_obj_tag(v___x_6791_) == 0)
{
lean_object* v_a_6792_; lean_object* v___x_6793_; 
v_a_6792_ = lean_ctor_get(v___x_6791_, 0);
lean_inc_n(v_a_6792_, 2);
lean_dec_ref_known(v___x_6791_, 1);
v___x_6793_ = l_Lean_Meta_getDecLevel(v_a_6792_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_);
if (lean_obj_tag(v___x_6793_) == 0)
{
lean_object* v_a_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___x_6798_; lean_object* v___x_6799_; lean_object* v___x_6800_; 
v_a_6794_ = lean_ctor_get(v___x_6793_, 0);
lean_inc(v_a_6794_);
lean_dec_ref_known(v___x_6793_, 1);
v___x_6795_ = lean_box(0);
v___x_6796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6796_, 0, v_a_6794_);
lean_ctor_set(v___x_6796_, 1, v___x_6795_);
lean_inc_ref(v___x_6796_);
v___x_6797_ = l_Lean_mkConst(v_className_6782_, v___x_6796_);
lean_inc(v_a_6792_);
v___x_6798_ = l_Lean_Expr_app___override(v___x_6797_, v_a_6792_);
v___x_6799_ = lean_box(0);
v___x_6800_ = l_Lean_Meta_synthInstance(v___x_6798_, v___x_6799_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_);
if (lean_obj_tag(v___x_6800_) == 0)
{
lean_object* v_a_6801_; lean_object* v___x_6803_; uint8_t v_isShared_6804_; uint8_t v_isSharedCheck_6810_; 
v_a_6801_ = lean_ctor_get(v___x_6800_, 0);
v_isSharedCheck_6810_ = !lean_is_exclusive(v___x_6800_);
if (v_isSharedCheck_6810_ == 0)
{
v___x_6803_ = v___x_6800_;
v_isShared_6804_ = v_isSharedCheck_6810_;
goto v_resetjp_6802_;
}
else
{
lean_inc(v_a_6801_);
lean_dec(v___x_6800_);
v___x_6803_ = lean_box(0);
v_isShared_6804_ = v_isSharedCheck_6810_;
goto v_resetjp_6802_;
}
v_resetjp_6802_:
{
lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v___x_6808_; 
v___x_6805_ = l_Lean_mkConst(v_rName_6783_, v___x_6796_);
v___x_6806_ = l_Lean_mkApp4(v___x_6805_, v_a_6792_, v_a_6801_, v_a_6784_, v_b_6785_);
if (v_isShared_6804_ == 0)
{
lean_ctor_set(v___x_6803_, 0, v___x_6806_);
v___x_6808_ = v___x_6803_;
goto v_reusejp_6807_;
}
else
{
lean_object* v_reuseFailAlloc_6809_; 
v_reuseFailAlloc_6809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6809_, 0, v___x_6806_);
v___x_6808_ = v_reuseFailAlloc_6809_;
goto v_reusejp_6807_;
}
v_reusejp_6807_:
{
return v___x_6808_;
}
}
}
else
{
lean_dec_ref_known(v___x_6796_, 2);
lean_dec(v_a_6792_);
lean_dec_ref(v_b_6785_);
lean_dec_ref(v_a_6784_);
lean_dec(v_rName_6783_);
return v___x_6800_;
}
}
else
{
lean_object* v_a_6811_; lean_object* v___x_6813_; uint8_t v_isShared_6814_; uint8_t v_isSharedCheck_6818_; 
lean_dec(v_a_6792_);
lean_dec_ref(v_b_6785_);
lean_dec_ref(v_a_6784_);
lean_dec(v_rName_6783_);
lean_dec(v_className_6782_);
v_a_6811_ = lean_ctor_get(v___x_6793_, 0);
v_isSharedCheck_6818_ = !lean_is_exclusive(v___x_6793_);
if (v_isSharedCheck_6818_ == 0)
{
v___x_6813_ = v___x_6793_;
v_isShared_6814_ = v_isSharedCheck_6818_;
goto v_resetjp_6812_;
}
else
{
lean_inc(v_a_6811_);
lean_dec(v___x_6793_);
v___x_6813_ = lean_box(0);
v_isShared_6814_ = v_isSharedCheck_6818_;
goto v_resetjp_6812_;
}
v_resetjp_6812_:
{
lean_object* v___x_6816_; 
if (v_isShared_6814_ == 0)
{
v___x_6816_ = v___x_6813_;
goto v_reusejp_6815_;
}
else
{
lean_object* v_reuseFailAlloc_6817_; 
v_reuseFailAlloc_6817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6817_, 0, v_a_6811_);
v___x_6816_ = v_reuseFailAlloc_6817_;
goto v_reusejp_6815_;
}
v_reusejp_6815_:
{
return v___x_6816_;
}
}
}
}
else
{
lean_dec_ref(v_b_6785_);
lean_dec_ref(v_a_6784_);
lean_dec(v_rName_6783_);
lean_dec(v_className_6782_);
return v___x_6791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6819_, lean_object* v_rName_6820_, lean_object* v_a_6821_, lean_object* v_b_6822_, lean_object* v_a_6823_, lean_object* v_a_6824_, lean_object* v_a_6825_, lean_object* v_a_6826_, lean_object* v_a_6827_){
_start:
{
lean_object* v_res_6828_; 
v_res_6828_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6819_, v_rName_6820_, v_a_6821_, v_b_6822_, v_a_6823_, v_a_6824_, v_a_6825_, v_a_6826_);
lean_dec(v_a_6826_);
lean_dec_ref(v_a_6825_);
lean_dec(v_a_6824_);
lean_dec_ref(v_a_6823_);
return v_res_6828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6831_, lean_object* v_b_6832_, lean_object* v_a_6833_, lean_object* v_a_6834_, lean_object* v_a_6835_, lean_object* v_a_6836_){
_start:
{
lean_object* v___x_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; 
v___x_6838_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6839_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6840_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6838_, v___x_6839_, v_a_6831_, v_b_6832_, v_a_6833_, v_a_6834_, v_a_6835_, v_a_6836_);
return v___x_6840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6841_, lean_object* v_b_6842_, lean_object* v_a_6843_, lean_object* v_a_6844_, lean_object* v_a_6845_, lean_object* v_a_6846_, lean_object* v_a_6847_){
_start:
{
lean_object* v_res_6848_; 
v_res_6848_ = l_Lean_Meta_mkLE(v_a_6841_, v_b_6842_, v_a_6843_, v_a_6844_, v_a_6845_, v_a_6846_);
lean_dec(v_a_6846_);
lean_dec_ref(v_a_6845_);
lean_dec(v_a_6844_);
lean_dec_ref(v_a_6843_);
return v_res_6848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6851_, lean_object* v_b_6852_, lean_object* v_a_6853_, lean_object* v_a_6854_, lean_object* v_a_6855_, lean_object* v_a_6856_){
_start:
{
lean_object* v___x_6858_; lean_object* v___x_6859_; lean_object* v___x_6860_; 
v___x_6858_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6859_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6860_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6858_, v___x_6859_, v_a_6851_, v_b_6852_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
return v___x_6860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6861_, lean_object* v_b_6862_, lean_object* v_a_6863_, lean_object* v_a_6864_, lean_object* v_a_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_){
_start:
{
lean_object* v_res_6868_; 
v_res_6868_ = l_Lean_Meta_mkLT(v_a_6861_, v_b_6862_, v_a_6863_, v_a_6864_, v_a_6865_, v_a_6866_);
lean_dec(v_a_6866_);
lean_dec_ref(v_a_6865_);
lean_dec(v_a_6864_);
lean_dec_ref(v_a_6863_);
return v_res_6868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_, lean_object* v_a_6878_){
_start:
{
lean_object* v___x_6880_; lean_object* v___x_6881_; uint8_t v___x_6882_; 
v___x_6880_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6881_ = lean_unsigned_to_nat(3u);
v___x_6882_ = l_Lean_Expr_isAppOfArity(v_h_6874_, v___x_6880_, v___x_6881_);
if (v___x_6882_ == 0)
{
lean_object* v___x_6883_; lean_object* v___x_6884_; lean_object* v___x_6885_; lean_object* v___x_6886_; lean_object* v___x_6887_; 
v___x_6883_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6884_ = lean_unsigned_to_nat(1u);
v___x_6885_ = lean_mk_empty_array_with_capacity(v___x_6884_);
v___x_6886_ = lean_array_push(v___x_6885_, v_h_6874_);
v___x_6887_ = l_Lean_Meta_mkAppM(v___x_6883_, v___x_6886_, v_a_6875_, v_a_6876_, v_a_6877_, v_a_6878_);
return v___x_6887_;
}
else
{
lean_object* v___x_6888_; lean_object* v___x_6889_; 
v___x_6888_ = l_Lean_Expr_appArg_x21(v_h_6874_);
lean_dec_ref(v_h_6874_);
v___x_6889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6889_, 0, v___x_6888_);
return v___x_6889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6890_, lean_object* v_a_6891_, lean_object* v_a_6892_, lean_object* v_a_6893_, lean_object* v_a_6894_, lean_object* v_a_6895_){
_start:
{
lean_object* v_res_6896_; 
v_res_6896_ = l_Lean_Meta_mkIffOfEq(v_h_6890_, v_a_6891_, v_a_6892_, v_a_6893_, v_a_6894_);
lean_dec(v_a_6894_);
lean_dec_ref(v_a_6893_);
lean_dec(v_a_6892_);
lean_dec_ref(v_a_6891_);
return v_res_6896_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6902_; lean_object* v___x_6903_; lean_object* v___x_6904_; 
v___x_6902_ = lean_box(0);
v___x_6903_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6904_ = l_Lean_mkConst(v___x_6903_, v___x_6902_);
return v___x_6904_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6907_; lean_object* v___x_6908_; lean_object* v___x_6909_; 
v___x_6907_ = lean_box(0);
v___x_6908_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6909_ = l_Lean_mkConst(v___x_6908_, v___x_6907_);
return v___x_6909_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6910_; lean_object* v___x_6911_; lean_object* v___x_6912_; 
v___x_6910_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6911_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6912_, 0, v___x_6911_);
lean_ctor_set(v___x_6912_, 1, v___x_6910_);
return v___x_6912_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6917_; lean_object* v___x_6918_; lean_object* v___x_6919_; 
v___x_6917_ = lean_box(0);
v___x_6918_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6919_ = l_Lean_mkConst(v___x_6918_, v___x_6917_);
return v___x_6919_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6922_; lean_object* v___x_6923_; lean_object* v___x_6924_; 
v___x_6922_ = lean_box(0);
v___x_6923_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6924_ = l_Lean_mkConst(v___x_6923_, v___x_6922_);
return v___x_6924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6925_, lean_object* v_a_6926_, lean_object* v_a_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_){
_start:
{
if (lean_obj_tag(v_a_6925_) == 0)
{
lean_object* v___x_6931_; lean_object* v___x_6932_; 
v___x_6931_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6932_, 0, v___x_6931_);
return v___x_6932_;
}
else
{
lean_object* v_tail_6933_; 
v_tail_6933_ = lean_ctor_get(v_a_6925_, 1);
if (lean_obj_tag(v_tail_6933_) == 0)
{
lean_object* v_head_6934_; lean_object* v___x_6936_; uint8_t v_isShared_6937_; uint8_t v_isSharedCheck_6958_; 
v_head_6934_ = lean_ctor_get(v_a_6925_, 0);
v_isSharedCheck_6958_ = !lean_is_exclusive(v_a_6925_);
if (v_isSharedCheck_6958_ == 0)
{
lean_object* v_unused_6959_; 
v_unused_6959_ = lean_ctor_get(v_a_6925_, 1);
lean_dec(v_unused_6959_);
v___x_6936_ = v_a_6925_;
v_isShared_6937_ = v_isSharedCheck_6958_;
goto v_resetjp_6935_;
}
else
{
lean_inc(v_head_6934_);
lean_dec(v_a_6925_);
v___x_6936_ = lean_box(0);
v_isShared_6937_ = v_isSharedCheck_6958_;
goto v_resetjp_6935_;
}
v_resetjp_6935_:
{
lean_object* v___x_6938_; 
lean_inc(v_a_6929_);
lean_inc_ref(v_a_6928_);
lean_inc(v_a_6927_);
lean_inc_ref(v_a_6926_);
lean_inc(v_head_6934_);
v___x_6938_ = lean_infer_type(v_head_6934_, v_a_6926_, v_a_6927_, v_a_6928_, v_a_6929_);
if (lean_obj_tag(v___x_6938_) == 0)
{
lean_object* v_a_6939_; lean_object* v___x_6941_; uint8_t v_isShared_6942_; uint8_t v_isSharedCheck_6949_; 
v_a_6939_ = lean_ctor_get(v___x_6938_, 0);
v_isSharedCheck_6949_ = !lean_is_exclusive(v___x_6938_);
if (v_isSharedCheck_6949_ == 0)
{
v___x_6941_ = v___x_6938_;
v_isShared_6942_ = v_isSharedCheck_6949_;
goto v_resetjp_6940_;
}
else
{
lean_inc(v_a_6939_);
lean_dec(v___x_6938_);
v___x_6941_ = lean_box(0);
v_isShared_6942_ = v_isSharedCheck_6949_;
goto v_resetjp_6940_;
}
v_resetjp_6940_:
{
lean_object* v___x_6944_; 
if (v_isShared_6937_ == 0)
{
lean_ctor_set_tag(v___x_6936_, 0);
lean_ctor_set(v___x_6936_, 1, v_a_6939_);
v___x_6944_ = v___x_6936_;
goto v_reusejp_6943_;
}
else
{
lean_object* v_reuseFailAlloc_6948_; 
v_reuseFailAlloc_6948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_head_6934_);
lean_ctor_set(v_reuseFailAlloc_6948_, 1, v_a_6939_);
v___x_6944_ = v_reuseFailAlloc_6948_;
goto v_reusejp_6943_;
}
v_reusejp_6943_:
{
lean_object* v___x_6946_; 
if (v_isShared_6942_ == 0)
{
lean_ctor_set(v___x_6941_, 0, v___x_6944_);
v___x_6946_ = v___x_6941_;
goto v_reusejp_6945_;
}
else
{
lean_object* v_reuseFailAlloc_6947_; 
v_reuseFailAlloc_6947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6947_, 0, v___x_6944_);
v___x_6946_ = v_reuseFailAlloc_6947_;
goto v_reusejp_6945_;
}
v_reusejp_6945_:
{
return v___x_6946_;
}
}
}
}
else
{
lean_object* v_a_6950_; lean_object* v___x_6952_; uint8_t v_isShared_6953_; uint8_t v_isSharedCheck_6957_; 
lean_del_object(v___x_6936_);
lean_dec(v_head_6934_);
v_a_6950_ = lean_ctor_get(v___x_6938_, 0);
v_isSharedCheck_6957_ = !lean_is_exclusive(v___x_6938_);
if (v_isSharedCheck_6957_ == 0)
{
v___x_6952_ = v___x_6938_;
v_isShared_6953_ = v_isSharedCheck_6957_;
goto v_resetjp_6951_;
}
else
{
lean_inc(v_a_6950_);
lean_dec(v___x_6938_);
v___x_6952_ = lean_box(0);
v_isShared_6953_ = v_isSharedCheck_6957_;
goto v_resetjp_6951_;
}
v_resetjp_6951_:
{
lean_object* v___x_6955_; 
if (v_isShared_6953_ == 0)
{
v___x_6955_ = v___x_6952_;
goto v_reusejp_6954_;
}
else
{
lean_object* v_reuseFailAlloc_6956_; 
v_reuseFailAlloc_6956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6956_, 0, v_a_6950_);
v___x_6955_ = v_reuseFailAlloc_6956_;
goto v_reusejp_6954_;
}
v_reusejp_6954_:
{
return v___x_6955_;
}
}
}
}
}
else
{
lean_object* v_head_6960_; lean_object* v___x_6961_; 
lean_inc(v_tail_6933_);
v_head_6960_ = lean_ctor_get(v_a_6925_, 0);
lean_inc(v_head_6960_);
lean_dec_ref_known(v_a_6925_, 2);
v___x_6961_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6933_, v_a_6926_, v_a_6927_, v_a_6928_, v_a_6929_);
if (lean_obj_tag(v___x_6961_) == 0)
{
lean_object* v_a_6962_; lean_object* v_fst_6963_; lean_object* v_snd_6964_; lean_object* v___x_6966_; uint8_t v_isShared_6967_; uint8_t v_isSharedCheck_6992_; 
v_a_6962_ = lean_ctor_get(v___x_6961_, 0);
lean_inc(v_a_6962_);
lean_dec_ref_known(v___x_6961_, 1);
v_fst_6963_ = lean_ctor_get(v_a_6962_, 0);
v_snd_6964_ = lean_ctor_get(v_a_6962_, 1);
v_isSharedCheck_6992_ = !lean_is_exclusive(v_a_6962_);
if (v_isSharedCheck_6992_ == 0)
{
v___x_6966_ = v_a_6962_;
v_isShared_6967_ = v_isSharedCheck_6992_;
goto v_resetjp_6965_;
}
else
{
lean_inc(v_snd_6964_);
lean_inc(v_fst_6963_);
lean_dec(v_a_6962_);
v___x_6966_ = lean_box(0);
v_isShared_6967_ = v_isSharedCheck_6992_;
goto v_resetjp_6965_;
}
v_resetjp_6965_:
{
lean_object* v___x_6968_; 
lean_inc(v_a_6929_);
lean_inc_ref(v_a_6928_);
lean_inc(v_a_6927_);
lean_inc_ref(v_a_6926_);
lean_inc(v_head_6960_);
v___x_6968_ = lean_infer_type(v_head_6960_, v_a_6926_, v_a_6927_, v_a_6928_, v_a_6929_);
if (lean_obj_tag(v___x_6968_) == 0)
{
lean_object* v_a_6969_; lean_object* v___x_6971_; uint8_t v_isShared_6972_; uint8_t v_isSharedCheck_6983_; 
v_a_6969_ = lean_ctor_get(v___x_6968_, 0);
v_isSharedCheck_6983_ = !lean_is_exclusive(v___x_6968_);
if (v_isSharedCheck_6983_ == 0)
{
v___x_6971_ = v___x_6968_;
v_isShared_6972_ = v_isSharedCheck_6983_;
goto v_resetjp_6970_;
}
else
{
lean_inc(v_a_6969_);
lean_dec(v___x_6968_);
v___x_6971_ = lean_box(0);
v_isShared_6972_ = v_isSharedCheck_6983_;
goto v_resetjp_6970_;
}
v_resetjp_6970_:
{
lean_object* v___x_6973_; lean_object* v___x_6974_; lean_object* v___x_6975_; lean_object* v___x_6976_; lean_object* v___x_6978_; 
v___x_6973_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6964_);
lean_inc(v_a_6969_);
v___x_6974_ = l_Lean_mkApp4(v___x_6973_, v_a_6969_, v_snd_6964_, v_head_6960_, v_fst_6963_);
v___x_6975_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6976_ = l_Lean_mkAppB(v___x_6975_, v_a_6969_, v_snd_6964_);
if (v_isShared_6967_ == 0)
{
lean_ctor_set(v___x_6966_, 1, v___x_6976_);
lean_ctor_set(v___x_6966_, 0, v___x_6974_);
v___x_6978_ = v___x_6966_;
goto v_reusejp_6977_;
}
else
{
lean_object* v_reuseFailAlloc_6982_; 
v_reuseFailAlloc_6982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6982_, 0, v___x_6974_);
lean_ctor_set(v_reuseFailAlloc_6982_, 1, v___x_6976_);
v___x_6978_ = v_reuseFailAlloc_6982_;
goto v_reusejp_6977_;
}
v_reusejp_6977_:
{
lean_object* v___x_6980_; 
if (v_isShared_6972_ == 0)
{
lean_ctor_set(v___x_6971_, 0, v___x_6978_);
v___x_6980_ = v___x_6971_;
goto v_reusejp_6979_;
}
else
{
lean_object* v_reuseFailAlloc_6981_; 
v_reuseFailAlloc_6981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6981_, 0, v___x_6978_);
v___x_6980_ = v_reuseFailAlloc_6981_;
goto v_reusejp_6979_;
}
v_reusejp_6979_:
{
return v___x_6980_;
}
}
}
}
else
{
lean_object* v_a_6984_; lean_object* v___x_6986_; uint8_t v_isShared_6987_; uint8_t v_isSharedCheck_6991_; 
lean_del_object(v___x_6966_);
lean_dec(v_snd_6964_);
lean_dec(v_fst_6963_);
lean_dec(v_head_6960_);
v_a_6984_ = lean_ctor_get(v___x_6968_, 0);
v_isSharedCheck_6991_ = !lean_is_exclusive(v___x_6968_);
if (v_isSharedCheck_6991_ == 0)
{
v___x_6986_ = v___x_6968_;
v_isShared_6987_ = v_isSharedCheck_6991_;
goto v_resetjp_6985_;
}
else
{
lean_inc(v_a_6984_);
lean_dec(v___x_6968_);
v___x_6986_ = lean_box(0);
v_isShared_6987_ = v_isSharedCheck_6991_;
goto v_resetjp_6985_;
}
v_resetjp_6985_:
{
lean_object* v___x_6989_; 
if (v_isShared_6987_ == 0)
{
v___x_6989_ = v___x_6986_;
goto v_reusejp_6988_;
}
else
{
lean_object* v_reuseFailAlloc_6990_; 
v_reuseFailAlloc_6990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6990_, 0, v_a_6984_);
v___x_6989_ = v_reuseFailAlloc_6990_;
goto v_reusejp_6988_;
}
v_reusejp_6988_:
{
return v___x_6989_;
}
}
}
}
}
else
{
lean_dec(v_head_6960_);
return v___x_6961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6993_, lean_object* v_a_6994_, lean_object* v_a_6995_, lean_object* v_a_6996_, lean_object* v_a_6997_, lean_object* v_a_6998_){
_start:
{
lean_object* v_res_6999_; 
v_res_6999_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6993_, v_a_6994_, v_a_6995_, v_a_6996_, v_a_6997_);
lean_dec(v_a_6997_);
lean_dec_ref(v_a_6996_);
lean_dec(v_a_6995_);
lean_dec_ref(v_a_6994_);
return v_res_6999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_7000_, lean_object* v_a_7001_, lean_object* v_a_7002_, lean_object* v_a_7003_, lean_object* v_a_7004_){
_start:
{
lean_object* v___x_7006_; 
v___x_7006_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_7000_, v_a_7001_, v_a_7002_, v_a_7003_, v_a_7004_);
if (lean_obj_tag(v___x_7006_) == 0)
{
lean_object* v_a_7007_; lean_object* v___x_7009_; uint8_t v_isShared_7010_; uint8_t v_isSharedCheck_7015_; 
v_a_7007_ = lean_ctor_get(v___x_7006_, 0);
v_isSharedCheck_7015_ = !lean_is_exclusive(v___x_7006_);
if (v_isSharedCheck_7015_ == 0)
{
v___x_7009_ = v___x_7006_;
v_isShared_7010_ = v_isSharedCheck_7015_;
goto v_resetjp_7008_;
}
else
{
lean_inc(v_a_7007_);
lean_dec(v___x_7006_);
v___x_7009_ = lean_box(0);
v_isShared_7010_ = v_isSharedCheck_7015_;
goto v_resetjp_7008_;
}
v_resetjp_7008_:
{
lean_object* v_fst_7011_; lean_object* v___x_7013_; 
v_fst_7011_ = lean_ctor_get(v_a_7007_, 0);
lean_inc(v_fst_7011_);
lean_dec(v_a_7007_);
if (v_isShared_7010_ == 0)
{
lean_ctor_set(v___x_7009_, 0, v_fst_7011_);
v___x_7013_ = v___x_7009_;
goto v_reusejp_7012_;
}
else
{
lean_object* v_reuseFailAlloc_7014_; 
v_reuseFailAlloc_7014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7014_, 0, v_fst_7011_);
v___x_7013_ = v_reuseFailAlloc_7014_;
goto v_reusejp_7012_;
}
v_reusejp_7012_:
{
return v___x_7013_;
}
}
}
else
{
lean_object* v_a_7016_; lean_object* v___x_7018_; uint8_t v_isShared_7019_; uint8_t v_isSharedCheck_7023_; 
v_a_7016_ = lean_ctor_get(v___x_7006_, 0);
v_isSharedCheck_7023_ = !lean_is_exclusive(v___x_7006_);
if (v_isSharedCheck_7023_ == 0)
{
v___x_7018_ = v___x_7006_;
v_isShared_7019_ = v_isSharedCheck_7023_;
goto v_resetjp_7017_;
}
else
{
lean_inc(v_a_7016_);
lean_dec(v___x_7006_);
v___x_7018_ = lean_box(0);
v_isShared_7019_ = v_isSharedCheck_7023_;
goto v_resetjp_7017_;
}
v_resetjp_7017_:
{
lean_object* v___x_7021_; 
if (v_isShared_7019_ == 0)
{
v___x_7021_ = v___x_7018_;
goto v_reusejp_7020_;
}
else
{
lean_object* v_reuseFailAlloc_7022_; 
v_reuseFailAlloc_7022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7022_, 0, v_a_7016_);
v___x_7021_ = v_reuseFailAlloc_7022_;
goto v_reusejp_7020_;
}
v_reusejp_7020_:
{
return v___x_7021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_7024_, lean_object* v_a_7025_, lean_object* v_a_7026_, lean_object* v_a_7027_, lean_object* v_a_7028_, lean_object* v_a_7029_){
_start:
{
lean_object* v_res_7030_; 
v_res_7030_ = l_Lean_Meta_mkAndIntroN(v_hs_7024_, v_a_7025_, v_a_7026_, v_a_7027_, v_a_7028_);
lean_dec(v_a_7028_);
lean_dec_ref(v_a_7027_);
lean_dec(v_a_7026_);
lean_dec_ref(v_a_7025_);
return v_res_7030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7087_; uint8_t v___x_7088_; lean_object* v___x_7089_; lean_object* v___x_7090_; 
v___x_7087_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7088_ = 0;
v___x_7089_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7090_ = l_Lean_registerTraceClass(v___x_7087_, v___x_7088_, v___x_7089_);
if (lean_obj_tag(v___x_7090_) == 0)
{
lean_object* v___x_7091_; uint8_t v___x_7092_; lean_object* v___x_7093_; 
lean_dec_ref_known(v___x_7090_, 1);
v___x_7091_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7092_ = 1;
v___x_7093_ = l_Lean_registerTraceClass(v___x_7091_, v___x_7092_, v___x_7089_);
if (lean_obj_tag(v___x_7093_) == 0)
{
lean_object* v___x_7094_; lean_object* v___x_7095_; 
lean_dec_ref_known(v___x_7093_, 1);
v___x_7094_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7095_ = l_Lean_registerTraceClass(v___x_7094_, v___x_7092_, v___x_7089_);
return v___x_7095_;
}
else
{
return v___x_7093_;
}
}
else
{
return v___x_7090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7096_){
_start:
{
lean_object* v_res_7097_; 
v_res_7097_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7097_;
}
}
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasAssignableMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_AppBuilder(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasAssignableMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_AppBuilder(builtin);
}
#ifdef __cplusplus
}
#endif
