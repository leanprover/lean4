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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
size_t v_x_1975__boxed_1677_; size_t v_x_1976__boxed_1678_; lean_object* v_res_1679_; 
v_x_1975__boxed_1677_ = lean_unbox_usize(v_x_1673_);
lean_dec(v_x_1673_);
v_x_1976__boxed_1678_ = lean_unbox_usize(v_x_1674_);
lean_dec(v_x_1674_);
v_res_1679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1672_, v_x_1975__boxed_1677_, v_x_1976__boxed_1678_, v_x_1675_, v_x_1676_);
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
lean_object* v___x_1691_; lean_object* v_mctx_1692_; lean_object* v_cache_1693_; lean_object* v_zetaDeltaFVarIds_1694_; lean_object* v_postponed_1695_; lean_object* v_diag_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1726_; 
v___x_1691_ = lean_st_ref_take(v___y_1689_);
v_mctx_1692_ = lean_ctor_get(v___x_1691_, 0);
v_cache_1693_ = lean_ctor_get(v___x_1691_, 1);
v_zetaDeltaFVarIds_1694_ = lean_ctor_get(v___x_1691_, 2);
v_postponed_1695_ = lean_ctor_get(v___x_1691_, 3);
v_diag_1696_ = lean_ctor_get(v___x_1691_, 4);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1698_ = v___x_1691_;
v_isShared_1699_ = v_isSharedCheck_1726_;
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
v_isShared_1699_ = v_isSharedCheck_1726_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_depth_1700_; lean_object* v_levelAssignDepth_1701_; lean_object* v_lmvarCounter_1702_; lean_object* v_mvarCounter_1703_; lean_object* v_lDecls_1704_; lean_object* v_decls_1705_; lean_object* v_userNames_1706_; lean_object* v_lAssignment_1707_; lean_object* v_eAssignment_1708_; lean_object* v_dAssignment_1709_; lean_object* v_instanceTypedMVars_1710_; lean_object* v_synthNormMemo_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1725_; 
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
v_synthNormMemo_1711_ = lean_ctor_get(v_mctx_1692_, 11);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_mctx_1692_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1713_ = v_mctx_1692_;
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_synthNormMemo_1711_);
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
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1715_ = lean_box(0);
v___x_1716_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_eAssignment_1708_, v_mvarId_1687_, v_val_1688_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 8, v___x_1716_);
v___x_1718_ = v___x_1713_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_depth_1700_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_levelAssignDepth_1701_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_lmvarCounter_1702_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_mvarCounter_1703_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_lDecls_1704_);
lean_ctor_set(v_reuseFailAlloc_1724_, 5, v_decls_1705_);
lean_ctor_set(v_reuseFailAlloc_1724_, 6, v_userNames_1706_);
lean_ctor_set(v_reuseFailAlloc_1724_, 7, v_lAssignment_1707_);
lean_ctor_set(v_reuseFailAlloc_1724_, 8, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1724_, 9, v_dAssignment_1709_);
lean_ctor_set(v_reuseFailAlloc_1724_, 10, v_instanceTypedMVars_1710_);
lean_ctor_set(v_reuseFailAlloc_1724_, 11, v_synthNormMemo_1711_);
v___x_1718_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1718_);
v___x_1720_ = v___x_1698_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_cache_1693_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_zetaDeltaFVarIds_1694_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_postponed_1695_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_diag_1696_);
v___x_1720_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_st_ref_put(v___y_1689_, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1715_);
return v___x_1722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg___boxed(lean_object* v_mvarId_1727_, lean_object* v_val_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1727_, v_val_1728_, v___y_1729_);
lean_dec(v___y_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(lean_object* v_as_1732_, size_t v_i_1733_, size_t v_stop_1734_, lean_object* v_b_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_eq(v_i_1733_, v_stop_1734_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_array_uget_borrowed(v_as_1732_, v_i_1733_);
lean_inc(v___x_1742_);
v___x_1743_ = l_Lean_MVarId_getDecl(v___x_1742_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_type_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v_type_1745_ = lean_ctor_get(v_a_1744_, 2);
lean_inc_ref(v_type_1745_);
lean_dec(v_a_1744_);
v___x_1746_ = lean_box(0);
v___x_1747_ = l_Lean_Meta_synthInstance(v_type_1745_, v___x_1746_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
lean_inc(v___x_1742_);
v___x_1749_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v___x_1742_, v_a_1748_, v___y_1737_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; size_t v___x_1751_; size_t v___x_1752_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1733_, v___x_1751_);
v_i_1733_ = v___x_1752_;
v_b_1735_ = v_a_1750_;
goto _start;
}
else
{
return v___x_1749_;
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1747_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1747_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_a_1762_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1743_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1743_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_b_1735_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2___boxed(lean_object* v_as_1771_, lean_object* v_i_1772_, lean_object* v_stop_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
size_t v_i_boxed_1780_; size_t v_stop_boxed_1781_; lean_object* v_res_1782_; 
v_i_boxed_1780_ = lean_unbox_usize(v_i_1772_);
lean_dec(v_i_1772_);
v_stop_boxed_1781_ = lean_unbox_usize(v_stop_1773_);
lean_dec(v_stop_1773_);
v_res_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_as_1771_, v_i_boxed_1780_, v_stop_boxed_1781_, v_b_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_as_1771_);
return v_res_1782_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1));
v___x_1787_ = l_Lean_MessageData_ofFormat(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object* v_methodName_1788_, lean_object* v_f_1789_, lean_object* v_args_1790_, lean_object* v_instMVars_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___y_1832_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_array_get_size(v_instMVars_1791_);
v___x_1843_ = lean_nat_dec_lt(v___x_1841_, v___x_1842_);
if (v___x_1843_ == 0)
{
goto v___jp_1797_;
}
else
{
lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_nat_dec_le(v___x_1842_, v___x_1842_);
if (v___x_1845_ == 0)
{
if (v___x_1843_ == 0)
{
goto v___jp_1797_;
}
else
{
size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = ((size_t)0ULL);
v___x_1847_ = lean_usize_of_nat(v___x_1842_);
v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1791_, v___x_1846_, v___x_1847_, v___x_1844_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
v___y_1832_ = v___x_1848_;
goto v___jp_1831_;
}
}
else
{
size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = lean_usize_of_nat(v___x_1842_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1791_, v___x_1849_, v___x_1850_, v___x_1844_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
v___y_1832_ = v___x_1851_;
goto v___jp_1831_;
}
}
v___jp_1797_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_a_1800_; lean_object* v___x_1801_; 
v___x_1798_ = l_Lean_mkAppN(v_f_1789_, v_args_1790_);
v___x_1799_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v___x_1798_, v_a_1793_);
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc_n(v_a_1800_, 2);
lean_dec_ref(v___x_1799_);
v___x_1801_ = l_Lean_Meta_hasAssignableMVar(v_a_1800_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1822_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1822_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1822_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_unbox(v_a_1802_);
lean_dec(v_a_1802_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1808_; 
lean_dec(v_methodName_1788_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_a_1800_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1800_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_del_object(v___x_1804_);
v___x_1810_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2);
v___x_1811_ = l_Lean_indentExpr(v_a_1800_);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_methodName_1788_, v___x_1812_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_a_1800_);
lean_dec(v_methodName_1788_);
v_a_1823_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1801_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1801_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
v___jp_1831_:
{
if (lean_obj_tag(v___y_1832_) == 0)
{
lean_dec_ref_known(v___y_1832_, 1);
goto v___jp_1797_;
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v_f_1789_);
lean_dec(v_methodName_1788_);
v_a_1833_ = lean_ctor_get(v___y_1832_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___y_1832_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___y_1832_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___y_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* v_methodName_1852_, lean_object* v_f_1853_, lean_object* v_args_1854_, lean_object* v_instMVars_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v_methodName_1852_, v_f_1853_, v_args_1854_, v_instMVars_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec_ref(v_instMVars_1855_);
lean_dec_ref(v_args_1854_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object* v_mvarId_1862_, lean_object* v_val_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1862_, v_val_1863_, v___y_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object* v_mvarId_1870_, lean_object* v_val_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(v_mvarId_1870_, v_val_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object* v_00_u03b2_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_x_1879_, v_x_1880_, v_x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1883_, lean_object* v_x_1884_, size_t v_x_1885_, size_t v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1884_, v_x_1885_, v_x_1886_, v_x_1887_, v_x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
size_t v_x_2415__boxed_1896_; size_t v_x_2416__boxed_1897_; lean_object* v_res_1898_; 
v_x_2415__boxed_1896_ = lean_unbox_usize(v_x_1892_);
lean_dec(v_x_1892_);
v_x_2416__boxed_1897_ = lean_unbox_usize(v_x_1893_);
lean_dec(v_x_1893_);
v_res_1898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1890_, v_x_1891_, v_x_2415__boxed_1896_, v_x_2416__boxed_1897_, v_x_1894_, v_x_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1899_, lean_object* v_n_1900_, lean_object* v_k_1901_, lean_object* v_v_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1900_, v_k_1901_, v_v_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1904_, size_t v_depth_1905_, lean_object* v_keys_1906_, lean_object* v_vals_1907_, lean_object* v_heq_1908_, lean_object* v_i_1909_, lean_object* v_entries_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1905_, v_keys_1906_, v_vals_1907_, v_i_1909_, v_entries_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1912_, lean_object* v_depth_1913_, lean_object* v_keys_1914_, lean_object* v_vals_1915_, lean_object* v_heq_1916_, lean_object* v_i_1917_, lean_object* v_entries_1918_){
_start:
{
size_t v_depth_boxed_1919_; lean_object* v_res_1920_; 
v_depth_boxed_1919_ = lean_unbox_usize(v_depth_1913_);
lean_dec(v_depth_1913_);
v_res_1920_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1912_, v_depth_boxed_1919_, v_keys_1914_, v_vals_1915_, v_heq_1916_, v_i_1917_, v_entries_1918_);
lean_dec_ref(v_vals_1915_);
lean_dec_ref(v_keys_1914_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1922_, v_x_1923_, v_x_1924_, v_x_1925_);
return v___x_1926_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2));
v___x_1932_ = l_Lean_stringToMessageData(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4));
v___x_1935_ = l_Lean_stringToMessageData(v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7));
v___x_1940_ = l_Lean_MessageData_ofFormat(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* v_f_1941_, lean_object* v_xs_1942_, lean_object* v_type_1943_, lean_object* v_i_1944_, lean_object* v_j_1945_, lean_object* v_args_1946_, lean_object* v_instMVars_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1953_ = lean_array_get_size(v_xs_1942_);
v___x_1954_ = lean_nat_dec_le(v___x_1953_, v_i_1944_);
if (v___x_1954_ == 0)
{
if (lean_obj_tag(v_type_1943_) == 7)
{
lean_object* v_binderName_1955_; lean_object* v_binderType_1956_; lean_object* v_body_1957_; uint8_t v_binderInfo_1958_; lean_object* v___x_1959_; lean_object* v_d_1960_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; 
v_binderName_1955_ = lean_ctor_get(v_type_1943_, 0);
lean_inc(v_binderName_1955_);
v_binderType_1956_ = lean_ctor_get(v_type_1943_, 1);
lean_inc_ref(v_binderType_1956_);
v_body_1957_ = lean_ctor_get(v_type_1943_, 2);
lean_inc_ref(v_body_1957_);
v_binderInfo_1958_ = lean_ctor_get_uint8(v_type_1943_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1943_, 3);
v___x_1959_ = lean_array_get_size(v_args_1946_);
v_d_1960_ = lean_expr_instantiate_rev_range(v_binderType_1956_, v_j_1945_, v___x_1959_, v_args_1946_);
lean_dec_ref(v_binderType_1956_);
switch(v_binderInfo_1958_)
{
case 1:
{
v___y_1962_ = v_a_1948_;
v___y_1963_ = v_a_1949_;
v___y_1964_ = v_a_1950_;
v___y_1965_ = v_a_1951_;
goto v___jp_1961_;
}
case 2:
{
v___y_1962_ = v_a_1948_;
v___y_1963_ = v_a_1949_;
v___y_1964_ = v_a_1950_;
v___y_1965_ = v_a_1951_;
goto v___jp_1961_;
}
case 3:
{
lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_d_1960_);
v___x_1973_ = 1;
v___x_1974_ = l_Lean_Meta_mkFreshExprMVar(v___x_1972_, v___x_1973_, v_binderName_1955_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc_n(v_a_1975_, 2);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = lean_array_push(v_args_1946_, v_a_1975_);
v___x_1977_ = l_Lean_Expr_mvarId_x21(v_a_1975_);
lean_dec(v_a_1975_);
v___x_1978_ = lean_array_push(v_instMVars_1947_, v___x_1977_);
v_type_1943_ = v_body_1957_;
v_args_1946_ = v___x_1976_;
v_instMVars_1947_ = v___x_1978_;
goto _start;
}
else
{
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_instMVars_1947_);
lean_dec_ref(v_args_1946_);
lean_dec(v_j_1945_);
lean_dec(v_i_1944_);
lean_dec_ref(v_f_1941_);
return v___x_1974_;
}
}
default: 
{
lean_object* v_x_1980_; lean_object* v___y_1982_; lean_object* v___x_1999_; 
lean_dec(v_binderName_1955_);
v_x_1980_ = lean_array_fget_borrowed(v_xs_1942_, v_i_1944_);
lean_inc(v_a_1951_);
lean_inc_ref(v_a_1950_);
lean_inc(v_a_1949_);
lean_inc_ref(v_a_1948_);
lean_inc(v_x_1980_);
v___x_1999_ = lean_infer_type(v_x_1980_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; uint8_t v_transparency_2002_; uint8_t v___x_2003_; uint8_t v___x_2004_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = l_Lean_Meta_Context_config(v_a_1948_);
v_transparency_2002_ = lean_ctor_get_uint8(v___x_2001_, 9);
lean_dec_ref(v___x_2001_);
v___x_2003_ = 1;
v___x_2004_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Meta_isExprDefEq(v_d_1960_, v_a_2000_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
v___y_1982_ = v___x_2005_;
goto v___jp_1981_;
}
else
{
lean_object* v_keyedConfig_2006_; uint8_t v_trackZetaDelta_2007_; lean_object* v_zetaDeltaSet_2008_; lean_object* v_lctx_2009_; lean_object* v_localInstances_2010_; lean_object* v_defEqCtx_x3f_2011_; lean_object* v_synthPendingDepth_2012_; lean_object* v_customCanUnfoldPredicate_x3f_2013_; uint8_t v_univApprox_2014_; uint8_t v_inTypeClassResolution_2015_; uint8_t v_cacheInferType_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_keyedConfig_2006_ = lean_ctor_get(v_a_1948_, 0);
v_trackZetaDelta_2007_ = lean_ctor_get_uint8(v_a_1948_, sizeof(void*)*7);
v_zetaDeltaSet_2008_ = lean_ctor_get(v_a_1948_, 1);
v_lctx_2009_ = lean_ctor_get(v_a_1948_, 2);
v_localInstances_2010_ = lean_ctor_get(v_a_1948_, 3);
v_defEqCtx_x3f_2011_ = lean_ctor_get(v_a_1948_, 4);
v_synthPendingDepth_2012_ = lean_ctor_get(v_a_1948_, 5);
v_customCanUnfoldPredicate_x3f_2013_ = lean_ctor_get(v_a_1948_, 6);
v_univApprox_2014_ = lean_ctor_get_uint8(v_a_1948_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2015_ = lean_ctor_get_uint8(v_a_1948_, sizeof(void*)*7 + 2);
v_cacheInferType_2016_ = lean_ctor_get_uint8(v_a_1948_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2006_);
v___x_2017_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2003_, v_keyedConfig_2006_);
lean_inc(v_customCanUnfoldPredicate_x3f_2013_);
lean_inc(v_synthPendingDepth_2012_);
lean_inc(v_defEqCtx_x3f_2011_);
lean_inc_ref(v_localInstances_2010_);
lean_inc_ref(v_lctx_2009_);
lean_inc(v_zetaDeltaSet_2008_);
v___x_2018_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_ctor_set(v___x_2018_, 1, v_zetaDeltaSet_2008_);
lean_ctor_set(v___x_2018_, 2, v_lctx_2009_);
lean_ctor_set(v___x_2018_, 3, v_localInstances_2010_);
lean_ctor_set(v___x_2018_, 4, v_defEqCtx_x3f_2011_);
lean_ctor_set(v___x_2018_, 5, v_synthPendingDepth_2012_);
lean_ctor_set(v___x_2018_, 6, v_customCanUnfoldPredicate_x3f_2013_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*7, v_trackZetaDelta_2007_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*7 + 1, v_univApprox_2014_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2015_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*7 + 3, v_cacheInferType_2016_);
v___x_2019_ = l_Lean_Meta_isExprDefEq(v_d_1960_, v_a_2000_, v___x_2018_, v_a_1949_, v_a_1950_, v_a_1951_);
lean_dec_ref_known(v___x_2018_, 7);
v___y_1982_ = v___x_2019_;
goto v___jp_1981_;
}
}
else
{
lean_dec_ref(v_d_1960_);
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_instMVars_1947_);
lean_dec_ref(v_args_1946_);
lean_dec(v_j_1945_);
lean_dec(v_i_1944_);
lean_dec_ref(v_f_1941_);
return v___x_1999_;
}
v___jp_1981_:
{
if (lean_obj_tag(v___y_1982_) == 0)
{
lean_object* v_a_1983_; uint8_t v___x_1984_; 
v_a_1983_ = lean_ctor_get(v___y_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___y_1982_, 1);
v___x_1984_ = lean_unbox(v_a_1983_);
lean_dec(v_a_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_instMVars_1947_);
lean_dec(v_j_1945_);
lean_dec(v_i_1944_);
v___x_1985_ = l_Lean_mkAppN(v_f_1941_, v_args_1946_);
lean_dec_ref(v_args_1946_);
lean_inc(v_x_1980_);
v___x_1986_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1985_, v_x_1980_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
return v___x_1986_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_add(v_i_1944_, v___x_1987_);
lean_dec(v_i_1944_);
lean_inc(v_x_1980_);
v___x_1989_ = lean_array_push(v_args_1946_, v_x_1980_);
v_type_1943_ = v_body_1957_;
v_i_1944_ = v___x_1988_;
v_args_1946_ = v___x_1989_;
goto _start;
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_instMVars_1947_);
lean_dec_ref(v_args_1946_);
lean_dec(v_j_1945_);
lean_dec(v_i_1944_);
lean_dec_ref(v_f_1941_);
v_a_1991_ = lean_ctor_get(v___y_1982_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___y_1982_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___y_1982_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___y_1982_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
v___jp_1961_:
{
lean_object* v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_d_1960_);
v___x_1967_ = 0;
v___x_1968_ = l_Lean_Meta_mkFreshExprMVar(v___x_1966_, v___x_1967_, v_binderName_1955_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = lean_array_push(v_args_1946_, v_a_1969_);
v_type_1943_ = v_body_1957_;
v_args_1946_ = v___x_1970_;
v_a_1948_ = v___y_1962_;
v_a_1949_ = v___y_1963_;
v_a_1950_ = v___y_1964_;
v_a_1951_ = v___y_1965_;
goto _start;
}
else
{
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_instMVars_1947_);
lean_dec_ref(v_args_1946_);
lean_dec(v_j_1945_);
lean_dec(v_i_1944_);
lean_dec_ref(v_f_1941_);
return v___x_1968_;
}
}
}
else
{
lean_object* v___x_2020_; lean_object* v_type_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_array_get_size(v_args_1946_);
v_type_2021_ = lean_expr_instantiate_rev_range(v_type_1943_, v_j_1945_, v___x_2020_, v_args_1946_);
lean_dec(v_j_1945_);
lean_dec_ref(v_type_1943_);
v___x_2022_ = l_Lean_Meta_whnfD(v_type_2021_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; uint8_t v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = l_Lean_Expr_isForall(v_a_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec(v_a_2023_);
lean_dec_ref(v_instMVars_1947_);
lean_dec_ref(v_args_1946_);
lean_dec(v_i_1944_);
v___x_2025_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2027_ = l_Lean_indentExpr(v_f_1941_);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2033_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1942_, v___x_2031_, v___x_2032_);
v___x_2034_ = l_Lean_indentD(v___x_2033_);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2030_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_2025_, v___x_2035_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
return v___x_2036_;
}
else
{
v_type_1943_ = v_a_2023_;
v_j_1945_ = v___x_2020_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1947_);
lean_dec_ref(v_args_1946_);
lean_dec(v_i_1944_);
lean_dec_ref(v_f_1941_);
return v___x_2022_;
}
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v_j_1945_);
lean_dec(v_i_1944_);
lean_dec_ref(v_type_1943_);
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2039_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2038_, v_f_1941_, v_args_1946_, v_instMVars_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
lean_dec_ref(v_instMVars_1947_);
lean_dec_ref(v_args_1946_);
return v___x_2039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* v_f_2040_, lean_object* v_xs_2041_, lean_object* v_type_2042_, lean_object* v_i_2043_, lean_object* v_j_2044_, lean_object* v_args_2045_, lean_object* v_instMVars_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2040_, v_xs_2041_, v_type_2042_, v_i_2043_, v_j_2044_, v_args_2045_, v_instMVars_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec_ref(v_xs_2041_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* v_f_2055_, lean_object* v_fType_2056_, lean_object* v_xs_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_2065_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2055_, v_xs_2057_, v_fType_2056_, v___x_2063_, v___x_2063_, v___x_2064_, v___x_2064_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* v_f_2066_, lean_object* v_fType_2067_, lean_object* v_xs_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_f_2066_, v_fType_2067_, v_xs_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec_ref(v_xs_2068_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object* v_x_2075_, lean_object* v_x_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
if (lean_obj_tag(v_x_2075_) == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = l_List_reverse___redArg(v_x_2076_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
else
{
lean_object* v_tail_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2102_; 
v_tail_2084_ = lean_ctor_get(v_x_2075_, 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_x_2075_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; 
v_unused_2103_ = lean_ctor_get(v_x_2075_, 0);
lean_dec(v_unused_2103_);
v___x_2086_ = v_x_2075_;
v_isShared_2087_ = v_isSharedCheck_2102_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_tail_2084_);
lean_dec(v_x_2075_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2102_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_mkFreshLevelMVar(v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v_x_2076_);
lean_ctor_set(v___x_2086_, 0, v_a_2089_);
v___x_2091_ = v___x_2086_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2089_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_x_2076_);
v___x_2091_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
v_x_2075_ = v_tail_2084_;
v_x_2076_ = v___x_2091_;
goto _start;
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_del_object(v___x_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_x_2076_);
v_a_2094_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2088_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2088_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object* v_x_2104_, lean_object* v_x_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_x_2104_, v_x_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2115_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2116_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
lean_ctor_set(v___x_2118_, 2, v___x_2117_);
lean_ctor_set(v___x_2118_, 3, v___x_2117_);
lean_ctor_set(v___x_2118_, 4, v___x_2116_);
lean_ctor_set(v___x_2118_, 5, v___x_2116_);
lean_ctor_set(v___x_2118_, 6, v___x_2116_);
lean_ctor_set(v___x_2118_, 7, v___x_2116_);
lean_ctor_set(v___x_2118_, 8, v___x_2116_);
lean_ctor_set(v___x_2118_, 9, v___x_2116_);
lean_ctor_set(v___x_2118_, 10, v___x_2116_);
lean_ctor_set(v___x_2118_, 11, v___x_2115_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = lean_unsigned_to_nat(32u);
v___x_2120_ = lean_mk_empty_array_with_capacity(v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2122_ = ((size_t)5ULL);
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_unsigned_to_nat(32u);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
v___x_2126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2127_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
lean_ctor_set(v___x_2127_, 2, v___x_2123_);
lean_ctor_set(v___x_2127_, 3, v___x_2123_);
lean_ctor_set_usize(v___x_2127_, 4, v___x_2122_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = lean_box(1);
v___x_2129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
lean_ctor_set(v___x_2131_, 2, v___x_2128_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2137_ = l_Lean_stringToMessageData(v___x_2136_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2140_ = l_Lean_stringToMessageData(v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2143_ = l_Lean_stringToMessageData(v___x_2142_);
return v___x_2143_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2153_, lean_object* v_declHint_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v_env_2159_; uint8_t v___x_2160_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_st_ref_get(v___y_2155_);
v_env_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc_ref(v_env_2159_);
lean_dec(v___x_2158_);
v___x_2160_ = l_Lean_Name_isAnonymous(v_declHint_2154_);
if (v___x_2160_ == 0)
{
uint8_t v_isExporting_2161_; 
v_isExporting_2161_ = lean_ctor_get_uint8(v_env_2159_, sizeof(void*)*13);
if (v_isExporting_2161_ == 0)
{
lean_object* v___x_2162_; 
lean_dec_ref(v_env_2159_);
lean_dec(v_declHint_2154_);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v_msg_2153_);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
lean_inc_ref(v_env_2159_);
v___x_2163_ = l_Lean_Environment_setExporting(v_env_2159_, v___x_2160_);
lean_inc(v_declHint_2154_);
lean_inc_ref(v___x_2163_);
v___x_2164_ = l_Lean_Environment_contains(v___x_2163_, v_declHint_2154_, v_isExporting_2161_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
lean_dec_ref(v___x_2163_);
lean_dec_ref(v_env_2159_);
lean_dec(v_declHint_2154_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_msg_2153_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_c_2171_; lean_object* v___x_2172_; 
v___x_2166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2168_ = l_Lean_Options_empty;
v___x_2169_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2163_);
lean_ctor_set(v___x_2169_, 1, v___x_2166_);
lean_ctor_set(v___x_2169_, 2, v___x_2167_);
lean_ctor_set(v___x_2169_, 3, v___x_2168_);
lean_inc(v_declHint_2154_);
v___x_2170_ = l_Lean_MessageData_ofConstName(v_declHint_2154_, v___x_2160_);
v_c_2171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2171_, 0, v___x_2169_);
lean_ctor_set(v_c_2171_, 1, v___x_2170_);
v___x_2172_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2159_, v_declHint_2154_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec_ref(v_env_2159_);
lean_dec(v_declHint_2154_);
v___x_2173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_c_2171_);
v___x_2175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = l_Lean_MessageData_note(v___x_2176_);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_msg_2153_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
return v___x_2179_;
}
else
{
lean_object* v_val_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2214_; 
v_val_2180_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2182_ = v___x_2172_;
v_isShared_2183_ = v_isSharedCheck_2214_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_val_2180_);
lean_dec(v___x_2172_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2214_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_mod_2186_; uint8_t v___x_2187_; 
v___x_2184_ = l_Lean_Environment_header(v_env_2159_);
lean_dec_ref(v_env_2159_);
v___x_2185_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2184_);
v_mod_2186_ = lean_array_get(v___x_2157_, v___x_2185_, v_val_2180_);
lean_dec(v_val_2180_);
lean_dec_ref(v___x_2185_);
v___x_2187_ = l_Lean_isPrivateName(v_declHint_2154_);
lean_dec(v_declHint_2154_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v_c_2171_);
v___x_2190_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_MessageData_ofName(v_mod_2186_);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2193_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = l_Lean_MessageData_note(v___x_2195_);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_msg_2153_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2197_);
v___x_2199_ = v___x_2182_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v_c_2171_);
v___x_2203_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_MessageData_ofName(v_mod_2186_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = l_Lean_MessageData_note(v___x_2208_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_msg_2153_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2210_);
v___x_2212_ = v___x_2182_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2215_; 
lean_dec_ref(v_env_2159_);
lean_dec(v_declHint_2154_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v_msg_2153_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2216_, lean_object* v_declHint_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2216_, v_declHint_2217_, v___y_2218_);
lean_dec(v___y_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_2221_, lean_object* v_declHint_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2238_; 
v___x_2228_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2221_, v_declHint_2222_, v___y_2226_);
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2238_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2238_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2233_ = l_Lean_unknownIdentifierMessageTag;
v___x_2234_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v_a_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_2239_, lean_object* v_declHint_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2239_, v_declHint_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_2247_, lean_object* v_msg_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_toCold_2254_; lean_object* v_currRecDepth_2255_; lean_object* v_ref_2256_; uint16_t v_optionFlags_2257_; uint8_t v_suppressElabErrors_2258_; uint8_t v_isRecordingDeps_2259_; lean_object* v_ref_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v_toCold_2254_ = lean_ctor_get(v___y_2251_, 0);
v_currRecDepth_2255_ = lean_ctor_get(v___y_2251_, 1);
v_ref_2256_ = lean_ctor_get(v___y_2251_, 2);
v_optionFlags_2257_ = lean_ctor_get_uint16(v___y_2251_, sizeof(void*)*3);
v_suppressElabErrors_2258_ = lean_ctor_get_uint8(v___y_2251_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2259_ = lean_ctor_get_uint8(v___y_2251_, sizeof(void*)*3 + 3);
v_ref_2260_ = l_Lean_replaceRef(v_ref_2247_, v_ref_2256_);
lean_inc(v_currRecDepth_2255_);
lean_inc_ref(v_toCold_2254_);
v___x_2261_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2261_, 0, v_toCold_2254_);
lean_ctor_set(v___x_2261_, 1, v_currRecDepth_2255_);
lean_ctor_set(v___x_2261_, 2, v_ref_2260_);
lean_ctor_set_uint16(v___x_2261_, sizeof(void*)*3, v_optionFlags_2257_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*3 + 2, v_suppressElabErrors_2258_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*3 + 3, v_isRecordingDeps_2259_);
v___x_2262_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2248_, v___y_2249_, v___y_2250_, v___x_2261_, v___y_2252_);
lean_dec_ref_known(v___x_2261_, 3);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2263_, lean_object* v_msg_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2263_, v_msg_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v_ref_2263_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2271_, lean_object* v_msg_2272_, lean_object* v_declHint_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; lean_object* v_a_2280_; lean_object* v___x_2281_; 
v___x_2279_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2272_, v_declHint_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2271_, v_a_2280_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2282_, lean_object* v_msg_2283_, lean_object* v_declHint_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2282_, v_msg_2283_, v_declHint_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v_ref_2282_);
return v_res_2290_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2297_, lean_object* v_constName_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2304_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2305_ = 0;
lean_inc(v_constName_2298_);
v___x_2306_ = l_Lean_MessageData_ofConstName(v_constName_2298_, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2304_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2297_, v___x_2309_, v_constName_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2311_, lean_object* v_constName_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2311_, v_constName_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v_ref_2311_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_ref_2325_; lean_object* v___x_2326_; 
v_ref_2325_ = lean_ctor_get(v___y_2322_, 2);
v___x_2326_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2325_, v_constName_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; lean_object* v_env_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; 
v___x_2340_ = lean_st_ref_get(v___y_2338_);
v_env_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc_ref(v_env_2341_);
lean_dec(v___x_2340_);
v___x_2342_ = 0;
lean_inc(v_constName_2334_);
v___x_2343_ = l_Lean_Environment_findConstVal_x3f(v_env_2341_, v_constName_2334_, v___x_2342_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
return v___x_2344_;
}
else
{
lean_object* v_val_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_constName_2334_);
v_val_2345_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2343_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_val_2345_);
lean_dec(v___x_2343_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 0);
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_val_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
lean_inc(v_constName_2360_);
v___x_2366_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v_levelParams_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v_levelParams_2368_ = lean_ctor_get(v_a_2367_, 1);
v___x_2369_ = lean_box(0);
lean_inc(v_levelParams_2368_);
v___x_2370_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2368_, v___x_2369_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc_n(v_a_2371_, 2);
lean_dec_ref_known(v___x_2370_, 1);
v___x_2372_ = l_Lean_mkConst(v_constName_2360_, v_a_2371_);
v___x_2373_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2367_, v_a_2371_, v_a_2364_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2382_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2382_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2382_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2372_);
lean_ctor_set(v___x_2378_, 1, v_a_2374_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2378_);
v___x_2380_ = v___x_2376_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v___x_2372_);
v_a_2383_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2373_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2373_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_a_2367_);
lean_dec(v_constName_2360_);
v_a_2391_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2370_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2370_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_constName_2360_);
v_a_2399_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2366_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2366_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2414_, lean_object* v_constName_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2422_, lean_object* v_constName_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2422_, v_constName_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2430_, lean_object* v_ref_2431_, lean_object* v_constName_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2431_, v_constName_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2439_, lean_object* v_ref_2440_, lean_object* v_constName_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2439_, v_ref_2440_, v_constName_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v_ref_2440_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2448_, lean_object* v_ref_2449_, lean_object* v_msg_2450_, lean_object* v_declHint_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2449_, v_msg_2450_, v_declHint_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_ref_2459_, lean_object* v_msg_2460_, lean_object* v_declHint_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2458_, v_ref_2459_, v_msg_2460_, v_declHint_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v_ref_2459_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2468_, lean_object* v_declHint_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2468_, v_declHint_2469_, v___y_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2476_, lean_object* v_declHint_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2476_, v_declHint_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2484_, lean_object* v_ref_2485_, lean_object* v_msg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2485_, v_msg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2493_, lean_object* v_ref_2494_, lean_object* v_msg_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2493_, v_ref_2494_, v_msg_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v_ref_2494_);
return v_res_2501_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2504_ = l_Lean_stringToMessageData(v___x_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2507_ = l_Lean_stringToMessageData(v___x_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2508_, lean_object* v_f_2509_, lean_object* v_inst_2510_, lean_object* v_xs_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2518_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2519_ = lean_apply_1(v_inst_2508_, v_f_2509_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_apply_1(v_inst_2510_, v_xs_2511_);
v___x_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2526_, lean_object* v_f_2527_, lean_object* v_inst_2528_, lean_object* v_xs_2529_, lean_object* v_x_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2526_, v_f_2527_, v_inst_2528_, v_xs_2529_, v_x_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v_x_2530_);
return v_res_2536_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_instMonadEIO___redArg();
return v___x_2537_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2539_ = l_StateRefT_x27_instMonad___redArg(v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2547_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2548_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2547_, v___x_2546_);
return v___x_2548_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; 
v___x_2549_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2550_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2551_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2550_, v___x_2549_);
return v___x_2551_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2554_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2555_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2557_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2556_, v___x_2555_, v___x_2554_);
return v___x_2557_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___f_2559_; lean_object* v___f_2560_; lean_object* v___x_2561_; 
v___x_2558_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2559_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2560_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2561_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2560_, v___f_2559_, v___x_2558_);
return v___x_2561_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_instMonadExceptOfEIO___redArg();
return v___x_2562_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2564_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2563_);
return v___x_2564_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2566_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2565_);
return v___x_2566_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2568_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2567_);
return v___x_2568_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2570_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2569_);
return v___x_2570_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2583_ = l_Lean_Name_append(v___x_2582_, v___x_2581_);
return v___x_2583_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2590_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2591_ = l_Lean_Name_append(v___x_2590_, v___x_2589_);
return v___x_2591_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2592_; double v___x_2593_; 
v___x_2592_ = lean_unsigned_to_nat(1000000000u);
v___x_2593_ = lean_float_of_nat(v___x_2592_);
return v___x_2593_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2600_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2601_ = l_Lean_Name_append(v___x_2600_, v___x_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_f_2604_, lean_object* v_xs_2605_, lean_object* v_k_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v_toApplicative_2613_; lean_object* v_toFunctor_2614_; lean_object* v_toSeq_2615_; lean_object* v_toSeqLeft_2616_; lean_object* v_toSeqRight_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; lean_object* v___f_2623_; lean_object* v___f_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v_toApplicative_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2868_; 
v___x_2612_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2613_ = lean_ctor_get(v___x_2612_, 0);
v_toFunctor_2614_ = lean_ctor_get(v_toApplicative_2613_, 0);
v_toSeq_2615_ = lean_ctor_get(v_toApplicative_2613_, 2);
v_toSeqLeft_2616_ = lean_ctor_get(v_toApplicative_2613_, 3);
v_toSeqRight_2617_ = lean_ctor_get(v_toApplicative_2613_, 4);
v___f_2618_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2619_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2614_, 2);
v___f_2620_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2620_, 0, v_toFunctor_2614_);
v___f_2621_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2621_, 0, v_toFunctor_2614_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___f_2620_);
lean_ctor_set(v___x_2622_, 1, v___f_2621_);
lean_inc(v_toSeqRight_2617_);
v___f_2623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2623_, 0, v_toSeqRight_2617_);
lean_inc(v_toSeqLeft_2616_);
v___f_2624_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2624_, 0, v_toSeqLeft_2616_);
lean_inc(v_toSeq_2615_);
v___f_2625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2625_, 0, v_toSeq_2615_);
v___x_2626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2622_);
lean_ctor_set(v___x_2626_, 1, v___f_2618_);
lean_ctor_set(v___x_2626_, 2, v___f_2625_);
lean_ctor_set(v___x_2626_, 3, v___f_2624_);
lean_ctor_set(v___x_2626_, 4, v___f_2623_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___f_2619_);
v___x_2628_ = l_StateRefT_x27_instMonad___redArg(v___x_2627_);
v_toApplicative_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v___x_2628_, 1);
lean_dec(v_unused_2869_);
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2868_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_toApplicative_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2868_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_toFunctor_2633_; lean_object* v_toSeq_2634_; lean_object* v_toSeqLeft_2635_; lean_object* v_toSeqRight_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2866_; 
v_toFunctor_2633_ = lean_ctor_get(v_toApplicative_2629_, 0);
v_toSeq_2634_ = lean_ctor_get(v_toApplicative_2629_, 2);
v_toSeqLeft_2635_ = lean_ctor_get(v_toApplicative_2629_, 3);
v_toSeqRight_2636_ = lean_ctor_get(v_toApplicative_2629_, 4);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_toApplicative_2629_);
if (v_isSharedCheck_2866_ == 0)
{
lean_object* v_unused_2867_; 
v_unused_2867_ = lean_ctor_get(v_toApplicative_2629_, 1);
lean_dec(v_unused_2867_);
v___x_2638_ = v_toApplicative_2629_;
v_isShared_2639_ = v_isSharedCheck_2866_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_toSeqRight_2636_);
lean_inc(v_toSeqLeft_2635_);
lean_inc(v_toSeq_2634_);
lean_inc(v_toFunctor_2633_);
lean_dec(v_toApplicative_2629_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2866_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___f_2642_; lean_object* v___f_2643_; lean_object* v___x_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; lean_object* v___f_2647_; lean_object* v___x_2649_; 
v___f_2640_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2641_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2633_);
v___f_2642_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2642_, 0, v_toFunctor_2633_);
v___f_2643_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2643_, 0, v_toFunctor_2633_);
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___f_2642_);
lean_ctor_set(v___x_2644_, 1, v___f_2643_);
v___f_2645_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2645_, 0, v_toSeqRight_2636_);
v___f_2646_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2646_, 0, v_toSeqLeft_2635_);
v___f_2647_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2647_, 0, v_toSeq_2634_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 4, v___f_2645_);
lean_ctor_set(v___x_2638_, 3, v___f_2646_);
lean_ctor_set(v___x_2638_, 2, v___f_2647_);
lean_ctor_set(v___x_2638_, 1, v___f_2640_);
lean_ctor_set(v___x_2638_, 0, v___x_2644_);
v___x_2649_ = v___x_2638_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v___f_2640_);
lean_ctor_set(v_reuseFailAlloc_2865_, 2, v___f_2647_);
lean_ctor_set(v_reuseFailAlloc_2865_, 3, v___f_2646_);
lean_ctor_set(v_reuseFailAlloc_2865_, 4, v___f_2645_);
v___x_2649_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 1, v___f_2641_);
lean_ctor_set(v___x_2631_, 0, v___x_2649_);
v___x_2651_ = v___x_2631_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___f_2641_);
v___x_2651_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v_toMonadRef_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v_toCold_2657_; lean_object* v_options_2658_; uint8_t v_hasTrace_2659_; 
v___x_2652_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2653_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2654_ = lean_ctor_get(v___x_2653_, 0);
v___x_2655_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2656_ = l_Lean_KVMap_instValueBool;
v_toCold_2657_ = lean_ctor_get(v_a_2609_, 0);
v_options_2658_ = lean_ctor_get(v_toCold_2657_, 2);
v_hasTrace_2659_ = lean_ctor_get_uint8(v_options_2658_, sizeof(void*)*1);
if (v_hasTrace_2659_ == 0)
{
lean_object* v___x_2660_; 
lean_dec_ref(v___x_2651_);
lean_dec(v_xs_2605_);
lean_dec(v_f_2604_);
lean_dec_ref(v_inst_2603_);
lean_dec_ref(v_inst_2602_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2660_ = lean_apply_5(v_k_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2660_) == 0)
{
return v___x_2660_;
}
else
{
lean_object* v_a_2661_; uint8_t v___y_2663_; uint8_t v___x_2672_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
v___x_2672_ = l_Lean_Exception_isInterrupt(v_a_2661_);
if (v___x_2672_ == 0)
{
uint8_t v___x_2673_; 
lean_inc(v_a_2661_);
v___x_2673_ = l_Lean_Exception_isRuntime(v_a_2661_);
v___y_2663_ = v___x_2673_;
goto v___jp_2662_;
}
else
{
v___y_2663_ = v___x_2672_;
goto v___jp_2662_;
}
v___jp_2662_:
{
if (v___y_2663_ == 0)
{
lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v___x_2660_, 0);
lean_dec(v_unused_2671_);
v___x_2665_ = v___x_2660_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_dec(v___x_2660_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2661_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
else
{
lean_dec(v_a_2661_);
return v___x_2660_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2674_; lean_object* v___x_2675_; lean_object* v___y_2677_; lean_object* v___y_2678_; uint8_t v___y_2679_; lean_object* v___y_2704_; lean_object* v_a_2705_; lean_object* v___f_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v_a_2717_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v_a_2733_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; uint8_t v___y_2739_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v_a_2750_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v_a_2756_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v_a_2761_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v_a_2774_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v_a_2791_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v_a_2797_; 
v_inheritedTraceOptions_2674_ = lean_ctor_get(v_toCold_2657_, 11);
v___x_2675_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2708_, 0, v_inst_2602_);
lean_closure_set(v___f_2708_, 1, v_f_2604_);
lean_closure_set(v___f_2708_, 2, v_inst_2603_);
lean_closure_set(v___f_2708_, 3, v_xs_2605_);
v___f_2709_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2712_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2713_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2674_, v_options_2658_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2836_ = l_Lean_trace_profiler;
v___x_2837_ = l_Lean_Option_get___redArg(v___x_2656_, v_options_2658_, v___x_2836_);
v___x_2838_ = lean_unbox(v___x_2837_);
lean_dec(v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
lean_dec_ref(v___f_2708_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2839_ = lean_apply_5(v_k_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
v___x_2841_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2842_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2843_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2674_, v_options_2658_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_dec(v_a_2840_);
lean_dec_ref(v___x_2651_);
return v___x_2839_;
}
else
{
lean_object* v___x_2844_; lean_object* v___x_8995__overap_2845_; lean_object* v___x_2846_; 
lean_dec_ref_known(v___x_2839_, 1);
lean_inc(v_a_2840_);
v___x_2844_ = l_Lean_MessageData_ofExpr(v_a_2840_);
lean_inc_ref(v_toMonadRef_2654_);
lean_inc_ref(v___x_2651_);
v___x_8995__overap_2845_ = l_Lean_addTrace___redArg(v___x_2651_, v___x_2652_, v_toMonadRef_2654_, v___x_2675_, v___x_2841_, v___x_2844_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2846_ = lean_apply_5(v___x_8995__overap_2845_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v___x_2651_);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; 
v_unused_2854_ = lean_ctor_get(v___x_2846_, 0);
lean_dec(v_unused_2854_);
v___x_2848_ = v___x_2846_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_dec(v___x_2846_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v_a_2840_);
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2840_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_a_2840_);
v_a_2855_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2846_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2846_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
lean_inc(v_a_2855_);
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
v___y_2704_ = v___x_2860_;
v_a_2705_ = v_a_2855_;
goto v___jp_2703_;
}
}
}
}
}
else
{
lean_object* v_a_2863_; 
v_a_2863_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2863_);
v___y_2704_ = v___x_2839_;
v_a_2705_ = v_a_2863_;
goto v___jp_2703_;
}
}
else
{
goto v___jp_2799_;
}
}
else
{
goto v___jp_2799_;
}
v___jp_2676_:
{
if (v___y_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
lean_dec_ref(v___y_2677_);
v___x_2680_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2681_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2674_, v_options_2658_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_dec_ref(v___x_2651_);
v___x_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___y_2678_);
return v___x_2683_;
}
else
{
lean_object* v___x_2684_; lean_object* v___x_8806__overap_2685_; lean_object* v___x_2686_; 
lean_inc_ref(v___y_2678_);
v___x_2684_ = l_Lean_Exception_toMessageData(v___y_2678_);
lean_inc_ref(v_toMonadRef_2654_);
v___x_8806__overap_2685_ = l_Lean_addTrace___redArg(v___x_2651_, v___x_2652_, v_toMonadRef_2654_, v___x_2675_, v___x_2680_, v___x_2684_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2686_ = lean_apply_5(v___x_8806__overap_2685_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2694_);
v___x_2688_ = v___x_2686_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v___x_2686_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 1);
lean_ctor_set(v___x_2688_, 0, v___y_2678_);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___y_2678_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v___y_2678_);
v_a_2695_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2686_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2686_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2678_);
lean_dec_ref(v___x_2651_);
return v___y_2677_;
}
}
v___jp_2703_:
{
uint8_t v___x_2706_; 
v___x_2706_ = l_Lean_Exception_isInterrupt(v_a_2705_);
if (v___x_2706_ == 0)
{
uint8_t v___x_2707_; 
lean_inc_ref(v_a_2705_);
v___x_2707_ = l_Lean_Exception_isRuntime(v_a_2705_);
v___y_2677_ = v___y_2704_;
v___y_2678_ = v_a_2705_;
v___y_2679_ = v___x_2707_;
goto v___jp_2676_;
}
else
{
v___y_2677_ = v___y_2704_;
v___y_2678_ = v_a_2705_;
v___y_2679_ = v___x_2706_;
goto v___jp_2676_;
}
}
v___jp_2714_:
{
lean_object* v___x_2718_; double v___x_2719_; double v___x_2720_; double v___x_2721_; double v___x_2722_; double v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_8867__overap_2728_; lean_object* v___x_2729_; 
v___x_2718_ = lean_io_mono_nanos_now();
v___x_2719_ = lean_float_of_nat(v___y_2716_);
v___x_2720_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2721_ = lean_float_div(v___x_2719_, v___x_2720_);
v___x_2722_ = lean_float_of_nat(v___x_2718_);
v___x_2723_ = lean_float_div(v___x_2722_, v___x_2720_);
v___x_2724_ = lean_box_float(v___x_2721_);
v___x_2725_ = lean_box_float(v___x_2723_);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_a_2717_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
lean_inc_ref(v_toMonadRef_2654_);
v___x_8867__overap_2728_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2651_, v___x_2652_, v_toMonadRef_2654_, v___x_2675_, lean_box(0), v___x_2655_, v___f_2709_, v___x_2710_, v_hasTrace_2659_, v___x_2711_, v_options_2658_, v___x_2713_, v___y_2715_, v___f_2708_, v___x_2727_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2729_ = lean_apply_5(v___x_8867__overap_2728_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
return v___x_2729_;
}
v___jp_2730_:
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_a_2733_);
v___y_2715_ = v___y_2732_;
v___y_2716_ = v___y_2731_;
v_a_2717_ = v___x_2734_;
goto v___jp_2714_;
}
v___jp_2735_:
{
if (v___y_2739_ == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2740_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2741_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2674_, v_options_2658_, v___x_2741_);
if (v___x_2742_ == 0)
{
v___y_2731_ = v___y_2737_;
v___y_2732_ = v___y_2736_;
v_a_2733_ = v___y_2738_;
goto v___jp_2730_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_8886__overap_2744_; lean_object* v___x_2745_; 
lean_inc_ref(v___y_2738_);
v___x_2743_ = l_Lean_Exception_toMessageData(v___y_2738_);
lean_inc_ref(v_toMonadRef_2654_);
lean_inc_ref(v___x_2651_);
v___x_8886__overap_2744_ = l_Lean_addTrace___redArg(v___x_2651_, v___x_2652_, v_toMonadRef_2654_, v___x_2675_, v___x_2740_, v___x_2743_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2745_ = lean_apply_5(v___x_8886__overap_2744_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_dec_ref_known(v___x_2745_, 1);
v___y_2731_ = v___y_2737_;
v___y_2732_ = v___y_2736_;
v_a_2733_ = v___y_2738_;
goto v___jp_2730_;
}
else
{
lean_object* v_a_2746_; 
lean_dec_ref(v___y_2738_);
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___y_2731_ = v___y_2737_;
v___y_2732_ = v___y_2736_;
v_a_2733_ = v_a_2746_;
goto v___jp_2730_;
}
}
}
else
{
v___y_2731_ = v___y_2737_;
v___y_2732_ = v___y_2736_;
v_a_2733_ = v___y_2738_;
goto v___jp_2730_;
}
}
v___jp_2747_:
{
uint8_t v___x_2751_; 
v___x_2751_ = l_Lean_Exception_isInterrupt(v_a_2750_);
if (v___x_2751_ == 0)
{
uint8_t v___x_2752_; 
lean_inc_ref(v_a_2750_);
v___x_2752_ = l_Lean_Exception_isRuntime(v_a_2750_);
v___y_2736_ = v___y_2749_;
v___y_2737_ = v___y_2748_;
v___y_2738_ = v_a_2750_;
v___y_2739_ = v___x_2752_;
goto v___jp_2735_;
}
else
{
v___y_2736_ = v___y_2749_;
v___y_2737_ = v___y_2748_;
v___y_2738_ = v_a_2750_;
v___y_2739_ = v___x_2751_;
goto v___jp_2735_;
}
}
v___jp_2753_:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2757_, 0, v_a_2756_);
v___y_2715_ = v___y_2755_;
v___y_2716_ = v___y_2754_;
v_a_2717_ = v___x_2757_;
goto v___jp_2714_;
}
v___jp_2758_:
{
lean_object* v___x_2762_; double v___x_2763_; double v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_8929__overap_2769_; lean_object* v___x_2770_; 
v___x_2762_ = lean_io_get_num_heartbeats();
v___x_2763_ = lean_float_of_nat(v___y_2760_);
v___x_2764_ = lean_float_of_nat(v___x_2762_);
v___x_2765_ = lean_box_float(v___x_2763_);
v___x_2766_ = lean_box_float(v___x_2764_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_a_2761_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
lean_inc_ref(v_toMonadRef_2654_);
v___x_8929__overap_2769_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2651_, v___x_2652_, v_toMonadRef_2654_, v___x_2675_, lean_box(0), v___x_2655_, v___f_2709_, v___x_2710_, v_hasTrace_2659_, v___x_2711_, v_options_2658_, v___x_2713_, v___y_2759_, v___f_2708_, v___x_2768_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2770_ = lean_apply_5(v___x_8929__overap_2769_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
return v___x_2770_;
}
v___jp_2771_:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_a_2774_);
v___y_2759_ = v___y_2772_;
v___y_2760_ = v___y_2773_;
v_a_2761_ = v___x_2775_;
goto v___jp_2758_;
}
v___jp_2776_:
{
if (v___y_2780_ == 0)
{
lean_object* v___x_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v___x_2781_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2782_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2783_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2674_, v_options_2658_, v___x_2782_);
if (v___x_2783_ == 0)
{
v___y_2772_ = v___y_2777_;
v___y_2773_ = v___y_2778_;
v_a_2774_ = v___y_2779_;
goto v___jp_2771_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_8948__overap_2785_; lean_object* v___x_2786_; 
lean_inc_ref(v___y_2779_);
v___x_2784_ = l_Lean_Exception_toMessageData(v___y_2779_);
lean_inc_ref(v_toMonadRef_2654_);
lean_inc_ref(v___x_2651_);
v___x_8948__overap_2785_ = l_Lean_addTrace___redArg(v___x_2651_, v___x_2652_, v_toMonadRef_2654_, v___x_2675_, v___x_2781_, v___x_2784_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2786_ = lean_apply_5(v___x_8948__overap_2785_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_dec_ref_known(v___x_2786_, 1);
v___y_2772_ = v___y_2777_;
v___y_2773_ = v___y_2778_;
v_a_2774_ = v___y_2779_;
goto v___jp_2771_;
}
else
{
lean_object* v_a_2787_; 
lean_dec_ref(v___y_2779_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___y_2772_ = v___y_2777_;
v___y_2773_ = v___y_2778_;
v_a_2774_ = v_a_2787_;
goto v___jp_2771_;
}
}
}
else
{
v___y_2772_ = v___y_2777_;
v___y_2773_ = v___y_2778_;
v_a_2774_ = v___y_2779_;
goto v___jp_2771_;
}
}
v___jp_2788_:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Lean_Exception_isInterrupt(v_a_2791_);
if (v___x_2792_ == 0)
{
uint8_t v___x_2793_; 
lean_inc_ref(v_a_2791_);
v___x_2793_ = l_Lean_Exception_isRuntime(v_a_2791_);
v___y_2777_ = v___y_2789_;
v___y_2778_ = v___y_2790_;
v___y_2779_ = v_a_2791_;
v___y_2780_ = v___x_2793_;
goto v___jp_2776_;
}
else
{
v___y_2777_ = v___y_2789_;
v___y_2778_ = v___y_2790_;
v___y_2779_ = v_a_2791_;
v___y_2780_ = v___x_2792_;
goto v___jp_2776_;
}
}
v___jp_2794_:
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v_a_2797_);
v___y_2759_ = v___y_2795_;
v___y_2760_ = v___y_2796_;
v_a_2761_ = v___x_2798_;
goto v___jp_2758_;
}
v___jp_2799_:
{
lean_object* v___x_8845__overap_2800_; lean_object* v___x_2801_; 
lean_inc_ref(v___x_2651_);
v___x_8845__overap_2800_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2651_, v___x_2652_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2801_ = lean_apply_5(v___x_8845__overap_2800_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2804_ = l_Lean_Option_get___redArg(v___x_2656_, v_options_2658_, v___x_2803_);
v___x_2805_ = lean_unbox(v___x_2804_);
lean_dec(v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_io_mono_nanos_now();
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2807_ = lean_apply_5(v_k_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2811_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2674_, v_options_2658_, v___x_2810_);
if (v___x_2811_ == 0)
{
v___y_2754_ = v___x_2806_;
v___y_2755_ = v_a_2802_;
v_a_2756_ = v_a_2808_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_8909__overap_2813_; lean_object* v___x_2814_; 
lean_inc(v_a_2808_);
v___x_2812_ = l_Lean_MessageData_ofExpr(v_a_2808_);
lean_inc_ref(v_toMonadRef_2654_);
lean_inc_ref(v___x_2651_);
v___x_8909__overap_2813_ = l_Lean_addTrace___redArg(v___x_2651_, v___x_2652_, v_toMonadRef_2654_, v___x_2675_, v___x_2809_, v___x_2812_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2814_ = lean_apply_5(v___x_8909__overap_2813_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_dec_ref_known(v___x_2814_, 1);
v___y_2754_ = v___x_2806_;
v___y_2755_ = v_a_2802_;
v_a_2756_ = v_a_2808_;
goto v___jp_2753_;
}
else
{
lean_object* v_a_2815_; 
lean_dec(v_a_2808_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___y_2748_ = v___x_2806_;
v___y_2749_ = v_a_2802_;
v_a_2750_ = v_a_2815_;
goto v___jp_2747_;
}
}
}
else
{
lean_object* v_a_2816_; 
v_a_2816_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2807_, 1);
v___y_2748_ = v___x_2806_;
v___y_2749_ = v_a_2802_;
v_a_2750_ = v_a_2816_;
goto v___jp_2747_;
}
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2818_ = lean_apply_5(v_k_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2821_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2822_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2674_, v_options_2658_, v___x_2821_);
if (v___x_2822_ == 0)
{
v___y_2795_ = v_a_2802_;
v___y_2796_ = v___x_2817_;
v_a_2797_ = v_a_2819_;
goto v___jp_2794_;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_8971__overap_2824_; lean_object* v___x_2825_; 
lean_inc(v_a_2819_);
v___x_2823_ = l_Lean_MessageData_ofExpr(v_a_2819_);
lean_inc_ref(v_toMonadRef_2654_);
lean_inc_ref(v___x_2651_);
v___x_8971__overap_2824_ = l_Lean_addTrace___redArg(v___x_2651_, v___x_2652_, v_toMonadRef_2654_, v___x_2675_, v___x_2820_, v___x_2823_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_a_2608_);
lean_inc_ref(v_a_2607_);
v___x_2825_ = lean_apply_5(v___x_8971__overap_2824_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, lean_box(0));
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref_known(v___x_2825_, 1);
v___y_2795_ = v_a_2802_;
v___y_2796_ = v___x_2817_;
v_a_2797_ = v_a_2819_;
goto v___jp_2794_;
}
else
{
lean_object* v_a_2826_; 
lean_dec(v_a_2819_);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___y_2789_ = v_a_2802_;
v___y_2790_ = v___x_2817_;
v_a_2791_ = v_a_2826_;
goto v___jp_2788_;
}
}
}
else
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2818_, 1);
v___y_2789_ = v_a_2802_;
v___y_2790_ = v___x_2817_;
v_a_2791_ = v_a_2827_;
goto v___jp_2788_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref(v___f_2708_);
lean_dec_ref(v___x_2651_);
lean_dec_ref(v_k_2606_);
v_a_2828_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2801_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2801_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_f_2872_, lean_object* v_xs_2873_, lean_object* v_k_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2870_, v_inst_2871_, v_f_2872_, v_xs_2873_, v_k_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2881_, lean_object* v_00_u03b2_2882_, lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_f_2885_, lean_object* v_xs_2886_, lean_object* v_k_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2883_, v_inst_2884_, v_f_2885_, v_xs_2886_, v_k_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2894_, lean_object* v_00_u03b2_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_f_2898_, lean_object* v_xs_2899_, lean_object* v_k_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2894_, v_00_u03b2_2895_, v_inst_2896_, v_inst_2897_, v_f_2898_, v_xs_2899_, v_k_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2907_, uint8_t v_allowLevelAssignments_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2908_, v_k_2907_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
v_a_2923_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2914_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2914_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2931_, lean_object* v_allowLevelAssignments_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2938_; lean_object* v_res_2939_; 
v_allowLevelAssignments_boxed_2938_ = lean_unbox(v_allowLevelAssignments_2932_);
v_res_2939_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2931_, v_allowLevelAssignments_boxed_2938_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2940_, lean_object* v_k_2941_, uint8_t v_allowLevelAssignments_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2941_, v_allowLevelAssignments_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_k_2950_, lean_object* v_allowLevelAssignments_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2957_; lean_object* v_res_2958_; 
v_allowLevelAssignments_boxed_2957_ = lean_unbox(v_allowLevelAssignments_2951_);
v_res_2958_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2949_, v_k_2950_, v_allowLevelAssignments_boxed_2957_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2959_, lean_object* v_xs_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2959_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v_fst_2968_; lean_object* v_snd_2969_; lean_object* v___x_2970_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v_fst_2968_ = lean_ctor_get(v_a_2967_, 0);
lean_inc(v_fst_2968_);
v_snd_2969_ = lean_ctor_get(v_a_2967_, 1);
lean_inc(v_snd_2969_);
lean_dec(v_a_2967_);
v___x_2970_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2968_, v_snd_2969_, v_xs_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_2970_;
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v_a_2971_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2966_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2966_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2979_, lean_object* v_xs_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2979_, v_xs_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec_ref(v_xs_2980_);
return v_res_2986_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = lean_unsigned_to_nat(32u);
v___x_2988_ = lean_mk_empty_array_with_capacity(v___x_2987_);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2990_ = ((size_t)5ULL);
v___x_2991_ = lean_unsigned_to_nat(0u);
v___x_2992_ = lean_unsigned_to_nat(32u);
v___x_2993_ = lean_mk_empty_array_with_capacity(v___x_2992_);
v___x_2994_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2995_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v___x_2993_);
lean_ctor_set(v___x_2995_, 2, v___x_2991_);
lean_ctor_set(v___x_2995_, 3, v___x_2991_);
lean_ctor_set_usize(v___x_2995_, 4, v___x_2990_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v_traceState_2999_; lean_object* v_traces_3000_; lean_object* v___x_3001_; lean_object* v_traceState_3002_; lean_object* v_env_3003_; lean_object* v_nextMacroScope_3004_; lean_object* v_ngen_3005_; lean_object* v_auxDeclNGen_3006_; lean_object* v_cache_3007_; lean_object* v_recordedDeps_3008_; lean_object* v_messages_3009_; lean_object* v_infoState_3010_; lean_object* v_snapshotTasks_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3030_; 
v___x_2998_ = lean_st_ref_get(v___y_2996_);
v_traceState_2999_ = lean_ctor_get(v___x_2998_, 4);
lean_inc_ref(v_traceState_2999_);
lean_dec(v___x_2998_);
v_traces_3000_ = lean_ctor_get(v_traceState_2999_, 0);
lean_inc_ref(v_traces_3000_);
lean_dec_ref(v_traceState_2999_);
v___x_3001_ = lean_st_ref_take(v___y_2996_);
v_traceState_3002_ = lean_ctor_get(v___x_3001_, 4);
v_env_3003_ = lean_ctor_get(v___x_3001_, 0);
v_nextMacroScope_3004_ = lean_ctor_get(v___x_3001_, 1);
v_ngen_3005_ = lean_ctor_get(v___x_3001_, 2);
v_auxDeclNGen_3006_ = lean_ctor_get(v___x_3001_, 3);
v_cache_3007_ = lean_ctor_get(v___x_3001_, 5);
v_recordedDeps_3008_ = lean_ctor_get(v___x_3001_, 6);
v_messages_3009_ = lean_ctor_get(v___x_3001_, 7);
v_infoState_3010_ = lean_ctor_get(v___x_3001_, 8);
v_snapshotTasks_3011_ = lean_ctor_get(v___x_3001_, 9);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3013_ = v___x_3001_;
v_isShared_3014_ = v_isSharedCheck_3030_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_snapshotTasks_3011_);
lean_inc(v_infoState_3010_);
lean_inc(v_messages_3009_);
lean_inc(v_recordedDeps_3008_);
lean_inc(v_cache_3007_);
lean_inc(v_traceState_3002_);
lean_inc(v_auxDeclNGen_3006_);
lean_inc(v_ngen_3005_);
lean_inc(v_nextMacroScope_3004_);
lean_inc(v_env_3003_);
lean_dec(v___x_3001_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3030_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
uint64_t v_tid_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3028_; 
v_tid_3015_ = lean_ctor_get_uint64(v_traceState_3002_, sizeof(void*)*1);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_traceState_3002_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v_traceState_3002_, 0);
lean_dec(v_unused_3029_);
v___x_3017_ = v_traceState_3002_;
v_isShared_3018_ = v_isSharedCheck_3028_;
goto v_resetjp_3016_;
}
else
{
lean_dec(v_traceState_3002_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3028_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3019_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3019_);
v___x_3021_ = v___x_3017_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3019_);
lean_ctor_set_uint64(v_reuseFailAlloc_3027_, sizeof(void*)*1, v_tid_3015_);
v___x_3021_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3023_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 4, v___x_3021_);
v___x_3023_ = v___x_3013_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_env_3003_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_nextMacroScope_3004_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v_ngen_3005_);
lean_ctor_set(v_reuseFailAlloc_3026_, 3, v_auxDeclNGen_3006_);
lean_ctor_set(v_reuseFailAlloc_3026_, 4, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3026_, 5, v_cache_3007_);
lean_ctor_set(v_reuseFailAlloc_3026_, 6, v_recordedDeps_3008_);
lean_ctor_set(v_reuseFailAlloc_3026_, 7, v_messages_3009_);
lean_ctor_set(v_reuseFailAlloc_3026_, 8, v_infoState_3010_);
lean_ctor_set(v_reuseFailAlloc_3026_, 9, v_snapshotTasks_3011_);
v___x_3023_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_st_ref_put(v___y_2996_, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_traces_3000_);
return v___x_3025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3031_);
lean_dec(v___y_3031_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3034_, lean_object* v_opt_3035_){
_start:
{
lean_object* v_name_3036_; lean_object* v_defValue_3037_; lean_object* v_map_3038_; lean_object* v___x_3039_; 
v_name_3036_ = lean_ctor_get(v_opt_3035_, 0);
v_defValue_3037_ = lean_ctor_get(v_opt_3035_, 1);
v_map_3038_ = lean_ctor_get(v_opts_3034_, 0);
v___x_3039_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3038_, v_name_3036_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_inc(v_defValue_3037_);
return v_defValue_3037_;
}
else
{
lean_object* v_val_3040_; 
v_val_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_val_3040_);
lean_dec_ref_known(v___x_3039_, 1);
if (lean_obj_tag(v_val_3040_) == 3)
{
lean_object* v_v_3041_; 
v_v_3041_ = lean_ctor_get(v_val_3040_, 0);
lean_inc(v_v_3041_);
lean_dec_ref_known(v_val_3040_, 1);
return v_v_3041_;
}
else
{
lean_dec(v_val_3040_);
lean_inc(v_defValue_3037_);
return v_defValue_3037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3042_, lean_object* v_opt_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3042_, v_opt_3043_);
lean_dec_ref(v_opt_3043_);
lean_dec_ref(v_opts_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3045_, lean_object* v_opt_3046_){
_start:
{
lean_object* v_name_3047_; lean_object* v_defValue_3048_; lean_object* v_map_3049_; lean_object* v___x_3050_; 
v_name_3047_ = lean_ctor_get(v_opt_3046_, 0);
v_defValue_3048_ = lean_ctor_get(v_opt_3046_, 1);
v_map_3049_ = lean_ctor_get(v_opts_3045_, 0);
v___x_3050_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3049_, v_name_3047_);
if (lean_obj_tag(v___x_3050_) == 0)
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_unbox(v_defValue_3048_);
return v___x_3051_;
}
else
{
lean_object* v_val_3052_; 
v_val_3052_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_val_3052_);
lean_dec_ref_known(v___x_3050_, 1);
if (lean_obj_tag(v_val_3052_) == 1)
{
uint8_t v_v_3053_; 
v_v_3053_ = lean_ctor_get_uint8(v_val_3052_, 0);
lean_dec_ref_known(v_val_3052_, 0);
return v_v_3053_;
}
else
{
uint8_t v___x_3054_; 
lean_dec(v_val_3052_);
v___x_3054_ = lean_unbox(v_defValue_3048_);
return v___x_3054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3055_, lean_object* v_opt_3056_){
_start:
{
uint8_t v_res_3057_; lean_object* v_r_3058_; 
v_res_3057_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3055_, v_opt_3056_);
lean_dec_ref(v_opt_3056_);
lean_dec_ref(v_opts_3055_);
v_r_3058_ = lean_box(v_res_3057_);
return v_r_3058_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3059_){
_start:
{
if (lean_obj_tag(v_e_3059_) == 0)
{
uint8_t v___x_3060_; 
v___x_3060_ = 2;
return v___x_3060_;
}
else
{
lean_object* v_a_3061_; uint8_t v___x_3062_; 
v_a_3061_ = lean_ctor_get(v_e_3059_, 0);
v___x_3062_ = l_Lean_Expr_hasSyntheticSorry(v_a_3061_);
if (v___x_3062_ == 0)
{
uint8_t v___x_3063_; 
v___x_3063_ = 0;
return v___x_3063_;
}
else
{
uint8_t v___x_3064_; 
v___x_3064_ = 1;
return v___x_3064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3065_){
_start:
{
uint8_t v_res_3066_; lean_object* v_r_3067_; 
v_res_3066_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3065_);
lean_dec_ref(v_e_3065_);
v_r_3067_ = lean_box(v_res_3066_);
return v_r_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3068_, size_t v_i_3069_, lean_object* v_bs_3070_){
_start:
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_usize_dec_lt(v_i_3069_, v_sz_3068_);
if (v___x_3071_ == 0)
{
return v_bs_3070_;
}
else
{
lean_object* v_v_3072_; lean_object* v_msg_3073_; lean_object* v___x_3074_; lean_object* v_bs_x27_3075_; size_t v___x_3076_; size_t v___x_3077_; lean_object* v___x_3078_; 
v_v_3072_ = lean_array_uget_borrowed(v_bs_3070_, v_i_3069_);
v_msg_3073_ = lean_ctor_get(v_v_3072_, 1);
lean_inc_ref(v_msg_3073_);
v___x_3074_ = lean_unsigned_to_nat(0u);
v_bs_x27_3075_ = lean_array_uset(v_bs_3070_, v_i_3069_, v___x_3074_);
v___x_3076_ = ((size_t)1ULL);
v___x_3077_ = lean_usize_add(v_i_3069_, v___x_3076_);
v___x_3078_ = lean_array_uset(v_bs_x27_3075_, v_i_3069_, v_msg_3073_);
v_i_3069_ = v___x_3077_;
v_bs_3070_ = v___x_3078_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3080_, lean_object* v_i_3081_, lean_object* v_bs_3082_){
_start:
{
size_t v_sz_boxed_3083_; size_t v_i_boxed_3084_; lean_object* v_res_3085_; 
v_sz_boxed_3083_ = lean_unbox_usize(v_sz_3080_);
lean_dec(v_sz_3080_);
v_i_boxed_3084_ = lean_unbox_usize(v_i_3081_);
lean_dec(v_i_3081_);
v_res_3085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3083_, v_i_boxed_3084_, v_bs_3082_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3086_, lean_object* v_data_3087_, lean_object* v_ref_3088_, lean_object* v_msg_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_toCold_3095_; lean_object* v_currRecDepth_3096_; lean_object* v_ref_3097_; uint16_t v_optionFlags_3098_; uint8_t v_suppressElabErrors_3099_; uint8_t v_isRecordingDeps_3100_; lean_object* v_ref_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_traceState_3104_; lean_object* v_traces_3105_; lean_object* v___x_3106_; size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; lean_object* v_msg_3110_; lean_object* v___x_3111_; lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3150_; 
v_toCold_3095_ = lean_ctor_get(v___y_3092_, 0);
v_currRecDepth_3096_ = lean_ctor_get(v___y_3092_, 1);
v_ref_3097_ = lean_ctor_get(v___y_3092_, 2);
v_optionFlags_3098_ = lean_ctor_get_uint16(v___y_3092_, sizeof(void*)*3);
v_suppressElabErrors_3099_ = lean_ctor_get_uint8(v___y_3092_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3100_ = lean_ctor_get_uint8(v___y_3092_, sizeof(void*)*3 + 3);
v_ref_3101_ = l_Lean_replaceRef(v_ref_3088_, v_ref_3097_);
lean_inc(v_currRecDepth_3096_);
lean_inc_ref(v_toCold_3095_);
v___x_3102_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3102_, 0, v_toCold_3095_);
lean_ctor_set(v___x_3102_, 1, v_currRecDepth_3096_);
lean_ctor_set(v___x_3102_, 2, v_ref_3101_);
lean_ctor_set_uint16(v___x_3102_, sizeof(void*)*3, v_optionFlags_3098_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*3 + 2, v_suppressElabErrors_3099_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*3 + 3, v_isRecordingDeps_3100_);
v___x_3103_ = lean_st_ref_get(v___y_3093_);
v_traceState_3104_ = lean_ctor_get(v___x_3103_, 4);
lean_inc_ref(v_traceState_3104_);
lean_dec(v___x_3103_);
v_traces_3105_ = lean_ctor_get(v_traceState_3104_, 0);
lean_inc_ref(v_traces_3105_);
lean_dec_ref(v_traceState_3104_);
v___x_3106_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3105_);
lean_dec_ref(v_traces_3105_);
v_sz_3107_ = lean_array_size(v___x_3106_);
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3107_, v___x_3108_, v___x_3106_);
v_msg_3110_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3110_, 0, v_data_3087_);
lean_ctor_set(v_msg_3110_, 1, v_msg_3089_);
lean_ctor_set(v_msg_3110_, 2, v___x_3109_);
v___x_3111_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3110_, v___y_3090_, v___y_3091_, v___x_3102_, v___y_3093_);
lean_dec_ref_known(v___x_3102_, 3);
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3150_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3150_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v_traceState_3117_; lean_object* v_env_3118_; lean_object* v_nextMacroScope_3119_; lean_object* v_ngen_3120_; lean_object* v_auxDeclNGen_3121_; lean_object* v_cache_3122_; lean_object* v_recordedDeps_3123_; lean_object* v_messages_3124_; lean_object* v_infoState_3125_; lean_object* v_snapshotTasks_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3149_; 
v___x_3116_ = lean_st_ref_take(v___y_3093_);
v_traceState_3117_ = lean_ctor_get(v___x_3116_, 4);
v_env_3118_ = lean_ctor_get(v___x_3116_, 0);
v_nextMacroScope_3119_ = lean_ctor_get(v___x_3116_, 1);
v_ngen_3120_ = lean_ctor_get(v___x_3116_, 2);
v_auxDeclNGen_3121_ = lean_ctor_get(v___x_3116_, 3);
v_cache_3122_ = lean_ctor_get(v___x_3116_, 5);
v_recordedDeps_3123_ = lean_ctor_get(v___x_3116_, 6);
v_messages_3124_ = lean_ctor_get(v___x_3116_, 7);
v_infoState_3125_ = lean_ctor_get(v___x_3116_, 8);
v_snapshotTasks_3126_ = lean_ctor_get(v___x_3116_, 9);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3128_ = v___x_3116_;
v_isShared_3129_ = v_isSharedCheck_3149_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_snapshotTasks_3126_);
lean_inc(v_infoState_3125_);
lean_inc(v_messages_3124_);
lean_inc(v_recordedDeps_3123_);
lean_inc(v_cache_3122_);
lean_inc(v_traceState_3117_);
lean_inc(v_auxDeclNGen_3121_);
lean_inc(v_ngen_3120_);
lean_inc(v_nextMacroScope_3119_);
lean_inc(v_env_3118_);
lean_dec(v___x_3116_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3149_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
uint64_t v_tid_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3147_; 
v_tid_3130_ = lean_ctor_get_uint64(v_traceState_3117_, sizeof(void*)*1);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_traceState_3117_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v_traceState_3117_, 0);
lean_dec(v_unused_3148_);
v___x_3132_ = v_traceState_3117_;
v_isShared_3133_ = v_isSharedCheck_3147_;
goto v_resetjp_3131_;
}
else
{
lean_dec(v_traceState_3117_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3147_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_ref_3088_);
lean_ctor_set(v___x_3135_, 1, v_a_3112_);
v___x_3136_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3086_, v___x_3135_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3136_);
v___x_3138_ = v___x_3132_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3136_);
lean_ctor_set_uint64(v_reuseFailAlloc_3146_, sizeof(void*)*1, v_tid_3130_);
v___x_3138_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3140_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 4, v___x_3138_);
v___x_3140_ = v___x_3128_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_env_3118_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_nextMacroScope_3119_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_ngen_3120_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_auxDeclNGen_3121_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3145_, 5, v_cache_3122_);
lean_ctor_set(v_reuseFailAlloc_3145_, 6, v_recordedDeps_3123_);
lean_ctor_set(v_reuseFailAlloc_3145_, 7, v_messages_3124_);
lean_ctor_set(v_reuseFailAlloc_3145_, 8, v_infoState_3125_);
lean_ctor_set(v_reuseFailAlloc_3145_, 9, v_snapshotTasks_3126_);
v___x_3140_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = lean_st_ref_put(v___y_3093_, v___x_3140_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3134_);
v___x_3143_ = v___x_3114_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3134_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3151_, lean_object* v_data_3152_, lean_object* v_ref_3153_, lean_object* v_msg_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3151_, v_data_3152_, v_ref_3153_, v_msg_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3161_){
_start:
{
if (lean_obj_tag(v_x_3161_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
v_a_3163_ = lean_ctor_get(v_x_3161_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_x_3161_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v_x_3161_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v_x_3161_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set_tag(v___x_3165_, 1);
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_a_3171_ = lean_ctor_get(v_x_3161_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_x_3161_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v_x_3161_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v_x_3161_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 0);
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3179_);
return v_res_3181_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3182_; double v___x_3183_; 
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_float_of_nat(v___x_3182_);
return v___x_3183_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3186_ = l_Lean_stringToMessageData(v___x_3185_);
return v___x_3186_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3187_; double v___x_3188_; 
v___x_3187_ = lean_unsigned_to_nat(1000u);
v___x_3188_ = lean_float_of_nat(v___x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3189_, uint8_t v_collapsed_3190_, lean_object* v_tag_3191_, lean_object* v_opts_3192_, uint8_t v_clsEnabled_3193_, lean_object* v_oldTraces_3194_, lean_object* v_msg_3195_, lean_object* v_resStartStop_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_fst_3202_; lean_object* v_snd_3203_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v_data_3207_; lean_object* v_fst_3218_; lean_object* v_snd_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; lean_object* v___y_3223_; lean_object* v_a_3224_; uint8_t v___y_3239_; double v___y_3271_; 
v_fst_3202_ = lean_ctor_get(v_resStartStop_3196_, 0);
lean_inc(v_fst_3202_);
v_snd_3203_ = lean_ctor_get(v_resStartStop_3196_, 1);
lean_inc(v_snd_3203_);
lean_dec_ref(v_resStartStop_3196_);
v_fst_3218_ = lean_ctor_get(v_snd_3203_, 0);
lean_inc(v_fst_3218_);
v_snd_3219_ = lean_ctor_get(v_snd_3203_, 1);
lean_inc(v_snd_3219_);
lean_dec(v_snd_3203_);
v___x_3220_ = l_Lean_trace_profiler;
v___x_3221_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3192_, v___x_3220_);
if (v___x_3221_ == 0)
{
v___y_3239_ = v___x_3221_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3277_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3192_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; double v___x_3280_; double v___x_3281_; double v___x_3282_; 
v___x_3278_ = l_Lean_trace_profiler_threshold;
v___x_3279_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3192_, v___x_3278_);
v___x_3280_ = lean_float_of_nat(v___x_3279_);
v___x_3281_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3282_ = lean_float_div(v___x_3280_, v___x_3281_);
v___y_3271_ = v___x_3282_;
goto v___jp_3270_;
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; double v___x_3285_; 
v___x_3283_ = l_Lean_trace_profiler_threshold;
v___x_3284_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3192_, v___x_3283_);
v___x_3285_ = lean_float_of_nat(v___x_3284_);
v___y_3271_ = v___x_3285_;
goto v___jp_3270_;
}
}
v___jp_3204_:
{
lean_object* v___x_3208_; 
lean_inc(v___y_3205_);
v___x_3208_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3194_, v_data_3207_, v___y_3205_, v___y_3206_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v___x_3209_; 
lean_dec_ref_known(v___x_3208_, 1);
v___x_3209_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3202_);
return v___x_3209_;
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_fst_3202_);
v_a_3210_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3208_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3208_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
v___jp_3222_:
{
uint8_t v_result_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; double v___x_3228_; lean_object* v_data_3229_; 
v_result_3225_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3202_);
v___x_3226_ = lean_box(v_result_3225_);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
v___x_3228_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3191_);
lean_inc_ref(v___x_3227_);
lean_inc(v_cls_3189_);
v_data_3229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3229_, 0, v_cls_3189_);
lean_ctor_set(v_data_3229_, 1, v___x_3227_);
lean_ctor_set(v_data_3229_, 2, v_tag_3191_);
lean_ctor_set_float(v_data_3229_, sizeof(void*)*3, v___x_3228_);
lean_ctor_set_float(v_data_3229_, sizeof(void*)*3 + 8, v___x_3228_);
lean_ctor_set_uint8(v_data_3229_, sizeof(void*)*3 + 16, v_collapsed_3190_);
if (v___x_3221_ == 0)
{
lean_dec_ref_known(v___x_3227_, 1);
lean_dec(v_snd_3219_);
lean_dec(v_fst_3218_);
lean_dec_ref(v_tag_3191_);
lean_dec(v_cls_3189_);
v___y_3205_ = v___y_3223_;
v___y_3206_ = v_a_3224_;
v_data_3207_ = v_data_3229_;
goto v___jp_3204_;
}
else
{
lean_object* v_data_3230_; double v___x_3231_; double v___x_3232_; 
lean_dec_ref_known(v_data_3229_, 3);
v_data_3230_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3230_, 0, v_cls_3189_);
lean_ctor_set(v_data_3230_, 1, v___x_3227_);
lean_ctor_set(v_data_3230_, 2, v_tag_3191_);
v___x_3231_ = lean_unbox_float(v_fst_3218_);
lean_dec(v_fst_3218_);
lean_ctor_set_float(v_data_3230_, sizeof(void*)*3, v___x_3231_);
v___x_3232_ = lean_unbox_float(v_snd_3219_);
lean_dec(v_snd_3219_);
lean_ctor_set_float(v_data_3230_, sizeof(void*)*3 + 8, v___x_3232_);
lean_ctor_set_uint8(v_data_3230_, sizeof(void*)*3 + 16, v_collapsed_3190_);
v___y_3205_ = v___y_3223_;
v___y_3206_ = v_a_3224_;
v_data_3207_ = v_data_3230_;
goto v___jp_3204_;
}
}
v___jp_3233_:
{
lean_object* v_ref_3234_; lean_object* v___x_3235_; 
v_ref_3234_ = lean_ctor_get(v___y_3199_, 2);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc(v___y_3198_);
lean_inc_ref(v___y_3197_);
lean_inc(v_fst_3202_);
v___x_3235_ = lean_apply_6(v_msg_3195_, v_fst_3202_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, lean_box(0));
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___y_3223_ = v_ref_3234_;
v_a_3224_ = v_a_3236_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3237_; 
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3223_ = v_ref_3234_;
v_a_3224_ = v___x_3237_;
goto v___jp_3222_;
}
}
v___jp_3238_:
{
if (v_clsEnabled_3193_ == 0)
{
if (v___y_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v_traceState_3241_; lean_object* v_env_3242_; lean_object* v_nextMacroScope_3243_; lean_object* v_ngen_3244_; lean_object* v_auxDeclNGen_3245_; lean_object* v_cache_3246_; lean_object* v_recordedDeps_3247_; lean_object* v_messages_3248_; lean_object* v_infoState_3249_; lean_object* v_snapshotTasks_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_snd_3219_);
lean_dec(v_fst_3218_);
lean_dec_ref(v_msg_3195_);
lean_dec_ref(v_tag_3191_);
lean_dec(v_cls_3189_);
v___x_3240_ = lean_st_ref_take(v___y_3200_);
v_traceState_3241_ = lean_ctor_get(v___x_3240_, 4);
v_env_3242_ = lean_ctor_get(v___x_3240_, 0);
v_nextMacroScope_3243_ = lean_ctor_get(v___x_3240_, 1);
v_ngen_3244_ = lean_ctor_get(v___x_3240_, 2);
v_auxDeclNGen_3245_ = lean_ctor_get(v___x_3240_, 3);
v_cache_3246_ = lean_ctor_get(v___x_3240_, 5);
v_recordedDeps_3247_ = lean_ctor_get(v___x_3240_, 6);
v_messages_3248_ = lean_ctor_get(v___x_3240_, 7);
v_infoState_3249_ = lean_ctor_get(v___x_3240_, 8);
v_snapshotTasks_3250_ = lean_ctor_get(v___x_3240_, 9);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3252_ = v___x_3240_;
v_isShared_3253_ = v_isSharedCheck_3269_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_snapshotTasks_3250_);
lean_inc(v_infoState_3249_);
lean_inc(v_messages_3248_);
lean_inc(v_recordedDeps_3247_);
lean_inc(v_cache_3246_);
lean_inc(v_traceState_3241_);
lean_inc(v_auxDeclNGen_3245_);
lean_inc(v_ngen_3244_);
lean_inc(v_nextMacroScope_3243_);
lean_inc(v_env_3242_);
lean_dec(v___x_3240_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3269_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
uint64_t v_tid_3254_; lean_object* v_traces_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3268_; 
v_tid_3254_ = lean_ctor_get_uint64(v_traceState_3241_, sizeof(void*)*1);
v_traces_3255_ = lean_ctor_get(v_traceState_3241_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_traceState_3241_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3257_ = v_traceState_3241_;
v_isShared_3258_ = v_isSharedCheck_3268_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_traces_3255_);
lean_dec(v_traceState_3241_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3268_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3194_, v_traces_3255_);
lean_dec_ref(v_traces_3255_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3259_);
v___x_3261_ = v___x_3257_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3259_);
lean_ctor_set_uint64(v_reuseFailAlloc_3267_, sizeof(void*)*1, v_tid_3254_);
v___x_3261_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3263_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v___x_3261_);
v___x_3263_ = v___x_3252_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_env_3242_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_nextMacroScope_3243_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_ngen_3244_);
lean_ctor_set(v_reuseFailAlloc_3266_, 3, v_auxDeclNGen_3245_);
lean_ctor_set(v_reuseFailAlloc_3266_, 4, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3266_, 5, v_cache_3246_);
lean_ctor_set(v_reuseFailAlloc_3266_, 6, v_recordedDeps_3247_);
lean_ctor_set(v_reuseFailAlloc_3266_, 7, v_messages_3248_);
lean_ctor_set(v_reuseFailAlloc_3266_, 8, v_infoState_3249_);
lean_ctor_set(v_reuseFailAlloc_3266_, 9, v_snapshotTasks_3250_);
v___x_3263_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = lean_st_ref_put(v___y_3200_, v___x_3263_);
v___x_3265_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3202_);
return v___x_3265_;
}
}
}
}
}
else
{
goto v___jp_3233_;
}
}
else
{
goto v___jp_3233_;
}
}
v___jp_3270_:
{
double v___x_3272_; double v___x_3273_; double v___x_3274_; uint8_t v___x_3275_; 
v___x_3272_ = lean_unbox_float(v_snd_3219_);
v___x_3273_ = lean_unbox_float(v_fst_3218_);
v___x_3274_ = lean_float_sub(v___x_3272_, v___x_3273_);
v___x_3275_ = lean_float_decLt(v___y_3271_, v___x_3274_);
v___y_3239_ = v___x_3275_;
goto v___jp_3238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3286_, lean_object* v_collapsed_3287_, lean_object* v_tag_3288_, lean_object* v_opts_3289_, lean_object* v_clsEnabled_3290_, lean_object* v_oldTraces_3291_, lean_object* v_msg_3292_, lean_object* v_resStartStop_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
uint8_t v_collapsed_boxed_3299_; uint8_t v_clsEnabled_boxed_3300_; lean_object* v_res_3301_; 
v_collapsed_boxed_3299_ = lean_unbox(v_collapsed_3287_);
v_clsEnabled_boxed_3300_ = lean_unbox(v_clsEnabled_3290_);
v_res_3301_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3286_, v_collapsed_boxed_3299_, v_tag_3288_, v_opts_3289_, v_clsEnabled_boxed_3300_, v_oldTraces_3291_, v_msg_3292_, v_resStartStop_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec_ref(v_opts_3289_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
if (lean_obj_tag(v_a_3302_) == 0)
{
lean_object* v___x_3304_; 
v___x_3304_ = l_List_reverse___redArg(v_a_3303_);
return v___x_3304_;
}
else
{
lean_object* v_head_3305_; lean_object* v_tail_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3315_; 
v_head_3305_ = lean_ctor_get(v_a_3302_, 0);
v_tail_3306_ = lean_ctor_get(v_a_3302_, 1);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_a_3302_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3308_ = v_a_3302_;
v_isShared_3309_ = v_isSharedCheck_3315_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_tail_3306_);
lean_inc(v_head_3305_);
lean_dec(v_a_3302_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3315_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3310_ = l_Lean_MessageData_ofExpr(v_head_3305_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v_a_3303_);
lean_ctor_set(v___x_3308_, 0, v___x_3310_);
v___x_3312_ = v___x_3308_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_a_3303_);
v___x_3312_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
v_a_3302_ = v_tail_3306_;
v_a_3303_ = v___x_3312_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3316_, lean_object* v_xs_3317_, lean_object* v_x_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3324_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3325_ = l_Lean_MessageData_ofName(v_f_3316_);
v___x_3326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3326_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = lean_array_to_list(v_xs_3317_);
v___x_3330_ = lean_box(0);
v___x_3331_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3329_, v___x_3330_);
v___x_3332_ = l_Lean_MessageData_ofList(v___x_3331_);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3328_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3335_, lean_object* v_xs_3336_, lean_object* v_x_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3335_, v_xs_3336_, v_x_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec_ref(v_x_3337_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3346_, lean_object* v_msg_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_ref_3353_; lean_object* v___x_3354_; lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3400_; 
v_ref_3353_ = lean_ctor_get(v___y_3350_, 2);
v___x_3354_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3400_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3400_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v_traceState_3360_; lean_object* v_env_3361_; lean_object* v_nextMacroScope_3362_; lean_object* v_ngen_3363_; lean_object* v_auxDeclNGen_3364_; lean_object* v_cache_3365_; lean_object* v_recordedDeps_3366_; lean_object* v_messages_3367_; lean_object* v_infoState_3368_; lean_object* v_snapshotTasks_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3399_; 
v___x_3359_ = lean_st_ref_take(v___y_3351_);
v_traceState_3360_ = lean_ctor_get(v___x_3359_, 4);
v_env_3361_ = lean_ctor_get(v___x_3359_, 0);
v_nextMacroScope_3362_ = lean_ctor_get(v___x_3359_, 1);
v_ngen_3363_ = lean_ctor_get(v___x_3359_, 2);
v_auxDeclNGen_3364_ = lean_ctor_get(v___x_3359_, 3);
v_cache_3365_ = lean_ctor_get(v___x_3359_, 5);
v_recordedDeps_3366_ = lean_ctor_get(v___x_3359_, 6);
v_messages_3367_ = lean_ctor_get(v___x_3359_, 7);
v_infoState_3368_ = lean_ctor_get(v___x_3359_, 8);
v_snapshotTasks_3369_ = lean_ctor_get(v___x_3359_, 9);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3371_ = v___x_3359_;
v_isShared_3372_ = v_isSharedCheck_3399_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_snapshotTasks_3369_);
lean_inc(v_infoState_3368_);
lean_inc(v_messages_3367_);
lean_inc(v_recordedDeps_3366_);
lean_inc(v_cache_3365_);
lean_inc(v_traceState_3360_);
lean_inc(v_auxDeclNGen_3364_);
lean_inc(v_ngen_3363_);
lean_inc(v_nextMacroScope_3362_);
lean_inc(v_env_3361_);
lean_dec(v___x_3359_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3399_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint64_t v_tid_3373_; lean_object* v_traces_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3398_; 
v_tid_3373_ = lean_ctor_get_uint64(v_traceState_3360_, sizeof(void*)*1);
v_traces_3374_ = lean_ctor_get(v_traceState_3360_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_traceState_3360_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3376_ = v_traceState_3360_;
v_isShared_3377_ = v_isSharedCheck_3398_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_traces_3374_);
lean_dec(v_traceState_3360_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3398_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; double v___x_3380_; uint8_t v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_box(0);
v___x_3380_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3381_ = 0;
v___x_3382_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3383_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3383_, 0, v_cls_3346_);
lean_ctor_set(v___x_3383_, 1, v___x_3379_);
lean_ctor_set(v___x_3383_, 2, v___x_3382_);
lean_ctor_set_float(v___x_3383_, sizeof(void*)*3, v___x_3380_);
lean_ctor_set_float(v___x_3383_, sizeof(void*)*3 + 8, v___x_3380_);
lean_ctor_set_uint8(v___x_3383_, sizeof(void*)*3 + 16, v___x_3381_);
v___x_3384_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3385_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v_a_3355_);
lean_ctor_set(v___x_3385_, 2, v___x_3384_);
lean_inc(v_ref_3353_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_ref_3353_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = l_Lean_PersistentArray_push___redArg(v_traces_3374_, v___x_3386_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3387_);
v___x_3389_ = v___x_3376_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3387_);
lean_ctor_set_uint64(v_reuseFailAlloc_3397_, sizeof(void*)*1, v_tid_3373_);
v___x_3389_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3391_; 
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 4, v___x_3389_);
v___x_3391_ = v___x_3371_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_env_3361_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_nextMacroScope_3362_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_ngen_3363_);
lean_ctor_set(v_reuseFailAlloc_3396_, 3, v_auxDeclNGen_3364_);
lean_ctor_set(v_reuseFailAlloc_3396_, 4, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3396_, 5, v_cache_3365_);
lean_ctor_set(v_reuseFailAlloc_3396_, 6, v_recordedDeps_3366_);
lean_ctor_set(v_reuseFailAlloc_3396_, 7, v_messages_3367_);
lean_ctor_set(v_reuseFailAlloc_3396_, 8, v_infoState_3368_);
lean_ctor_set(v_reuseFailAlloc_3396_, 9, v_snapshotTasks_3369_);
v___x_3391_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_st_ref_put(v___y_3351_, v___x_3391_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3378_);
v___x_3394_ = v___x_3357_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3378_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3401_, lean_object* v_msg_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3401_, v_msg_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3409_, lean_object* v_xs_3410_, lean_object* v_k_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_toCold_3417_; lean_object* v_options_3418_; uint8_t v_hasTrace_3419_; 
v_toCold_3417_ = lean_ctor_get(v_a_3414_, 0);
v_options_3418_ = lean_ctor_get(v_toCold_3417_, 2);
v_hasTrace_3419_ = lean_ctor_get_uint8(v_options_3418_, sizeof(void*)*1);
if (v_hasTrace_3419_ == 0)
{
lean_object* v___x_3420_; 
lean_dec_ref(v_xs_3410_);
lean_dec(v_f_3409_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
lean_inc(v_a_3413_);
lean_inc_ref(v_a_3412_);
v___x_3420_ = lean_apply_5(v_k_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, lean_box(0));
return v___x_3420_;
}
else
{
lean_object* v_inheritedTraceOptions_3421_; lean_object* v___f_3422_; lean_object* v___y_3424_; lean_object* v___y_3425_; uint8_t v___y_3426_; lean_object* v___y_3450_; lean_object* v_a_3451_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v_a_3461_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v_a_3476_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; uint8_t v___y_3482_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v_a_3492_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v_a_3498_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v_a_3503_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v_a_3515_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; uint8_t v___y_3521_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v_a_3531_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v_a_3537_; 
v_inheritedTraceOptions_3421_ = lean_ctor_get(v_toCold_3417_, 11);
v___f_3422_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3422_, 0, v_f_3409_);
lean_closure_set(v___f_3422_, 1, v_xs_3410_);
v___x_3454_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3455_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3457_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3421_, v_options_3418_, v___x_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3564_ = l_Lean_trace_profiler;
v___x_3565_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3418_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; 
lean_dec_ref(v___f_3422_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
lean_inc(v_a_3413_);
lean_inc_ref(v_a_3412_);
v___x_3566_ = lean_apply_5(v_k_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, lean_box(0));
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
v___x_3568_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3569_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3570_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3421_, v_options_3418_, v___x_3569_);
if (v___x_3570_ == 0)
{
lean_dec(v_a_3567_);
return v___x_3566_;
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_dec_ref_known(v___x_3566_, 1);
lean_inc(v_a_3567_);
v___x_3571_ = l_Lean_MessageData_ofExpr(v_a_3567_);
v___x_3572_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3568_, v___x_3571_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; 
v_unused_3580_ = lean_ctor_get(v___x_3572_, 0);
lean_dec(v_unused_3580_);
v___x_3574_ = v___x_3572_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v___x_3572_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v_a_3567_);
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3567_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v_a_3567_);
v_a_3581_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3572_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3572_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
lean_inc(v_a_3581_);
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
v___y_3450_ = v___x_3586_;
v_a_3451_ = v_a_3581_;
goto v___jp_3449_;
}
}
}
}
}
else
{
lean_object* v_a_3589_; 
v_a_3589_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3589_);
v___y_3450_ = v___x_3566_;
v_a_3451_ = v_a_3589_;
goto v___jp_3449_;
}
}
else
{
goto v___jp_3539_;
}
}
else
{
goto v___jp_3539_;
}
v___jp_3423_:
{
if (v___y_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
lean_dec_ref(v___y_3424_);
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3428_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3429_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3421_, v_options_3418_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___y_3425_);
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
lean_inc_ref(v___y_3425_);
v___x_3431_ = l_Lean_Exception_toMessageData(v___y_3425_);
v___x_3432_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3427_, v___x_3431_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; 
v_unused_3440_ = lean_ctor_get(v___x_3432_, 0);
lean_dec(v_unused_3440_);
v___x_3434_ = v___x_3432_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_dec(v___x_3432_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 0, v___y_3425_);
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___y_3425_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec_ref(v___y_3425_);
v_a_3441_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3432_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3432_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3425_);
return v___y_3424_;
}
}
v___jp_3449_:
{
uint8_t v___x_3452_; 
v___x_3452_ = l_Lean_Exception_isInterrupt(v_a_3451_);
if (v___x_3452_ == 0)
{
uint8_t v___x_3453_; 
lean_inc_ref(v_a_3451_);
v___x_3453_ = l_Lean_Exception_isRuntime(v_a_3451_);
v___y_3424_ = v___y_3450_;
v___y_3425_ = v_a_3451_;
v___y_3426_ = v___x_3453_;
goto v___jp_3423_;
}
else
{
v___y_3424_ = v___y_3450_;
v___y_3425_ = v_a_3451_;
v___y_3426_ = v___x_3452_;
goto v___jp_3423_;
}
}
v___jp_3458_:
{
lean_object* v___x_3462_; double v___x_3463_; double v___x_3464_; double v___x_3465_; double v___x_3466_; double v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3462_ = lean_io_mono_nanos_now();
v___x_3463_ = lean_float_of_nat(v___y_3459_);
v___x_3464_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3465_ = lean_float_div(v___x_3463_, v___x_3464_);
v___x_3466_ = lean_float_of_nat(v___x_3462_);
v___x_3467_ = lean_float_div(v___x_3466_, v___x_3464_);
v___x_3468_ = lean_box_float(v___x_3465_);
v___x_3469_ = lean_box_float(v___x_3467_);
v___x_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v_a_3461_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3454_, v_hasTrace_3419_, v___x_3455_, v_options_3418_, v___x_3457_, v___y_3460_, v___f_3422_, v___x_3471_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
return v___x_3472_;
}
v___jp_3473_:
{
lean_object* v___x_3477_; 
v___x_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_a_3476_);
v___y_3459_ = v___y_3474_;
v___y_3460_ = v___y_3475_;
v_a_3461_ = v___x_3477_;
goto v___jp_3458_;
}
v___jp_3478_:
{
if (v___y_3482_ == 0)
{
lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3483_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3484_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3485_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3421_, v_options_3418_, v___x_3484_);
if (v___x_3485_ == 0)
{
v___y_3474_ = v___y_3479_;
v___y_3475_ = v___y_3481_;
v_a_3476_ = v___y_3480_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_inc_ref(v___y_3480_);
v___x_3486_ = l_Lean_Exception_toMessageData(v___y_3480_);
v___x_3487_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3483_, v___x_3486_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_dec_ref_known(v___x_3487_, 1);
v___y_3474_ = v___y_3479_;
v___y_3475_ = v___y_3481_;
v_a_3476_ = v___y_3480_;
goto v___jp_3473_;
}
else
{
lean_object* v_a_3488_; 
lean_dec_ref(v___y_3480_);
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___y_3474_ = v___y_3479_;
v___y_3475_ = v___y_3481_;
v_a_3476_ = v_a_3488_;
goto v___jp_3473_;
}
}
}
else
{
v___y_3474_ = v___y_3479_;
v___y_3475_ = v___y_3481_;
v_a_3476_ = v___y_3480_;
goto v___jp_3473_;
}
}
v___jp_3489_:
{
uint8_t v___x_3493_; 
v___x_3493_ = l_Lean_Exception_isInterrupt(v_a_3492_);
if (v___x_3493_ == 0)
{
uint8_t v___x_3494_; 
lean_inc_ref(v_a_3492_);
v___x_3494_ = l_Lean_Exception_isRuntime(v_a_3492_);
v___y_3479_ = v___y_3490_;
v___y_3480_ = v_a_3492_;
v___y_3481_ = v___y_3491_;
v___y_3482_ = v___x_3494_;
goto v___jp_3478_;
}
else
{
v___y_3479_ = v___y_3490_;
v___y_3480_ = v_a_3492_;
v___y_3481_ = v___y_3491_;
v___y_3482_ = v___x_3493_;
goto v___jp_3478_;
}
}
v___jp_3495_:
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_a_3498_);
v___y_3459_ = v___y_3496_;
v___y_3460_ = v___y_3497_;
v_a_3461_ = v___x_3499_;
goto v___jp_3458_;
}
v___jp_3500_:
{
lean_object* v___x_3504_; double v___x_3505_; double v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3504_ = lean_io_get_num_heartbeats();
v___x_3505_ = lean_float_of_nat(v___y_3501_);
v___x_3506_ = lean_float_of_nat(v___x_3504_);
v___x_3507_ = lean_box_float(v___x_3505_);
v___x_3508_ = lean_box_float(v___x_3506_);
v___x_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3507_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_a_3503_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
v___x_3511_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3454_, v_hasTrace_3419_, v___x_3455_, v_options_3418_, v___x_3457_, v___y_3502_, v___f_3422_, v___x_3510_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
return v___x_3511_;
}
v___jp_3512_:
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_a_3515_);
v___y_3501_ = v___y_3513_;
v___y_3502_ = v___y_3514_;
v_a_3503_ = v___x_3516_;
goto v___jp_3500_;
}
v___jp_3517_:
{
if (v___y_3521_ == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v___x_3522_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3523_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3524_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3421_, v_options_3418_, v___x_3523_);
if (v___x_3524_ == 0)
{
v___y_3513_ = v___y_3519_;
v___y_3514_ = v___y_3520_;
v_a_3515_ = v___y_3518_;
goto v___jp_3512_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_inc_ref(v___y_3518_);
v___x_3525_ = l_Lean_Exception_toMessageData(v___y_3518_);
v___x_3526_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3522_, v___x_3525_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_dec_ref_known(v___x_3526_, 1);
v___y_3513_ = v___y_3519_;
v___y_3514_ = v___y_3520_;
v_a_3515_ = v___y_3518_;
goto v___jp_3512_;
}
else
{
lean_object* v_a_3527_; 
lean_dec_ref(v___y_3518_);
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___y_3513_ = v___y_3519_;
v___y_3514_ = v___y_3520_;
v_a_3515_ = v_a_3527_;
goto v___jp_3512_;
}
}
}
else
{
v___y_3513_ = v___y_3519_;
v___y_3514_ = v___y_3520_;
v_a_3515_ = v___y_3518_;
goto v___jp_3512_;
}
}
v___jp_3528_:
{
uint8_t v___x_3532_; 
v___x_3532_ = l_Lean_Exception_isInterrupt(v_a_3531_);
if (v___x_3532_ == 0)
{
uint8_t v___x_3533_; 
lean_inc_ref(v_a_3531_);
v___x_3533_ = l_Lean_Exception_isRuntime(v_a_3531_);
v___y_3518_ = v_a_3531_;
v___y_3519_ = v___y_3529_;
v___y_3520_ = v___y_3530_;
v___y_3521_ = v___x_3533_;
goto v___jp_3517_;
}
else
{
v___y_3518_ = v_a_3531_;
v___y_3519_ = v___y_3529_;
v___y_3520_ = v___y_3530_;
v___y_3521_ = v___x_3532_;
goto v___jp_3517_;
}
}
v___jp_3534_:
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v_a_3537_);
v___y_3501_ = v___y_3535_;
v___y_3502_ = v___y_3536_;
v_a_3503_ = v___x_3538_;
goto v___jp_3500_;
}
v___jp_3539_:
{
lean_object* v___x_3540_; lean_object* v_a_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3540_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3415_);
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref(v___x_3540_);
v___x_3542_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3543_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3418_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = lean_io_mono_nanos_now();
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
lean_inc(v_a_3413_);
lean_inc_ref(v_a_3412_);
v___x_3545_ = lean_apply_5(v_k_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, lean_box(0));
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3548_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3549_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3421_, v_options_3418_, v___x_3548_);
if (v___x_3549_ == 0)
{
v___y_3496_ = v___x_3544_;
v___y_3497_ = v_a_3541_;
v_a_3498_ = v_a_3546_;
goto v___jp_3495_;
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_inc(v_a_3546_);
v___x_3550_ = l_Lean_MessageData_ofExpr(v_a_3546_);
v___x_3551_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3547_, v___x_3550_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_dec_ref_known(v___x_3551_, 1);
v___y_3496_ = v___x_3544_;
v___y_3497_ = v_a_3541_;
v_a_3498_ = v_a_3546_;
goto v___jp_3495_;
}
else
{
lean_object* v_a_3552_; 
lean_dec(v_a_3546_);
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v___y_3490_ = v___x_3544_;
v___y_3491_ = v_a_3541_;
v_a_3492_ = v_a_3552_;
goto v___jp_3489_;
}
}
}
else
{
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3545_, 1);
v___y_3490_ = v___x_3544_;
v___y_3491_ = v_a_3541_;
v_a_3492_ = v_a_3553_;
goto v___jp_3489_;
}
}
else
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
lean_inc(v_a_3413_);
lean_inc_ref(v_a_3412_);
v___x_3555_ = lean_apply_5(v_k_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, lean_box(0));
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3555_, 1);
v___x_3557_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3558_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3559_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3421_, v_options_3418_, v___x_3558_);
if (v___x_3559_ == 0)
{
v___y_3535_ = v___x_3554_;
v___y_3536_ = v_a_3541_;
v_a_3537_ = v_a_3556_;
goto v___jp_3534_;
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_inc(v_a_3556_);
v___x_3560_ = l_Lean_MessageData_ofExpr(v_a_3556_);
v___x_3561_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3557_, v___x_3560_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_dec_ref_known(v___x_3561_, 1);
v___y_3535_ = v___x_3554_;
v___y_3536_ = v_a_3541_;
v_a_3537_ = v_a_3556_;
goto v___jp_3534_;
}
else
{
lean_object* v_a_3562_; 
lean_dec(v_a_3556_);
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
v___y_3529_ = v___x_3554_;
v___y_3530_ = v_a_3541_;
v_a_3531_ = v_a_3562_;
goto v___jp_3528_;
}
}
}
else
{
lean_object* v_a_3563_; 
v_a_3563_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3555_, 1);
v___y_3529_ = v___x_3554_;
v___y_3530_ = v_a_3541_;
v_a_3531_ = v_a_3563_;
goto v___jp_3528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3590_, lean_object* v_xs_3591_, lean_object* v_k_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3590_, v_xs_3591_, v_k_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3599_, lean_object* v_xs_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v___f_3606_; uint8_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_inc_ref(v_xs_3600_);
lean_inc(v_constName_3599_);
v___f_3606_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3606_, 0, v_constName_3599_);
lean_closure_set(v___f_3606_, 1, v_xs_3600_);
v___x_3607_ = 0;
v___x_3608_ = lean_box(v___x_3607_);
v___x_3609_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3609_, 0, lean_box(0));
lean_closure_set(v___x_3609_, 1, v___f_3606_);
lean_closure_set(v___x_3609_, 2, v___x_3608_);
v___x_3610_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3599_, v_xs_3600_, v___x_3609_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3611_, lean_object* v_xs_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_Meta_mkAppM(v_constName_3611_, v_xs_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3631_, lean_object* v_x_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3632_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3639_, lean_object* v_x_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3639_, v_x_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3647_, lean_object* v_xs_3648_, lean_object* v_x_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3655_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3656_ = l_Lean_MessageData_ofExpr(v_f_3647_);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_array_to_list(v_xs_3648_);
v___x_3661_ = lean_box(0);
v___x_3662_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3660_, v___x_3661_);
v___x_3663_ = l_Lean_MessageData_ofList(v___x_3662_);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3659_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3666_, lean_object* v_xs_3667_, lean_object* v_x_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3666_, v_xs_3667_, v_x_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v_x_3668_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3675_, lean_object* v_xs_3676_, lean_object* v_k_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_toCold_3683_; lean_object* v_options_3684_; uint8_t v_hasTrace_3685_; 
v_toCold_3683_ = lean_ctor_get(v_a_3680_, 0);
v_options_3684_ = lean_ctor_get(v_toCold_3683_, 2);
v_hasTrace_3685_ = lean_ctor_get_uint8(v_options_3684_, sizeof(void*)*1);
if (v_hasTrace_3685_ == 0)
{
lean_object* v___x_3686_; 
lean_dec_ref(v_xs_3676_);
lean_dec_ref(v_f_3675_);
lean_inc(v_a_3681_);
lean_inc_ref(v_a_3680_);
lean_inc(v_a_3679_);
lean_inc_ref(v_a_3678_);
v___x_3686_ = lean_apply_5(v_k_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, lean_box(0));
return v___x_3686_;
}
else
{
lean_object* v_inheritedTraceOptions_3687_; lean_object* v___f_3688_; lean_object* v___y_3690_; lean_object* v___y_3691_; uint8_t v___y_3692_; lean_object* v___y_3716_; lean_object* v_a_3717_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v_a_3727_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v_a_3742_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; uint8_t v___y_3748_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v_a_3758_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v_a_3764_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v_a_3769_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v_a_3781_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; uint8_t v___y_3787_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v_a_3797_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v_a_3803_; 
v_inheritedTraceOptions_3687_ = lean_ctor_get(v_toCold_3683_, 11);
v___f_3688_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3688_, 0, v_f_3675_);
lean_closure_set(v___f_3688_, 1, v_xs_3676_);
v___x_3720_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3721_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3722_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3684_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3830_; uint8_t v___x_3831_; 
v___x_3830_ = l_Lean_trace_profiler;
v___x_3831_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3684_, v___x_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; 
lean_dec_ref(v___f_3688_);
lean_inc(v_a_3681_);
lean_inc_ref(v_a_3680_);
lean_inc(v_a_3679_);
lean_inc_ref(v_a_3678_);
v___x_3832_ = lean_apply_5(v_k_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, lean_box(0));
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
v___x_3834_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3835_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3836_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3684_, v___x_3835_);
if (v___x_3836_ == 0)
{
lean_dec(v_a_3833_);
return v___x_3832_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
lean_dec_ref_known(v___x_3832_, 1);
lean_inc(v_a_3833_);
v___x_3837_ = l_Lean_MessageData_ofExpr(v_a_3833_);
v___x_3838_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3834_, v___x_3837_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3845_ == 0)
{
lean_object* v_unused_3846_; 
v_unused_3846_ = lean_ctor_get(v___x_3838_, 0);
lean_dec(v_unused_3846_);
v___x_3840_ = v___x_3838_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_dec(v___x_3838_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_a_3833_);
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3833_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec(v_a_3833_);
v_a_3847_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3838_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3838_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
lean_inc(v_a_3847_);
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
v___y_3716_ = v___x_3852_;
v_a_3717_ = v_a_3847_;
goto v___jp_3715_;
}
}
}
}
}
else
{
lean_object* v_a_3855_; 
v_a_3855_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3855_);
v___y_3716_ = v___x_3832_;
v_a_3717_ = v_a_3855_;
goto v___jp_3715_;
}
}
else
{
goto v___jp_3805_;
}
}
else
{
goto v___jp_3805_;
}
v___jp_3689_:
{
if (v___y_3692_ == 0)
{
lean_object* v___x_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
lean_dec_ref(v___y_3690_);
v___x_3693_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3694_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3684_, v___x_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___y_3691_);
return v___x_3696_;
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
lean_inc_ref(v___y_3691_);
v___x_3697_ = l_Lean_Exception_toMessageData(v___y_3691_);
v___x_3698_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3693_, v___x_3697_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; 
v_unused_3706_ = lean_ctor_get(v___x_3698_, 0);
lean_dec(v_unused_3706_);
v___x_3700_ = v___x_3698_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_dec(v___x_3698_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
lean_ctor_set_tag(v___x_3700_, 1);
lean_ctor_set(v___x_3700_, 0, v___y_3691_);
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___y_3691_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec_ref(v___y_3691_);
v_a_3707_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3698_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3698_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3691_);
return v___y_3690_;
}
}
v___jp_3715_:
{
uint8_t v___x_3718_; 
v___x_3718_ = l_Lean_Exception_isInterrupt(v_a_3717_);
if (v___x_3718_ == 0)
{
uint8_t v___x_3719_; 
lean_inc_ref(v_a_3717_);
v___x_3719_ = l_Lean_Exception_isRuntime(v_a_3717_);
v___y_3690_ = v___y_3716_;
v___y_3691_ = v_a_3717_;
v___y_3692_ = v___x_3719_;
goto v___jp_3689_;
}
else
{
v___y_3690_ = v___y_3716_;
v___y_3691_ = v_a_3717_;
v___y_3692_ = v___x_3718_;
goto v___jp_3689_;
}
}
v___jp_3724_:
{
lean_object* v___x_3728_; double v___x_3729_; double v___x_3730_; double v___x_3731_; double v___x_3732_; double v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3728_ = lean_io_mono_nanos_now();
v___x_3729_ = lean_float_of_nat(v___y_3725_);
v___x_3730_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3731_ = lean_float_div(v___x_3729_, v___x_3730_);
v___x_3732_ = lean_float_of_nat(v___x_3728_);
v___x_3733_ = lean_float_div(v___x_3732_, v___x_3730_);
v___x_3734_ = lean_box_float(v___x_3731_);
v___x_3735_ = lean_box_float(v___x_3733_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v_a_3727_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3720_, v_hasTrace_3685_, v___x_3721_, v_options_3684_, v___x_3723_, v___y_3726_, v___f_3688_, v___x_3737_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
return v___x_3738_;
}
v___jp_3739_:
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v_a_3742_);
v___y_3725_ = v___y_3740_;
v___y_3726_ = v___y_3741_;
v_a_3727_ = v___x_3743_;
goto v___jp_3724_;
}
v___jp_3744_:
{
if (v___y_3748_ == 0)
{
lean_object* v___x_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3749_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3750_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3751_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3684_, v___x_3750_);
if (v___x_3751_ == 0)
{
v___y_3740_ = v___y_3746_;
v___y_3741_ = v___y_3747_;
v_a_3742_ = v___y_3745_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_inc_ref(v___y_3745_);
v___x_3752_ = l_Lean_Exception_toMessageData(v___y_3745_);
v___x_3753_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3749_, v___x_3752_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_dec_ref_known(v___x_3753_, 1);
v___y_3740_ = v___y_3746_;
v___y_3741_ = v___y_3747_;
v_a_3742_ = v___y_3745_;
goto v___jp_3739_;
}
else
{
lean_object* v_a_3754_; 
lean_dec_ref(v___y_3745_);
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3753_, 1);
v___y_3740_ = v___y_3746_;
v___y_3741_ = v___y_3747_;
v_a_3742_ = v_a_3754_;
goto v___jp_3739_;
}
}
}
else
{
v___y_3740_ = v___y_3746_;
v___y_3741_ = v___y_3747_;
v_a_3742_ = v___y_3745_;
goto v___jp_3739_;
}
}
v___jp_3755_:
{
uint8_t v___x_3759_; 
v___x_3759_ = l_Lean_Exception_isInterrupt(v_a_3758_);
if (v___x_3759_ == 0)
{
uint8_t v___x_3760_; 
lean_inc_ref(v_a_3758_);
v___x_3760_ = l_Lean_Exception_isRuntime(v_a_3758_);
v___y_3745_ = v_a_3758_;
v___y_3746_ = v___y_3756_;
v___y_3747_ = v___y_3757_;
v___y_3748_ = v___x_3760_;
goto v___jp_3744_;
}
else
{
v___y_3745_ = v_a_3758_;
v___y_3746_ = v___y_3756_;
v___y_3747_ = v___y_3757_;
v___y_3748_ = v___x_3759_;
goto v___jp_3744_;
}
}
v___jp_3761_:
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3765_, 0, v_a_3764_);
v___y_3725_ = v___y_3762_;
v___y_3726_ = v___y_3763_;
v_a_3727_ = v___x_3765_;
goto v___jp_3724_;
}
v___jp_3766_:
{
lean_object* v___x_3770_; double v___x_3771_; double v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3770_ = lean_io_get_num_heartbeats();
v___x_3771_ = lean_float_of_nat(v___y_3767_);
v___x_3772_ = lean_float_of_nat(v___x_3770_);
v___x_3773_ = lean_box_float(v___x_3771_);
v___x_3774_ = lean_box_float(v___x_3772_);
v___x_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3776_, 0, v_a_3769_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3720_, v_hasTrace_3685_, v___x_3721_, v_options_3684_, v___x_3723_, v___y_3768_, v___f_3688_, v___x_3776_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
return v___x_3777_;
}
v___jp_3778_:
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3782_, 0, v_a_3781_);
v___y_3767_ = v___y_3779_;
v___y_3768_ = v___y_3780_;
v_a_3769_ = v___x_3782_;
goto v___jp_3766_;
}
v___jp_3783_:
{
if (v___y_3787_ == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v___x_3788_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3789_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3684_, v___x_3789_);
if (v___x_3790_ == 0)
{
v___y_3779_ = v___y_3785_;
v___y_3780_ = v___y_3786_;
v_a_3781_ = v___y_3784_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_inc_ref(v___y_3784_);
v___x_3791_ = l_Lean_Exception_toMessageData(v___y_3784_);
v___x_3792_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3788_, v___x_3791_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_dec_ref_known(v___x_3792_, 1);
v___y_3779_ = v___y_3785_;
v___y_3780_ = v___y_3786_;
v_a_3781_ = v___y_3784_;
goto v___jp_3778_;
}
else
{
lean_object* v_a_3793_; 
lean_dec_ref(v___y_3784_);
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___y_3779_ = v___y_3785_;
v___y_3780_ = v___y_3786_;
v_a_3781_ = v_a_3793_;
goto v___jp_3778_;
}
}
}
else
{
v___y_3779_ = v___y_3785_;
v___y_3780_ = v___y_3786_;
v_a_3781_ = v___y_3784_;
goto v___jp_3778_;
}
}
v___jp_3794_:
{
uint8_t v___x_3798_; 
v___x_3798_ = l_Lean_Exception_isInterrupt(v_a_3797_);
if (v___x_3798_ == 0)
{
uint8_t v___x_3799_; 
lean_inc_ref(v_a_3797_);
v___x_3799_ = l_Lean_Exception_isRuntime(v_a_3797_);
v___y_3784_ = v_a_3797_;
v___y_3785_ = v___y_3795_;
v___y_3786_ = v___y_3796_;
v___y_3787_ = v___x_3799_;
goto v___jp_3783_;
}
else
{
v___y_3784_ = v_a_3797_;
v___y_3785_ = v___y_3795_;
v___y_3786_ = v___y_3796_;
v___y_3787_ = v___x_3798_;
goto v___jp_3783_;
}
}
v___jp_3800_:
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3804_, 0, v_a_3803_);
v___y_3767_ = v___y_3801_;
v___y_3768_ = v___y_3802_;
v_a_3769_ = v___x_3804_;
goto v___jp_3766_;
}
v___jp_3805_:
{
lean_object* v___x_3806_; lean_object* v_a_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v___x_3806_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3681_);
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3806_);
v___x_3808_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3809_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3684_, v___x_3808_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = lean_io_mono_nanos_now();
lean_inc(v_a_3681_);
lean_inc_ref(v_a_3680_);
lean_inc(v_a_3679_);
lean_inc_ref(v_a_3678_);
v___x_3811_ = lean_apply_5(v_k_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, lean_box(0));
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v___x_3813_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3814_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3815_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3684_, v___x_3814_);
if (v___x_3815_ == 0)
{
v___y_3762_ = v___x_3810_;
v___y_3763_ = v_a_3807_;
v_a_3764_ = v_a_3812_;
goto v___jp_3761_;
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
lean_inc(v_a_3812_);
v___x_3816_ = l_Lean_MessageData_ofExpr(v_a_3812_);
v___x_3817_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3813_, v___x_3816_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_dec_ref_known(v___x_3817_, 1);
v___y_3762_ = v___x_3810_;
v___y_3763_ = v_a_3807_;
v_a_3764_ = v_a_3812_;
goto v___jp_3761_;
}
else
{
lean_object* v_a_3818_; 
lean_dec(v_a_3812_);
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
v___y_3756_ = v___x_3810_;
v___y_3757_ = v_a_3807_;
v_a_3758_ = v_a_3818_;
goto v___jp_3755_;
}
}
}
else
{
lean_object* v_a_3819_; 
v_a_3819_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v___x_3811_, 1);
v___y_3756_ = v___x_3810_;
v___y_3757_ = v_a_3807_;
v_a_3758_ = v_a_3819_;
goto v___jp_3755_;
}
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3681_);
lean_inc_ref(v_a_3680_);
lean_inc(v_a_3679_);
lean_inc_ref(v_a_3678_);
v___x_3821_ = lean_apply_5(v_k_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, lean_box(0));
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v___x_3823_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3824_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3825_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3684_, v___x_3824_);
if (v___x_3825_ == 0)
{
v___y_3801_ = v___x_3820_;
v___y_3802_ = v_a_3807_;
v_a_3803_ = v_a_3822_;
goto v___jp_3800_;
}
else
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
lean_inc(v_a_3822_);
v___x_3826_ = l_Lean_MessageData_ofExpr(v_a_3822_);
v___x_3827_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3823_, v___x_3826_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_dec_ref_known(v___x_3827_, 1);
v___y_3801_ = v___x_3820_;
v___y_3802_ = v_a_3807_;
v_a_3803_ = v_a_3822_;
goto v___jp_3800_;
}
else
{
lean_object* v_a_3828_; 
lean_dec(v_a_3822_);
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3827_, 1);
v___y_3795_ = v___x_3820_;
v___y_3796_ = v_a_3807_;
v_a_3797_ = v_a_3828_;
goto v___jp_3794_;
}
}
}
else
{
lean_object* v_a_3829_; 
v_a_3829_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3821_, 1);
v___y_3795_ = v___x_3820_;
v___y_3796_ = v_a_3807_;
v_a_3797_ = v_a_3829_;
goto v___jp_3794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3856_, lean_object* v_xs_3857_, lean_object* v_k_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3856_, v_xs_3857_, v_k_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3865_, lean_object* v_xs_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v___x_3872_; 
lean_inc(v_a_3870_);
lean_inc_ref(v_a_3869_);
lean_inc(v_a_3868_);
lean_inc_ref(v_a_3867_);
lean_inc_ref(v_f_3865_);
v___x_3872_ = lean_infer_type(v_f_3865_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3874_; uint8_t v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
lean_inc_ref(v_xs_3866_);
lean_inc_ref(v_f_3865_);
v___x_3874_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3874_, 0, v_f_3865_);
lean_closure_set(v___x_3874_, 1, v_a_3873_);
lean_closure_set(v___x_3874_, 2, v_xs_3866_);
v___x_3875_ = 0;
v___x_3876_ = lean_box(v___x_3875_);
v___x_3877_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3877_, 0, lean_box(0));
lean_closure_set(v___x_3877_, 1, v___x_3874_);
lean_closure_set(v___x_3877_, 2, v___x_3876_);
v___x_3878_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3865_, v_xs_3866_, v___x_3877_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
return v___x_3878_;
}
else
{
lean_dec_ref(v_xs_3866_);
lean_dec_ref(v_f_3865_);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3879_, lean_object* v_xs_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_Meta_mkAppM_x27(v_f_3879_, v_xs_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3887_, size_t v_i_3888_, size_t v_stop_3889_, lean_object* v_b_3890_){
_start:
{
lean_object* v___y_3892_; uint8_t v___x_3896_; 
v___x_3896_ = lean_usize_dec_eq(v_i_3888_, v_stop_3889_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_array_uget_borrowed(v_as_3887_, v_i_3888_);
if (lean_obj_tag(v___x_3897_) == 0)
{
v___y_3892_ = v_b_3890_;
goto v___jp_3891_;
}
else
{
lean_object* v_val_3898_; lean_object* v___x_3899_; 
v_val_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_val_3898_);
v___x_3899_ = lean_array_push(v_b_3890_, v_val_3898_);
v___y_3892_ = v___x_3899_;
goto v___jp_3891_;
}
}
else
{
return v_b_3890_;
}
v___jp_3891_:
{
size_t v___x_3893_; size_t v___x_3894_; 
v___x_3893_ = ((size_t)1ULL);
v___x_3894_ = lean_usize_add(v_i_3888_, v___x_3893_);
v_i_3888_ = v___x_3894_;
v_b_3890_ = v___y_3892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3900_, lean_object* v_i_3901_, lean_object* v_stop_3902_, lean_object* v_b_3903_){
_start:
{
size_t v_i_boxed_3904_; size_t v_stop_boxed_3905_; lean_object* v_res_3906_; 
v_i_boxed_3904_ = lean_unbox_usize(v_i_3901_);
lean_dec(v_i_3901_);
v_stop_boxed_3905_ = lean_unbox_usize(v_stop_3902_);
lean_dec(v_stop_3902_);
v_res_3906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3900_, v_i_boxed_3904_, v_stop_boxed_3905_, v_b_3903_);
lean_dec_ref(v_as_3900_);
return v_res_3906_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3914_ = l_Lean_MessageData_ofFormat(v___x_3913_);
return v___x_3914_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_box(1);
v___x_3916_ = l_Lean_MessageData_ofFormat(v___x_3915_);
return v___x_3916_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3921_ = l_Lean_MessageData_ofFormat(v___x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3922_, lean_object* v_xs_3923_, lean_object* v_x_3924_, lean_object* v_x_3925_, lean_object* v_x_3926_, lean_object* v_x_3927_, lean_object* v_x_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
if (lean_obj_tag(v_x_3928_) == 7)
{
lean_object* v_binderName_3934_; lean_object* v_binderType_3935_; lean_object* v_body_3936_; uint8_t v_binderInfo_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v_binderName_3934_ = lean_ctor_get(v_x_3928_, 0);
lean_inc(v_binderName_3934_);
v_binderType_3935_ = lean_ctor_get(v_x_3928_, 1);
lean_inc_ref(v_binderType_3935_);
v_body_3936_ = lean_ctor_get(v_x_3928_, 2);
lean_inc_ref(v_body_3936_);
v_binderInfo_3937_ = lean_ctor_get_uint8(v_x_3928_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3928_, 3);
v___x_3938_ = lean_array_get_size(v_xs_3923_);
v___x_3939_ = lean_nat_dec_lt(v_x_3924_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
lean_dec_ref(v_body_3936_);
lean_dec_ref(v_binderType_3935_);
lean_dec(v_binderName_3934_);
lean_dec(v_x_3926_);
lean_dec(v_x_3924_);
v___x_3940_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3941_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3940_, v_f_3922_, v_x_3925_, v_x_3927_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
lean_dec_ref(v_x_3927_);
lean_dec_ref(v_x_3925_);
return v___x_3941_;
}
else
{
lean_object* v___x_3942_; lean_object* v_d_3943_; lean_object* v___x_3944_; 
v___x_3942_ = lean_array_get_size(v_x_3925_);
v_d_3943_ = lean_expr_instantiate_rev_range(v_binderType_3935_, v_x_3926_, v___x_3942_, v_x_3925_);
lean_dec_ref(v_binderType_3935_);
v___x_3944_ = lean_array_fget_borrowed(v_xs_3923_, v_x_3924_);
if (lean_obj_tag(v___x_3944_) == 0)
{
if (v_binderInfo_3937_ == 3)
{
lean_object* v___x_3945_; uint8_t v___x_3946_; lean_object* v___x_3947_; 
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_d_3943_);
v___x_3946_ = 1;
v___x_3947_ = l_Lean_Meta_mkFreshExprMVar(v___x_3945_, v___x_3946_, v_binderName_3934_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc_n(v_a_3948_, 2);
lean_dec_ref_known(v___x_3947_, 1);
v___x_3949_ = lean_unsigned_to_nat(1u);
v___x_3950_ = lean_nat_add(v_x_3924_, v___x_3949_);
lean_dec(v_x_3924_);
v___x_3951_ = lean_array_push(v_x_3925_, v_a_3948_);
v___x_3952_ = l_Lean_Expr_mvarId_x21(v_a_3948_);
lean_dec(v_a_3948_);
v___x_3953_ = lean_array_push(v_x_3927_, v___x_3952_);
v_x_3924_ = v___x_3950_;
v_x_3925_ = v___x_3951_;
v_x_3927_ = v___x_3953_;
v_x_3928_ = v_body_3936_;
goto _start;
}
else
{
lean_dec_ref(v_body_3936_);
lean_dec_ref(v_x_3927_);
lean_dec(v_x_3926_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_f_3922_);
return v___x_3947_;
}
}
else
{
lean_object* v___x_3955_; uint8_t v___x_3956_; lean_object* v___x_3957_; 
v___x_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3955_, 0, v_d_3943_);
v___x_3956_ = 0;
v___x_3957_ = l_Lean_Meta_mkFreshExprMVar(v___x_3955_, v___x_3956_, v_binderName_3934_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = lean_unsigned_to_nat(1u);
v___x_3960_ = lean_nat_add(v_x_3924_, v___x_3959_);
lean_dec(v_x_3924_);
v___x_3961_ = lean_array_push(v_x_3925_, v_a_3958_);
v_x_3924_ = v___x_3960_;
v_x_3925_ = v___x_3961_;
v_x_3928_ = v_body_3936_;
goto _start;
}
else
{
lean_dec_ref(v_body_3936_);
lean_dec_ref(v_x_3927_);
lean_dec(v_x_3926_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_f_3922_);
return v___x_3957_;
}
}
}
else
{
lean_object* v_val_3963_; lean_object* v___x_3964_; 
lean_dec(v_binderName_3934_);
v_val_3963_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3932_);
lean_inc_ref(v_a_3931_);
lean_inc(v_a_3930_);
lean_inc_ref(v_a_3929_);
lean_inc(v_val_3963_);
v___x_3964_ = lean_infer_type(v_val_3963_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___x_3966_ = l_Lean_Meta_isExprDefEq(v_d_3943_, v_a_3965_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; uint8_t v___x_3968_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = lean_unbox(v_a_3967_);
lean_dec(v_a_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_dec_ref(v_body_3936_);
lean_dec_ref(v_x_3927_);
lean_dec(v_x_3926_);
lean_dec(v_x_3924_);
v___x_3969_ = l_Lean_mkAppN(v_f_3922_, v_x_3925_);
lean_dec_ref(v_x_3925_);
lean_inc(v_val_3963_);
v___x_3970_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3969_, v_val_3963_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
return v___x_3970_;
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3971_ = lean_unsigned_to_nat(1u);
v___x_3972_ = lean_nat_add(v_x_3924_, v___x_3971_);
lean_dec(v_x_3924_);
lean_inc(v_val_3963_);
v___x_3973_ = lean_array_push(v_x_3925_, v_val_3963_);
v_x_3924_ = v___x_3972_;
v_x_3925_ = v___x_3973_;
v_x_3928_ = v_body_3936_;
goto _start;
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec_ref(v_body_3936_);
lean_dec_ref(v_x_3927_);
lean_dec(v_x_3926_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_f_3922_);
v_a_3975_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3966_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3966_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
else
{
lean_dec_ref(v_d_3943_);
lean_dec_ref(v_body_3936_);
lean_dec_ref(v_x_3927_);
lean_dec(v_x_3926_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_f_3922_);
return v___x_3964_;
}
}
}
}
else
{
lean_object* v___x_3983_; lean_object* v_type_3984_; lean_object* v___x_3985_; 
v___x_3983_ = lean_array_get_size(v_x_3925_);
v_type_3984_ = lean_expr_instantiate_rev_range(v_x_3928_, v_x_3926_, v___x_3983_, v_x_3925_);
lean_dec(v_x_3926_);
lean_dec_ref(v_x_3928_);
v___x_3985_ = l_Lean_Meta_whnfD(v_type_3984_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; uint8_t v___x_3987_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v___x_3987_ = l_Lean_Expr_isForall(v_a_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; uint8_t v___x_3989_; 
lean_dec(v_a_3986_);
v___x_3988_ = lean_array_get_size(v_xs_3923_);
v___x_3989_ = lean_nat_dec_eq(v_x_3924_, v___x_3988_);
lean_dec(v_x_3924_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; lean_object* v___y_3992_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
lean_dec_ref(v_x_3927_);
lean_dec_ref(v_x_3925_);
v___x_3990_ = lean_unsigned_to_nat(0u);
v___x_4005_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4006_ = lean_nat_dec_lt(v___x_3990_, v___x_3988_);
if (v___x_4006_ == 0)
{
v___y_3992_ = v___x_4005_;
goto v___jp_3991_;
}
else
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_nat_dec_le(v___x_3988_, v___x_3988_);
if (v___x_4007_ == 0)
{
if (v___x_4006_ == 0)
{
v___y_3992_ = v___x_4005_;
goto v___jp_3991_;
}
else
{
size_t v___x_4008_; size_t v___x_4009_; lean_object* v___x_4010_; 
v___x_4008_ = ((size_t)0ULL);
v___x_4009_ = lean_usize_of_nat(v___x_3988_);
v___x_4010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3923_, v___x_4008_, v___x_4009_, v___x_4005_);
v___y_3992_ = v___x_4010_;
goto v___jp_3991_;
}
}
else
{
size_t v___x_4011_; size_t v___x_4012_; lean_object* v___x_4013_; 
v___x_4011_ = ((size_t)0ULL);
v___x_4012_ = lean_usize_of_nat(v___x_3988_);
v___x_4013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3923_, v___x_4011_, v___x_4012_, v___x_4005_);
v___y_3992_ = v___x_4013_;
goto v___jp_3991_;
}
}
v___jp_3991_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3993_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3994_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3995_ = l_Lean_indentExpr(v_f_3922_);
v___x_3996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3996_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_4000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3998_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_4002_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3992_, v___x_3990_, v___x_4001_);
lean_dec_ref(v___y_3992_);
v___x_4003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4000_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3993_, v___x_4003_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
return v___x_4004_;
}
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_4015_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_4014_, v_f_3922_, v_x_3925_, v_x_3927_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
lean_dec_ref(v_x_3927_);
lean_dec_ref(v_x_3925_);
return v___x_4015_;
}
}
else
{
v_x_3926_ = v___x_3983_;
v_x_3928_ = v_a_3986_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3927_);
lean_dec_ref(v_x_3925_);
lean_dec(v_x_3924_);
lean_dec_ref(v_f_3922_);
return v___x_3985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_4017_, lean_object* v_xs_4018_, lean_object* v_x_4019_, lean_object* v_x_4020_, lean_object* v_x_4021_, lean_object* v_x_4022_, lean_object* v_x_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_4017_, v_xs_4018_, v_x_4019_, v_x_4020_, v_x_4021_, v_x_4022_, v_x_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec_ref(v_xs_4018_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_4030_, lean_object* v_xs_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_4030_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v_fst_4039_; lean_object* v_snd_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v_fst_4039_ = lean_ctor_get(v_a_4038_, 0);
lean_inc(v_fst_4039_);
v_snd_4040_ = lean_ctor_get(v_a_4038_, 1);
lean_inc(v_snd_4040_);
lean_dec(v_a_4038_);
v___x_4041_ = lean_unsigned_to_nat(0u);
v___x_4042_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4043_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_4039_, v_xs_4031_, v___x_4041_, v___x_4042_, v___x_4041_, v___x_4042_, v_snd_4040_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
return v___x_4043_;
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4037_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4037_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4052_, lean_object* v_xs_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4052_, v_xs_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec_ref(v_xs_4053_);
return v_res_4059_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4064_ = l_Lean_MessageData_ofFormat(v___x_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
if (lean_obj_tag(v_a_4065_) == 0)
{
lean_object* v___x_4067_; 
v___x_4067_ = l_List_reverse___redArg(v_a_4066_);
return v___x_4067_;
}
else
{
lean_object* v_head_4068_; lean_object* v_tail_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4082_; 
v_head_4068_ = lean_ctor_get(v_a_4065_, 0);
v_tail_4069_ = lean_ctor_get(v_a_4065_, 1);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_a_4065_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4071_ = v_a_4065_;
v_isShared_4072_ = v_isSharedCheck_4082_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_tail_4069_);
lean_inc(v_head_4068_);
lean_dec(v_a_4065_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4082_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___y_4074_; 
if (lean_obj_tag(v_head_4068_) == 0)
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4074_ = v___x_4079_;
goto v___jp_4073_;
}
else
{
lean_object* v_val_4080_; lean_object* v___x_4081_; 
v_val_4080_ = lean_ctor_get(v_head_4068_, 0);
lean_inc(v_val_4080_);
lean_dec_ref_known(v_head_4068_, 1);
v___x_4081_ = l_Lean_MessageData_ofExpr(v_val_4080_);
v___y_4074_ = v___x_4081_;
goto v___jp_4073_;
}
v___jp_4073_:
{
lean_object* v___x_4076_; 
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 1, v_a_4066_);
lean_ctor_set(v___x_4071_, 0, v___y_4074_);
v___x_4076_ = v___x_4071_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___y_4074_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v_a_4066_);
v___x_4076_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
v_a_4065_ = v_tail_4069_;
v_a_4066_ = v___x_4076_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4083_, lean_object* v_xs_4084_, lean_object* v_x_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4091_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4092_ = l_Lean_MessageData_ofName(v_f_4083_);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = lean_array_to_list(v_xs_4084_);
v___x_4097_ = lean_box(0);
v___x_4098_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4096_, v___x_4097_);
v___x_4099_ = l_Lean_MessageData_ofList(v___x_4098_);
v___x_4100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4095_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4102_, lean_object* v_xs_4103_, lean_object* v_x_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4102_, v_xs_4103_, v_x_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec_ref(v_x_4104_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4111_, lean_object* v_xs_4112_, lean_object* v_k_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v_toCold_4119_; lean_object* v_options_4120_; uint8_t v_hasTrace_4121_; 
v_toCold_4119_ = lean_ctor_get(v_a_4116_, 0);
v_options_4120_ = lean_ctor_get(v_toCold_4119_, 2);
v_hasTrace_4121_ = lean_ctor_get_uint8(v_options_4120_, sizeof(void*)*1);
if (v_hasTrace_4121_ == 0)
{
lean_object* v___x_4122_; 
lean_dec_ref(v_xs_4112_);
lean_dec(v_f_4111_);
lean_inc(v_a_4117_);
lean_inc_ref(v_a_4116_);
lean_inc(v_a_4115_);
lean_inc_ref(v_a_4114_);
v___x_4122_ = lean_apply_5(v_k_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, lean_box(0));
return v___x_4122_;
}
else
{
lean_object* v_inheritedTraceOptions_4123_; lean_object* v___f_4124_; lean_object* v___y_4126_; lean_object* v___y_4127_; uint8_t v___y_4128_; lean_object* v___y_4152_; lean_object* v_a_4153_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v_a_4163_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v_a_4178_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; uint8_t v___y_4184_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_a_4194_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v_a_4200_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v_a_4205_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v_a_4217_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; uint8_t v___y_4223_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v_a_4233_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v_a_4239_; 
v_inheritedTraceOptions_4123_ = lean_ctor_get(v_toCold_4119_, 11);
v___f_4124_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4124_, 0, v_f_4111_);
lean_closure_set(v___f_4124_, 1, v_xs_4112_);
v___x_4156_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4157_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4158_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4123_, v_options_4120_, v___x_4158_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4266_; uint8_t v___x_4267_; 
v___x_4266_ = l_Lean_trace_profiler;
v___x_4267_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4120_, v___x_4266_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4268_; 
lean_dec_ref(v___f_4124_);
lean_inc(v_a_4117_);
lean_inc_ref(v_a_4116_);
lean_inc(v_a_4115_);
lean_inc_ref(v_a_4114_);
v___x_4268_ = lean_apply_5(v_k_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, lean_box(0));
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
v___x_4270_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4271_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4123_, v_options_4120_, v___x_4271_);
if (v___x_4272_ == 0)
{
lean_dec(v_a_4269_);
return v___x_4268_;
}
else
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_dec_ref_known(v___x_4268_, 1);
lean_inc(v_a_4269_);
v___x_4273_ = l_Lean_MessageData_ofExpr(v_a_4269_);
v___x_4274_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4270_, v___x_4273_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4281_ == 0)
{
lean_object* v_unused_4282_; 
v_unused_4282_ = lean_ctor_get(v___x_4274_, 0);
lean_dec(v_unused_4282_);
v___x_4276_ = v___x_4274_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_dec(v___x_4274_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 0, v_a_4269_);
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4269_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v_a_4269_);
v_a_4283_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4274_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4274_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
lean_inc(v_a_4283_);
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
v___y_4152_ = v___x_4288_;
v_a_4153_ = v_a_4283_;
goto v___jp_4151_;
}
}
}
}
}
else
{
lean_object* v_a_4291_; 
v_a_4291_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4291_);
v___y_4152_ = v___x_4268_;
v_a_4153_ = v_a_4291_;
goto v___jp_4151_;
}
}
else
{
goto v___jp_4241_;
}
}
else
{
goto v___jp_4241_;
}
v___jp_4125_:
{
if (v___y_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; 
lean_dec_ref(v___y_4127_);
v___x_4129_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4130_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4123_, v_options_4120_, v___x_4130_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___y_4126_);
return v___x_4132_;
}
else
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_inc_ref(v___y_4126_);
v___x_4133_ = l_Lean_Exception_toMessageData(v___y_4126_);
v___x_4134_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4129_, v___x_4133_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4141_ == 0)
{
lean_object* v_unused_4142_; 
v_unused_4142_ = lean_ctor_get(v___x_4134_, 0);
lean_dec(v_unused_4142_);
v___x_4136_ = v___x_4134_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_dec(v___x_4134_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
lean_ctor_set_tag(v___x_4136_, 1);
lean_ctor_set(v___x_4136_, 0, v___y_4126_);
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___y_4126_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v___y_4126_);
v_a_4143_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4134_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4134_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4126_);
return v___y_4127_;
}
}
v___jp_4151_:
{
uint8_t v___x_4154_; 
v___x_4154_ = l_Lean_Exception_isInterrupt(v_a_4153_);
if (v___x_4154_ == 0)
{
uint8_t v___x_4155_; 
lean_inc_ref(v_a_4153_);
v___x_4155_ = l_Lean_Exception_isRuntime(v_a_4153_);
v___y_4126_ = v_a_4153_;
v___y_4127_ = v___y_4152_;
v___y_4128_ = v___x_4155_;
goto v___jp_4125_;
}
else
{
v___y_4126_ = v_a_4153_;
v___y_4127_ = v___y_4152_;
v___y_4128_ = v___x_4154_;
goto v___jp_4125_;
}
}
v___jp_4160_:
{
lean_object* v___x_4164_; double v___x_4165_; double v___x_4166_; double v___x_4167_; double v___x_4168_; double v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4164_ = lean_io_mono_nanos_now();
v___x_4165_ = lean_float_of_nat(v___y_4161_);
v___x_4166_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4167_ = lean_float_div(v___x_4165_, v___x_4166_);
v___x_4168_ = lean_float_of_nat(v___x_4164_);
v___x_4169_ = lean_float_div(v___x_4168_, v___x_4166_);
v___x_4170_ = lean_box_float(v___x_4167_);
v___x_4171_ = lean_box_float(v___x_4169_);
v___x_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4170_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4173_, 0, v_a_4163_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4156_, v_hasTrace_4121_, v___x_4157_, v_options_4120_, v___x_4159_, v___y_4162_, v___f_4124_, v___x_4173_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4174_;
}
v___jp_4175_:
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_a_4178_);
v___y_4161_ = v___y_4176_;
v___y_4162_ = v___y_4177_;
v_a_4163_ = v___x_4179_;
goto v___jp_4160_;
}
v___jp_4180_:
{
if (v___y_4184_ == 0)
{
lean_object* v___x_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; 
v___x_4185_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4186_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4187_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4123_, v_options_4120_, v___x_4186_);
if (v___x_4187_ == 0)
{
v___y_4176_ = v___y_4181_;
v___y_4177_ = v___y_4182_;
v_a_4178_ = v___y_4183_;
goto v___jp_4175_;
}
else
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
lean_inc_ref(v___y_4183_);
v___x_4188_ = l_Lean_Exception_toMessageData(v___y_4183_);
v___x_4189_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4185_, v___x_4188_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_dec_ref_known(v___x_4189_, 1);
v___y_4176_ = v___y_4181_;
v___y_4177_ = v___y_4182_;
v_a_4178_ = v___y_4183_;
goto v___jp_4175_;
}
else
{
lean_object* v_a_4190_; 
lean_dec_ref(v___y_4183_);
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___y_4176_ = v___y_4181_;
v___y_4177_ = v___y_4182_;
v_a_4178_ = v_a_4190_;
goto v___jp_4175_;
}
}
}
else
{
v___y_4176_ = v___y_4181_;
v___y_4177_ = v___y_4182_;
v_a_4178_ = v___y_4183_;
goto v___jp_4175_;
}
}
v___jp_4191_:
{
uint8_t v___x_4195_; 
v___x_4195_ = l_Lean_Exception_isInterrupt(v_a_4194_);
if (v___x_4195_ == 0)
{
uint8_t v___x_4196_; 
lean_inc_ref(v_a_4194_);
v___x_4196_ = l_Lean_Exception_isRuntime(v_a_4194_);
v___y_4181_ = v___y_4192_;
v___y_4182_ = v___y_4193_;
v___y_4183_ = v_a_4194_;
v___y_4184_ = v___x_4196_;
goto v___jp_4180_;
}
else
{
v___y_4181_ = v___y_4192_;
v___y_4182_ = v___y_4193_;
v___y_4183_ = v_a_4194_;
v___y_4184_ = v___x_4195_;
goto v___jp_4180_;
}
}
v___jp_4197_:
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4201_, 0, v_a_4200_);
v___y_4161_ = v___y_4198_;
v___y_4162_ = v___y_4199_;
v_a_4163_ = v___x_4201_;
goto v___jp_4160_;
}
v___jp_4202_:
{
lean_object* v___x_4206_; double v___x_4207_; double v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4206_ = lean_io_get_num_heartbeats();
v___x_4207_ = lean_float_of_nat(v___y_4204_);
v___x_4208_ = lean_float_of_nat(v___x_4206_);
v___x_4209_ = lean_box_float(v___x_4207_);
v___x_4210_ = lean_box_float(v___x_4208_);
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4209_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4212_, 0, v_a_4205_);
lean_ctor_set(v___x_4212_, 1, v___x_4211_);
v___x_4213_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4156_, v_hasTrace_4121_, v___x_4157_, v_options_4120_, v___x_4159_, v___y_4203_, v___f_4124_, v___x_4212_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4213_;
}
v___jp_4214_:
{
lean_object* v___x_4218_; 
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v_a_4217_);
v___y_4203_ = v___y_4215_;
v___y_4204_ = v___y_4216_;
v_a_4205_ = v___x_4218_;
goto v___jp_4202_;
}
v___jp_4219_:
{
if (v___y_4223_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; 
v___x_4224_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4225_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4226_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4123_, v_options_4120_, v___x_4225_);
if (v___x_4226_ == 0)
{
v___y_4215_ = v___y_4220_;
v___y_4216_ = v___y_4222_;
v_a_4217_ = v___y_4221_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
lean_inc_ref(v___y_4221_);
v___x_4227_ = l_Lean_Exception_toMessageData(v___y_4221_);
v___x_4228_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4224_, v___x_4227_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_dec_ref_known(v___x_4228_, 1);
v___y_4215_ = v___y_4220_;
v___y_4216_ = v___y_4222_;
v_a_4217_ = v___y_4221_;
goto v___jp_4214_;
}
else
{
lean_object* v_a_4229_; 
lean_dec_ref(v___y_4221_);
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4228_, 1);
v___y_4215_ = v___y_4220_;
v___y_4216_ = v___y_4222_;
v_a_4217_ = v_a_4229_;
goto v___jp_4214_;
}
}
}
else
{
v___y_4215_ = v___y_4220_;
v___y_4216_ = v___y_4222_;
v_a_4217_ = v___y_4221_;
goto v___jp_4214_;
}
}
v___jp_4230_:
{
uint8_t v___x_4234_; 
v___x_4234_ = l_Lean_Exception_isInterrupt(v_a_4233_);
if (v___x_4234_ == 0)
{
uint8_t v___x_4235_; 
lean_inc_ref(v_a_4233_);
v___x_4235_ = l_Lean_Exception_isRuntime(v_a_4233_);
v___y_4220_ = v___y_4231_;
v___y_4221_ = v_a_4233_;
v___y_4222_ = v___y_4232_;
v___y_4223_ = v___x_4235_;
goto v___jp_4219_;
}
else
{
v___y_4220_ = v___y_4231_;
v___y_4221_ = v_a_4233_;
v___y_4222_ = v___y_4232_;
v___y_4223_ = v___x_4234_;
goto v___jp_4219_;
}
}
v___jp_4236_:
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4240_, 0, v_a_4239_);
v___y_4203_ = v___y_4237_;
v___y_4204_ = v___y_4238_;
v_a_4205_ = v___x_4240_;
goto v___jp_4202_;
}
v___jp_4241_:
{
lean_object* v___x_4242_; lean_object* v_a_4243_; lean_object* v___x_4244_; uint8_t v___x_4245_; 
v___x_4242_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4117_);
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref(v___x_4242_);
v___x_4244_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4245_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4120_, v___x_4244_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = lean_io_mono_nanos_now();
lean_inc(v_a_4117_);
lean_inc_ref(v_a_4116_);
lean_inc(v_a_4115_);
lean_inc_ref(v_a_4114_);
v___x_4247_ = lean_apply_5(v_k_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, lean_box(0));
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4247_, 1);
v___x_4249_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4250_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4251_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4123_, v_options_4120_, v___x_4250_);
if (v___x_4251_ == 0)
{
v___y_4198_ = v___x_4246_;
v___y_4199_ = v_a_4243_;
v_a_4200_ = v_a_4248_;
goto v___jp_4197_;
}
else
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_inc(v_a_4248_);
v___x_4252_ = l_Lean_MessageData_ofExpr(v_a_4248_);
v___x_4253_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4249_, v___x_4252_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_dec_ref_known(v___x_4253_, 1);
v___y_4198_ = v___x_4246_;
v___y_4199_ = v_a_4243_;
v_a_4200_ = v_a_4248_;
goto v___jp_4197_;
}
else
{
lean_object* v_a_4254_; 
lean_dec(v_a_4248_);
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___y_4192_ = v___x_4246_;
v___y_4193_ = v_a_4243_;
v_a_4194_ = v_a_4254_;
goto v___jp_4191_;
}
}
}
else
{
lean_object* v_a_4255_; 
v_a_4255_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4247_, 1);
v___y_4192_ = v___x_4246_;
v___y_4193_ = v_a_4243_;
v_a_4194_ = v_a_4255_;
goto v___jp_4191_;
}
}
else
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4117_);
lean_inc_ref(v_a_4116_);
lean_inc(v_a_4115_);
lean_inc_ref(v_a_4114_);
v___x_4257_ = lean_apply_5(v_k_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, lean_box(0));
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref_known(v___x_4257_, 1);
v___x_4259_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4260_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4261_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4123_, v_options_4120_, v___x_4260_);
if (v___x_4261_ == 0)
{
v___y_4237_ = v_a_4243_;
v___y_4238_ = v___x_4256_;
v_a_4239_ = v_a_4258_;
goto v___jp_4236_;
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
lean_inc(v_a_4258_);
v___x_4262_ = l_Lean_MessageData_ofExpr(v_a_4258_);
v___x_4263_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4259_, v___x_4262_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_dec_ref_known(v___x_4263_, 1);
v___y_4237_ = v_a_4243_;
v___y_4238_ = v___x_4256_;
v_a_4239_ = v_a_4258_;
goto v___jp_4236_;
}
else
{
lean_object* v_a_4264_; 
lean_dec(v_a_4258_);
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
lean_dec_ref_known(v___x_4263_, 1);
v___y_4231_ = v_a_4243_;
v___y_4232_ = v___x_4256_;
v_a_4233_ = v_a_4264_;
goto v___jp_4230_;
}
}
}
else
{
lean_object* v_a_4265_; 
v_a_4265_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4257_, 1);
v___y_4231_ = v_a_4243_;
v___y_4232_ = v___x_4256_;
v_a_4233_ = v_a_4265_;
goto v___jp_4230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4292_, lean_object* v_xs_4293_, lean_object* v_k_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4292_, v_xs_4293_, v_k_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4301_, lean_object* v_xs_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v___f_4308_; uint8_t v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
lean_inc_ref(v_xs_4302_);
lean_inc(v_constName_4301_);
v___f_4308_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4308_, 0, v_constName_4301_);
lean_closure_set(v___f_4308_, 1, v_xs_4302_);
v___x_4309_ = 0;
v___x_4310_ = lean_box(v___x_4309_);
v___x_4311_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4311_, 0, lean_box(0));
lean_closure_set(v___x_4311_, 1, v___f_4308_);
lean_closure_set(v___x_4311_, 2, v___x_4310_);
v___x_4312_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4301_, v_xs_4302_, v___x_4311_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4313_, lean_object* v_xs_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_Meta_mkAppOptM(v_constName_4313_, v_xs_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4321_, lean_object* v_xs_4322_, lean_object* v_x_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4329_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4330_ = l_Lean_MessageData_ofExpr(v_f_4321_);
v___x_4331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
v___x_4332_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4331_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
v___x_4334_ = lean_array_to_list(v_xs_4322_);
v___x_4335_ = lean_box(0);
v___x_4336_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4334_, v___x_4335_);
v___x_4337_ = l_Lean_MessageData_ofList(v___x_4336_);
v___x_4338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4333_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4340_, lean_object* v_xs_4341_, lean_object* v_x_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4340_, v_xs_4341_, v_x_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec_ref(v_x_4342_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4349_, lean_object* v_xs_4350_, lean_object* v_k_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v_toCold_4357_; lean_object* v_options_4358_; uint8_t v_hasTrace_4359_; 
v_toCold_4357_ = lean_ctor_get(v_a_4354_, 0);
v_options_4358_ = lean_ctor_get(v_toCold_4357_, 2);
v_hasTrace_4359_ = lean_ctor_get_uint8(v_options_4358_, sizeof(void*)*1);
if (v_hasTrace_4359_ == 0)
{
lean_object* v___x_4360_; 
lean_dec_ref(v_xs_4350_);
lean_dec_ref(v_f_4349_);
lean_inc(v_a_4355_);
lean_inc_ref(v_a_4354_);
lean_inc(v_a_4353_);
lean_inc_ref(v_a_4352_);
v___x_4360_ = lean_apply_5(v_k_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, lean_box(0));
return v___x_4360_;
}
else
{
lean_object* v_inheritedTraceOptions_4361_; lean_object* v___f_4362_; lean_object* v___y_4364_; lean_object* v___y_4365_; uint8_t v___y_4366_; lean_object* v___y_4390_; lean_object* v_a_4391_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; uint8_t v___x_4397_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v_a_4401_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v_a_4416_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; uint8_t v___y_4422_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v_a_4432_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v_a_4438_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v_a_4443_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v_a_4455_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; uint8_t v___y_4461_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v_a_4471_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v_a_4477_; 
v_inheritedTraceOptions_4361_ = lean_ctor_get(v_toCold_4357_, 11);
v___f_4362_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4362_, 0, v_f_4349_);
lean_closure_set(v___f_4362_, 1, v_xs_4350_);
v___x_4394_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4395_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4396_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4397_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4361_, v_options_4358_, v___x_4396_);
if (v___x_4397_ == 0)
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = l_Lean_trace_profiler;
v___x_4505_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4358_, v___x_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; 
lean_dec_ref(v___f_4362_);
lean_inc(v_a_4355_);
lean_inc_ref(v_a_4354_);
lean_inc(v_a_4353_);
lean_inc_ref(v_a_4352_);
v___x_4506_ = lean_apply_5(v_k_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, lean_box(0));
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; uint8_t v___x_4510_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_a_4507_);
v___x_4508_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4509_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4510_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4361_, v_options_4358_, v___x_4509_);
if (v___x_4510_ == 0)
{
lean_dec(v_a_4507_);
return v___x_4506_;
}
else
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_dec_ref_known(v___x_4506_, 1);
lean_inc(v_a_4507_);
v___x_4511_ = l_Lean_MessageData_ofExpr(v_a_4507_);
v___x_4512_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4508_, v___x_4511_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4512_, 0);
lean_dec(v_unused_4520_);
v___x_4514_ = v___x_4512_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_dec(v___x_4512_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 0, v_a_4507_);
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4507_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_a_4507_);
v_a_4521_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4512_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4512_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
lean_inc(v_a_4521_);
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
v___y_4390_ = v___x_4526_;
v_a_4391_ = v_a_4521_;
goto v___jp_4389_;
}
}
}
}
}
else
{
lean_object* v_a_4529_; 
v_a_4529_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_a_4529_);
v___y_4390_ = v___x_4506_;
v_a_4391_ = v_a_4529_;
goto v___jp_4389_;
}
}
else
{
goto v___jp_4479_;
}
}
else
{
goto v___jp_4479_;
}
v___jp_4363_:
{
if (v___y_4366_ == 0)
{
lean_object* v___x_4367_; lean_object* v___x_4368_; uint8_t v___x_4369_; 
lean_dec_ref(v___y_4365_);
v___x_4367_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4368_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4369_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4361_, v_options_4358_, v___x_4368_);
if (v___x_4369_ == 0)
{
lean_object* v___x_4370_; 
v___x_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4370_, 0, v___y_4364_);
return v___x_4370_;
}
else
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
lean_inc_ref(v___y_4364_);
v___x_4371_ = l_Lean_Exception_toMessageData(v___y_4364_);
v___x_4372_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4367_, v___x_4371_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4379_ == 0)
{
lean_object* v_unused_4380_; 
v_unused_4380_ = lean_ctor_get(v___x_4372_, 0);
lean_dec(v_unused_4380_);
v___x_4374_ = v___x_4372_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_dec(v___x_4372_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
lean_ctor_set_tag(v___x_4374_, 1);
lean_ctor_set(v___x_4374_, 0, v___y_4364_);
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___y_4364_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref(v___y_4364_);
v_a_4381_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4372_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4372_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4364_);
return v___y_4365_;
}
}
v___jp_4389_:
{
uint8_t v___x_4392_; 
v___x_4392_ = l_Lean_Exception_isInterrupt(v_a_4391_);
if (v___x_4392_ == 0)
{
uint8_t v___x_4393_; 
lean_inc_ref(v_a_4391_);
v___x_4393_ = l_Lean_Exception_isRuntime(v_a_4391_);
v___y_4364_ = v_a_4391_;
v___y_4365_ = v___y_4390_;
v___y_4366_ = v___x_4393_;
goto v___jp_4363_;
}
else
{
v___y_4364_ = v_a_4391_;
v___y_4365_ = v___y_4390_;
v___y_4366_ = v___x_4392_;
goto v___jp_4363_;
}
}
v___jp_4398_:
{
lean_object* v___x_4402_; double v___x_4403_; double v___x_4404_; double v___x_4405_; double v___x_4406_; double v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4402_ = lean_io_mono_nanos_now();
v___x_4403_ = lean_float_of_nat(v___y_4400_);
v___x_4404_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4405_ = lean_float_div(v___x_4403_, v___x_4404_);
v___x_4406_ = lean_float_of_nat(v___x_4402_);
v___x_4407_ = lean_float_div(v___x_4406_, v___x_4404_);
v___x_4408_ = lean_box_float(v___x_4405_);
v___x_4409_ = lean_box_float(v___x_4407_);
v___x_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4408_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4411_, 0, v_a_4401_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4394_, v_hasTrace_4359_, v___x_4395_, v_options_4358_, v___x_4397_, v___y_4399_, v___f_4362_, v___x_4411_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
return v___x_4412_;
}
v___jp_4413_:
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4417_, 0, v_a_4416_);
v___y_4399_ = v___y_4414_;
v___y_4400_ = v___y_4415_;
v_a_4401_ = v___x_4417_;
goto v___jp_4398_;
}
v___jp_4418_:
{
if (v___y_4422_ == 0)
{
lean_object* v___x_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4423_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4424_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4425_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4361_, v_options_4358_, v___x_4424_);
if (v___x_4425_ == 0)
{
v___y_4414_ = v___y_4420_;
v___y_4415_ = v___y_4421_;
v_a_4416_ = v___y_4419_;
goto v___jp_4413_;
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
lean_inc_ref(v___y_4419_);
v___x_4426_ = l_Lean_Exception_toMessageData(v___y_4419_);
v___x_4427_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4423_, v___x_4426_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_dec_ref_known(v___x_4427_, 1);
v___y_4414_ = v___y_4420_;
v___y_4415_ = v___y_4421_;
v_a_4416_ = v___y_4419_;
goto v___jp_4413_;
}
else
{
lean_object* v_a_4428_; 
lean_dec_ref(v___y_4419_);
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref_known(v___x_4427_, 1);
v___y_4414_ = v___y_4420_;
v___y_4415_ = v___y_4421_;
v_a_4416_ = v_a_4428_;
goto v___jp_4413_;
}
}
}
else
{
v___y_4414_ = v___y_4420_;
v___y_4415_ = v___y_4421_;
v_a_4416_ = v___y_4419_;
goto v___jp_4413_;
}
}
v___jp_4429_:
{
uint8_t v___x_4433_; 
v___x_4433_ = l_Lean_Exception_isInterrupt(v_a_4432_);
if (v___x_4433_ == 0)
{
uint8_t v___x_4434_; 
lean_inc_ref(v_a_4432_);
v___x_4434_ = l_Lean_Exception_isRuntime(v_a_4432_);
v___y_4419_ = v_a_4432_;
v___y_4420_ = v___y_4430_;
v___y_4421_ = v___y_4431_;
v___y_4422_ = v___x_4434_;
goto v___jp_4418_;
}
else
{
v___y_4419_ = v_a_4432_;
v___y_4420_ = v___y_4430_;
v___y_4421_ = v___y_4431_;
v___y_4422_ = v___x_4433_;
goto v___jp_4418_;
}
}
v___jp_4435_:
{
lean_object* v___x_4439_; 
v___x_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4439_, 0, v_a_4438_);
v___y_4399_ = v___y_4436_;
v___y_4400_ = v___y_4437_;
v_a_4401_ = v___x_4439_;
goto v___jp_4398_;
}
v___jp_4440_:
{
lean_object* v___x_4444_; double v___x_4445_; double v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4444_ = lean_io_get_num_heartbeats();
v___x_4445_ = lean_float_of_nat(v___y_4441_);
v___x_4446_ = lean_float_of_nat(v___x_4444_);
v___x_4447_ = lean_box_float(v___x_4445_);
v___x_4448_ = lean_box_float(v___x_4446_);
v___x_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4447_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4450_, 0, v_a_4443_);
lean_ctor_set(v___x_4450_, 1, v___x_4449_);
v___x_4451_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4394_, v_hasTrace_4359_, v___x_4395_, v_options_4358_, v___x_4397_, v___y_4442_, v___f_4362_, v___x_4450_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
return v___x_4451_;
}
v___jp_4452_:
{
lean_object* v___x_4456_; 
v___x_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4456_, 0, v_a_4455_);
v___y_4441_ = v___y_4453_;
v___y_4442_ = v___y_4454_;
v_a_4443_ = v___x_4456_;
goto v___jp_4440_;
}
v___jp_4457_:
{
if (v___y_4461_ == 0)
{
lean_object* v___x_4462_; lean_object* v___x_4463_; uint8_t v___x_4464_; 
v___x_4462_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4463_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4464_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4361_, v_options_4358_, v___x_4463_);
if (v___x_4464_ == 0)
{
v___y_4453_ = v___y_4458_;
v___y_4454_ = v___y_4460_;
v_a_4455_ = v___y_4459_;
goto v___jp_4452_;
}
else
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
lean_inc_ref(v___y_4459_);
v___x_4465_ = l_Lean_Exception_toMessageData(v___y_4459_);
v___x_4466_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4462_, v___x_4465_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_dec_ref_known(v___x_4466_, 1);
v___y_4453_ = v___y_4458_;
v___y_4454_ = v___y_4460_;
v_a_4455_ = v___y_4459_;
goto v___jp_4452_;
}
else
{
lean_object* v_a_4467_; 
lean_dec_ref(v___y_4459_);
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4466_, 1);
v___y_4453_ = v___y_4458_;
v___y_4454_ = v___y_4460_;
v_a_4455_ = v_a_4467_;
goto v___jp_4452_;
}
}
}
else
{
v___y_4453_ = v___y_4458_;
v___y_4454_ = v___y_4460_;
v_a_4455_ = v___y_4459_;
goto v___jp_4452_;
}
}
v___jp_4468_:
{
uint8_t v___x_4472_; 
v___x_4472_ = l_Lean_Exception_isInterrupt(v_a_4471_);
if (v___x_4472_ == 0)
{
uint8_t v___x_4473_; 
lean_inc_ref(v_a_4471_);
v___x_4473_ = l_Lean_Exception_isRuntime(v_a_4471_);
v___y_4458_ = v___y_4469_;
v___y_4459_ = v_a_4471_;
v___y_4460_ = v___y_4470_;
v___y_4461_ = v___x_4473_;
goto v___jp_4457_;
}
else
{
v___y_4458_ = v___y_4469_;
v___y_4459_ = v_a_4471_;
v___y_4460_ = v___y_4470_;
v___y_4461_ = v___x_4472_;
goto v___jp_4457_;
}
}
v___jp_4474_:
{
lean_object* v___x_4478_; 
v___x_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4478_, 0, v_a_4477_);
v___y_4441_ = v___y_4475_;
v___y_4442_ = v___y_4476_;
v_a_4443_ = v___x_4478_;
goto v___jp_4440_;
}
v___jp_4479_:
{
lean_object* v___x_4480_; lean_object* v_a_4481_; lean_object* v___x_4482_; uint8_t v___x_4483_; 
v___x_4480_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4355_);
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref(v___x_4480_);
v___x_4482_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4483_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4358_, v___x_4482_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4484_ = lean_io_mono_nanos_now();
lean_inc(v_a_4355_);
lean_inc_ref(v_a_4354_);
lean_inc(v_a_4353_);
lean_inc_ref(v_a_4352_);
v___x_4485_ = lean_apply_5(v_k_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, lean_box(0));
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; uint8_t v___x_4489_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v___x_4487_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4488_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4361_, v_options_4358_, v___x_4488_);
if (v___x_4489_ == 0)
{
v___y_4436_ = v_a_4481_;
v___y_4437_ = v___x_4484_;
v_a_4438_ = v_a_4486_;
goto v___jp_4435_;
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
lean_inc(v_a_4486_);
v___x_4490_ = l_Lean_MessageData_ofExpr(v_a_4486_);
v___x_4491_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4487_, v___x_4490_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_dec_ref_known(v___x_4491_, 1);
v___y_4436_ = v_a_4481_;
v___y_4437_ = v___x_4484_;
v_a_4438_ = v_a_4486_;
goto v___jp_4435_;
}
else
{
lean_object* v_a_4492_; 
lean_dec(v_a_4486_);
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v___y_4430_ = v_a_4481_;
v___y_4431_ = v___x_4484_;
v_a_4432_ = v_a_4492_;
goto v___jp_4429_;
}
}
}
else
{
lean_object* v_a_4493_; 
v_a_4493_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4493_);
lean_dec_ref_known(v___x_4485_, 1);
v___y_4430_ = v_a_4481_;
v___y_4431_ = v___x_4484_;
v_a_4432_ = v_a_4493_;
goto v___jp_4429_;
}
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4494_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4355_);
lean_inc_ref(v_a_4354_);
lean_inc(v_a_4353_);
lean_inc_ref(v_a_4352_);
v___x_4495_ = lean_apply_5(v_k_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, lean_box(0));
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; uint8_t v___x_4499_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
v___x_4497_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4498_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4499_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4361_, v_options_4358_, v___x_4498_);
if (v___x_4499_ == 0)
{
v___y_4475_ = v___x_4494_;
v___y_4476_ = v_a_4481_;
v_a_4477_ = v_a_4496_;
goto v___jp_4474_;
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_inc(v_a_4496_);
v___x_4500_ = l_Lean_MessageData_ofExpr(v_a_4496_);
v___x_4501_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4497_, v___x_4500_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_dec_ref_known(v___x_4501_, 1);
v___y_4475_ = v___x_4494_;
v___y_4476_ = v_a_4481_;
v_a_4477_ = v_a_4496_;
goto v___jp_4474_;
}
else
{
lean_object* v_a_4502_; 
lean_dec(v_a_4496_);
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v___y_4469_ = v___x_4494_;
v___y_4470_ = v_a_4481_;
v_a_4471_ = v_a_4502_;
goto v___jp_4468_;
}
}
}
else
{
lean_object* v_a_4503_; 
v_a_4503_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4503_);
lean_dec_ref_known(v___x_4495_, 1);
v___y_4469_ = v___x_4494_;
v___y_4470_ = v_a_4481_;
v_a_4471_ = v_a_4503_;
goto v___jp_4468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4530_, lean_object* v_xs_4531_, lean_object* v_k_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4530_, v_xs_4531_, v_k_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4539_, lean_object* v_xs_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v___x_4546_; 
lean_inc(v_a_4544_);
lean_inc_ref(v_a_4543_);
lean_inc(v_a_4542_);
lean_inc_ref(v_a_4541_);
lean_inc_ref(v_f_4539_);
v___x_4546_ = lean_infer_type(v_f_4539_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_a_4547_);
lean_dec_ref_known(v___x_4546_, 1);
v___x_4548_ = lean_unsigned_to_nat(0u);
v___x_4549_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4540_);
lean_inc_ref(v_f_4539_);
v___x_4550_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4550_, 0, v_f_4539_);
lean_closure_set(v___x_4550_, 1, v_xs_4540_);
lean_closure_set(v___x_4550_, 2, v___x_4548_);
lean_closure_set(v___x_4550_, 3, v___x_4549_);
lean_closure_set(v___x_4550_, 4, v___x_4548_);
lean_closure_set(v___x_4550_, 5, v___x_4549_);
lean_closure_set(v___x_4550_, 6, v_a_4547_);
v___x_4551_ = 0;
v___x_4552_ = lean_box(v___x_4551_);
v___x_4553_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4553_, 0, lean_box(0));
lean_closure_set(v___x_4553_, 1, v___x_4550_);
lean_closure_set(v___x_4553_, 2, v___x_4552_);
v___x_4554_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4539_, v_xs_4540_, v___x_4553_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
return v___x_4554_;
}
else
{
lean_dec_ref(v_xs_4540_);
lean_dec_ref(v_f_4539_);
return v___x_4546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4555_, lean_object* v_xs_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_Lean_Meta_mkAppOptM_x27(v_f_4555_, v_xs_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_);
lean_dec(v_a_4560_);
lean_dec_ref(v_a_4559_);
lean_dec(v_a_4558_);
lean_dec_ref(v_a_4557_);
return v_res_4562_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4571_ = l_Lean_MessageData_ofFormat(v___x_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4572_, lean_object* v_h1_4573_, lean_object* v_h2_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_){
_start:
{
lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___x_4590_; uint8_t v___x_4591_; 
v___x_4590_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4591_ = l_Lean_Expr_isAppOf(v_h2_4574_, v___x_4590_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
lean_inc_ref(v_h2_4574_);
v___x_4592_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref_known(v___x_4592_, 1);
v___x_4594_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4595_ = lean_unsigned_to_nat(3u);
v___x_4596_ = l_Lean_Expr_isAppOfArity(v_a_4593_, v___x_4594_, v___x_4595_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
lean_dec_ref(v_h1_4573_);
lean_dec_ref(v_motive_4572_);
v___x_4597_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4598_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4599_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4574_, v_a_4593_);
v___x_4600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4598_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
v___x_4601_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4597_, v___x_4600_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
return v___x_4601_;
}
else
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4602_ = l_Lean_Expr_appFn_x21(v_a_4593_);
v___x_4603_ = l_Lean_Expr_appFn_x21(v___x_4602_);
v___x_4604_ = l_Lean_Expr_appArg_x21(v___x_4603_);
lean_dec_ref(v___x_4603_);
v___x_4605_ = l_Lean_Expr_appArg_x21(v___x_4602_);
lean_dec_ref(v___x_4602_);
v___x_4606_ = l_Lean_Expr_appArg_x21(v_a_4593_);
lean_dec(v_a_4593_);
lean_inc_ref(v___x_4604_);
v___x_4607_ = l_Lean_Meta_getLevel(v___x_4604_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v___x_4609_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_a_4608_);
lean_dec_ref_known(v___x_4607_, 1);
lean_inc_ref(v_motive_4572_);
v___x_4609_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4572_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4633_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4633_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4633_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
if (lean_obj_tag(v_a_4610_) == 7)
{
lean_object* v_body_4614_; 
v_body_4614_ = lean_ctor_get(v_a_4610_, 2);
lean_inc_ref(v_body_4614_);
lean_dec_ref_known(v_a_4610_, 3);
if (lean_obj_tag(v_body_4614_) == 3)
{
lean_object* v_u_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v_u_4615_ = lean_ctor_get(v_body_4614_, 0);
lean_inc(v_u_4615_);
lean_dec_ref_known(v_body_4614_, 1);
v___x_4616_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4617_ = lean_box(0);
v___x_4618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4618_, 0, v_a_4608_);
lean_ctor_set(v___x_4618_, 1, v___x_4617_);
v___x_4619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4619_, 0, v_u_4615_);
lean_ctor_set(v___x_4619_, 1, v___x_4618_);
v___x_4620_ = l_Lean_mkConst(v___x_4616_, v___x_4619_);
v___x_4621_ = lean_unsigned_to_nat(6u);
v___x_4622_ = lean_mk_empty_array_with_capacity(v___x_4621_);
v___x_4623_ = lean_array_push(v___x_4622_, v___x_4604_);
v___x_4624_ = lean_array_push(v___x_4623_, v___x_4605_);
v___x_4625_ = lean_array_push(v___x_4624_, v_motive_4572_);
v___x_4626_ = lean_array_push(v___x_4625_, v_h1_4573_);
v___x_4627_ = lean_array_push(v___x_4626_, v___x_4606_);
v___x_4628_ = lean_array_push(v___x_4627_, v_h2_4574_);
v___x_4629_ = l_Lean_mkAppN(v___x_4620_, v___x_4628_);
lean_dec_ref(v___x_4628_);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4629_);
v___x_4631_ = v___x_4612_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4629_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
else
{
lean_dec_ref(v_body_4614_);
lean_del_object(v___x_4612_);
lean_dec(v_a_4608_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v___x_4604_);
lean_dec_ref(v_h2_4574_);
lean_dec_ref(v_h1_4573_);
v___y_4581_ = v_a_4575_;
v___y_4582_ = v_a_4576_;
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
goto v___jp_4580_;
}
}
else
{
lean_del_object(v___x_4612_);
lean_dec(v_a_4610_);
lean_dec(v_a_4608_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v___x_4604_);
lean_dec_ref(v_h2_4574_);
lean_dec_ref(v_h1_4573_);
v___y_4581_ = v_a_4575_;
v___y_4582_ = v_a_4576_;
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
goto v___jp_4580_;
}
}
}
else
{
lean_dec(v_a_4608_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v___x_4604_);
lean_dec_ref(v_h2_4574_);
lean_dec_ref(v_h1_4573_);
lean_dec_ref(v_motive_4572_);
return v___x_4609_;
}
}
else
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v___x_4604_);
lean_dec_ref(v_h2_4574_);
lean_dec_ref(v_h1_4573_);
lean_dec_ref(v_motive_4572_);
v_a_4634_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4607_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4607_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4574_);
lean_dec_ref(v_h1_4573_);
lean_dec_ref(v_motive_4572_);
return v___x_4592_;
}
}
else
{
lean_object* v___x_4642_; 
lean_dec_ref(v_h2_4574_);
lean_dec_ref(v_motive_4572_);
v___x_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4642_, 0, v_h1_4573_);
return v___x_4642_;
}
v___jp_4580_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4585_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4586_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4587_ = l_Lean_indentExpr(v_motive_4572_);
v___x_4588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4586_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
v___x_4589_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4585_, v___x_4588_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
return v___x_4589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4643_, lean_object* v_h1_4644_, lean_object* v_h2_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Lean_Meta_mkEqNDRec(v_motive_4643_, v_h1_4644_, v_h2_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4656_, lean_object* v_h1_4657_, lean_object* v_h2_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v___x_4674_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4675_ = l_Lean_Expr_isAppOf(v_h2_4658_, v___x_4674_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; 
lean_inc_ref(v_h2_4658_);
v___x_4676_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4676_, 1);
v___x_4678_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4679_ = lean_unsigned_to_nat(3u);
v___x_4680_ = l_Lean_Expr_isAppOfArity(v_a_4677_, v___x_4678_, v___x_4679_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
lean_dec(v_a_4677_);
lean_dec_ref(v_h1_4657_);
lean_dec_ref(v_motive_4656_);
v___x_4681_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4682_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4683_ = l_Lean_indentExpr(v_h2_4658_);
v___x_4684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4682_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
v___x_4685_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4681_, v___x_4684_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
return v___x_4685_;
}
else
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4686_ = l_Lean_Expr_appFn_x21(v_a_4677_);
v___x_4687_ = l_Lean_Expr_appFn_x21(v___x_4686_);
v___x_4688_ = l_Lean_Expr_appArg_x21(v___x_4687_);
lean_dec_ref(v___x_4687_);
v___x_4689_ = l_Lean_Expr_appArg_x21(v___x_4686_);
lean_dec_ref(v___x_4686_);
v___x_4690_ = l_Lean_Expr_appArg_x21(v_a_4677_);
lean_dec(v_a_4677_);
lean_inc_ref(v___x_4688_);
v___x_4691_ = l_Lean_Meta_getLevel(v___x_4688_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4693_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_a_4692_);
lean_dec_ref_known(v___x_4691_, 1);
lean_inc_ref(v_motive_4656_);
v___x_4693_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4656_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4718_; 
v_a_4694_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4696_ = v___x_4693_;
v_isShared_4697_ = v_isSharedCheck_4718_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4693_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4718_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
if (lean_obj_tag(v_a_4694_) == 7)
{
lean_object* v_body_4698_; 
v_body_4698_ = lean_ctor_get(v_a_4694_, 2);
lean_inc_ref(v_body_4698_);
lean_dec_ref_known(v_a_4694_, 3);
if (lean_obj_tag(v_body_4698_) == 7)
{
lean_object* v_body_4699_; 
v_body_4699_ = lean_ctor_get(v_body_4698_, 2);
lean_inc_ref(v_body_4699_);
lean_dec_ref_known(v_body_4698_, 3);
if (lean_obj_tag(v_body_4699_) == 3)
{
lean_object* v_u_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; 
v_u_4700_ = lean_ctor_get(v_body_4699_, 0);
lean_inc(v_u_4700_);
lean_dec_ref_known(v_body_4699_, 1);
v___x_4701_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4702_ = lean_box(0);
v___x_4703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4703_, 0, v_a_4692_);
lean_ctor_set(v___x_4703_, 1, v___x_4702_);
v___x_4704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4704_, 0, v_u_4700_);
lean_ctor_set(v___x_4704_, 1, v___x_4703_);
v___x_4705_ = l_Lean_mkConst(v___x_4701_, v___x_4704_);
v___x_4706_ = lean_unsigned_to_nat(6u);
v___x_4707_ = lean_mk_empty_array_with_capacity(v___x_4706_);
v___x_4708_ = lean_array_push(v___x_4707_, v___x_4688_);
v___x_4709_ = lean_array_push(v___x_4708_, v___x_4689_);
v___x_4710_ = lean_array_push(v___x_4709_, v_motive_4656_);
v___x_4711_ = lean_array_push(v___x_4710_, v_h1_4657_);
v___x_4712_ = lean_array_push(v___x_4711_, v___x_4690_);
v___x_4713_ = lean_array_push(v___x_4712_, v_h2_4658_);
v___x_4714_ = l_Lean_mkAppN(v___x_4705_, v___x_4713_);
lean_dec_ref(v___x_4713_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v___x_4714_);
v___x_4716_ = v___x_4696_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4714_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
else
{
lean_dec_ref(v_body_4699_);
lean_del_object(v___x_4696_);
lean_dec(v_a_4692_);
lean_dec_ref(v___x_4690_);
lean_dec_ref(v___x_4689_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v_h2_4658_);
lean_dec_ref(v_h1_4657_);
v___y_4665_ = v_a_4659_;
v___y_4666_ = v_a_4660_;
v___y_4667_ = v_a_4661_;
v___y_4668_ = v_a_4662_;
goto v___jp_4664_;
}
}
else
{
lean_dec_ref(v_body_4698_);
lean_del_object(v___x_4696_);
lean_dec(v_a_4692_);
lean_dec_ref(v___x_4690_);
lean_dec_ref(v___x_4689_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v_h2_4658_);
lean_dec_ref(v_h1_4657_);
v___y_4665_ = v_a_4659_;
v___y_4666_ = v_a_4660_;
v___y_4667_ = v_a_4661_;
v___y_4668_ = v_a_4662_;
goto v___jp_4664_;
}
}
else
{
lean_del_object(v___x_4696_);
lean_dec(v_a_4694_);
lean_dec(v_a_4692_);
lean_dec_ref(v___x_4690_);
lean_dec_ref(v___x_4689_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v_h2_4658_);
lean_dec_ref(v_h1_4657_);
v___y_4665_ = v_a_4659_;
v___y_4666_ = v_a_4660_;
v___y_4667_ = v_a_4661_;
v___y_4668_ = v_a_4662_;
goto v___jp_4664_;
}
}
}
else
{
lean_dec(v_a_4692_);
lean_dec_ref(v___x_4690_);
lean_dec_ref(v___x_4689_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v_h2_4658_);
lean_dec_ref(v_h1_4657_);
lean_dec_ref(v_motive_4656_);
return v___x_4693_;
}
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
lean_dec_ref(v___x_4690_);
lean_dec_ref(v___x_4689_);
lean_dec_ref(v___x_4688_);
lean_dec_ref(v_h2_4658_);
lean_dec_ref(v_h1_4657_);
lean_dec_ref(v_motive_4656_);
v_a_4719_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4691_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4691_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4658_);
lean_dec_ref(v_h1_4657_);
lean_dec_ref(v_motive_4656_);
return v___x_4676_;
}
}
else
{
lean_object* v___x_4727_; 
lean_dec_ref(v_h2_4658_);
lean_dec_ref(v_motive_4656_);
v___x_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4727_, 0, v_h1_4657_);
return v___x_4727_;
}
v___jp_4664_:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4669_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4670_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4671_ = l_Lean_indentExpr(v_motive_4656_);
v___x_4672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4670_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
v___x_4673_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4669_, v___x_4672_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
return v___x_4673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4728_, lean_object* v_h1_4729_, lean_object* v_h2_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_Meta_mkEqRec(v_motive_4728_, v_h1_4729_, v_h2_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
lean_dec(v_a_4734_);
lean_dec_ref(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore(lean_object* v_00_u03b1_4741_, lean_object* v_00_u03b2_4742_, lean_object* v_h_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
lean_object* v___x_4750_; 
lean_inc_ref(v_00_u03b1_4741_);
v___x_4750_ = l_Lean_Meta_getLevel(v_00_u03b1_4741_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_);
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4763_; 
v_a_4751_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4753_ = v___x_4750_;
v_isShared_4754_ = v_isSharedCheck_4763_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4750_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4763_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4761_; 
v___x_4755_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4756_ = lean_box(0);
v___x_4757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4757_, 0, v_a_4751_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
v___x_4758_ = l_Lean_mkConst(v___x_4755_, v___x_4757_);
v___x_4759_ = l_Lean_mkApp4(v___x_4758_, v_00_u03b1_4741_, v_00_u03b2_4742_, v_h_4743_, v_a_4744_);
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 0, v___x_4759_);
v___x_4761_ = v___x_4753_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4759_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_dec_ref(v_a_4744_);
lean_dec_ref(v_h_4743_);
lean_dec_ref(v_00_u03b2_4742_);
lean_dec_ref(v_00_u03b1_4741_);
v_a_4764_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4750_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4750_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore___boxed(lean_object* v_00_u03b1_4772_, lean_object* v_00_u03b2_4773_, lean_object* v_h_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Lean_Meta_mkEqMPCore(v_00_u03b1_4772_, v_00_u03b2_4773_, v_h_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4782_, lean_object* v_pr_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_){
_start:
{
lean_object* v___x_4789_; 
lean_inc_ref(v_eqProof_4782_);
v___x_4789_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_eqProof_4782_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref_known(v___x_4789_, 1);
v___x_4791_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4792_ = lean_unsigned_to_nat(3u);
v___x_4793_ = l_Lean_Expr_isAppOfArity(v_a_4790_, v___x_4791_, v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
lean_dec_ref(v_pr_4783_);
v___x_4794_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4795_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4796_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_eqProof_4782_, v_a_4790_);
v___x_4797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4795_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v___x_4798_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4794_, v___x_4797_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_);
return v___x_4798_;
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4799_ = l_Lean_Expr_appFn_x21(v_a_4790_);
v___x_4800_ = l_Lean_Expr_appArg_x21(v___x_4799_);
lean_dec_ref(v___x_4799_);
v___x_4801_ = l_Lean_Expr_appArg_x21(v_a_4790_);
lean_dec(v_a_4790_);
v___x_4802_ = l_Lean_Meta_mkEqMPCore(v___x_4800_, v___x_4801_, v_eqProof_4782_, v_pr_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_);
return v___x_4802_;
}
}
else
{
lean_dec_ref(v_pr_4783_);
lean_dec_ref(v_eqProof_4782_);
return v___x_4789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4803_, lean_object* v_pr_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Lean_Meta_mkEqMP(v_eqProof_4803_, v_pr_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4815_, lean_object* v_pr_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_){
_start:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4822_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4823_ = lean_unsigned_to_nat(2u);
v___x_4824_ = lean_mk_empty_array_with_capacity(v___x_4823_);
v___x_4825_ = lean_array_push(v___x_4824_, v_eqProof_4815_);
v___x_4826_ = lean_array_push(v___x_4825_, v_pr_4816_);
v___x_4827_ = l_Lean_Meta_mkAppM(v___x_4822_, v___x_4826_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4828_, lean_object* v_pr_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l_Lean_Meta_mkEqMPR(v_eqProof_4828_, v_pr_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_);
lean_dec(v_a_4833_);
lean_dec_ref(v_a_4832_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
return v_res_4835_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v___f_4842_; lean_object* v___x_12329__overap_4843_; lean_object* v___x_4844_; 
v___f_4842_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12329__overap_4843_ = lean_panic_fn_borrowed(v___f_4842_, v_msg_4836_);
lean_inc(v___y_4840_);
lean_inc_ref(v___y_4839_);
lean_inc(v___y_4838_);
lean_inc_ref(v___y_4837_);
v___x_4844_ = lean_apply_5(v___x_12329__overap_4843_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, lean_box(0));
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4852_, uint8_t v_skipRealize_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v___x_4856_; lean_object* v_env_4857_; uint8_t v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4856_ = lean_st_ref_get(v___y_4854_);
v_env_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc_ref(v_env_4857_);
lean_dec(v___x_4856_);
v___x_4858_ = l_Lean_Environment_contains(v_env_4857_, v_constName_4852_, v_skipRealize_4853_);
v___x_4859_ = lean_box(v___x_4858_);
v___x_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4859_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4861_, lean_object* v_skipRealize_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
uint8_t v_skipRealize_boxed_4865_; lean_object* v_res_4866_; 
v_skipRealize_boxed_4865_ = lean_unbox(v_skipRealize_4862_);
v_res_4866_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4861_, v_skipRealize_boxed_4865_, v___y_4863_);
lean_dec(v___y_4863_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4867_, uint8_t v_skipRealize_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v___x_4874_; 
v___x_4874_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4867_, v_skipRealize_4868_, v___y_4872_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4875_, lean_object* v_skipRealize_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
uint8_t v_skipRealize_boxed_4882_; lean_object* v_res_4883_; 
v_skipRealize_boxed_4882_ = lean_unbox(v_skipRealize_4876_);
v_res_4883_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4875_, v_skipRealize_boxed_4882_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___y_4884_, uint8_t v___x_4885_, lean_object* v_P_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; lean_object* v___x_4896_; 
v___x_4892_ = lean_unsigned_to_nat(1u);
v___x_4893_ = lean_mk_empty_array_with_capacity(v___x_4892_);
lean_inc_ref(v_P_4886_);
v___x_4894_ = lean_array_push(v___x_4893_, v_P_4886_);
v___x_4895_ = 1;
v___x_4896_ = l_Lean_Meta_mkLambdaFVars(v___x_4894_, v_P_4886_, v___y_4884_, v___x_4885_, v___y_4884_, v___x_4885_, v___x_4895_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec_ref(v___x_4894_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___y_4897_, lean_object* v___x_4898_, lean_object* v_P_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_){
_start:
{
uint8_t v___y_13587__boxed_4905_; uint8_t v___x_13588__boxed_4906_; lean_object* v_res_4907_; 
v___y_13587__boxed_4905_ = lean_unbox(v___y_4897_);
v___x_13588__boxed_4906_ = lean_unbox(v___x_4898_);
v_res_4907_ = l_Lean_Meta_mkNoConfusion___lam__0(v___y_13587__boxed_4905_, v___x_13588__boxed_4906_, v_P_4899_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
return v_res_4907_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4909_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4910_ = l_Lean_stringToMessageData(v___x_4909_);
return v___x_4910_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4913_ = l_Lean_stringToMessageData(v___x_4912_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4914_, lean_object* v_b_4915_, lean_object* v_i_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_){
_start:
{
lean_object* v_stop_4922_; lean_object* v_step_4923_; lean_object* v_a_4925_; uint8_t v___x_4928_; 
v_stop_4922_ = lean_ctor_get(v_range_4914_, 1);
v_step_4923_ = lean_ctor_get(v_range_4914_, 2);
v___x_4928_ = lean_nat_dec_lt(v_i_4916_, v_stop_4922_);
if (v___x_4928_ == 0)
{
lean_object* v___x_4929_; 
lean_dec(v_i_4916_);
v___x_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4929_, 0, v_b_4915_);
return v___x_4929_;
}
else
{
lean_object* v___x_4930_; 
lean_inc(v___y_4920_);
lean_inc_ref(v___y_4919_);
lean_inc(v___y_4918_);
lean_inc_ref(v___y_4917_);
lean_inc_ref(v_b_4915_);
v___x_4930_ = lean_infer_type(v_b_4915_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = l_Lean_Meta_whnfForall(v_a_4931_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
lean_dec_ref_known(v___x_4932_, 1);
v___x_4934_ = l_Lean_Expr_bindingDomain_x21(v_a_4933_);
lean_dec(v_a_4933_);
lean_inc(v___y_4920_);
lean_inc_ref(v___y_4919_);
lean_inc(v___y_4918_);
lean_inc_ref(v___y_4917_);
v___x_4935_ = lean_whnf(v___x_4934_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v_a_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; uint8_t v___x_4939_; 
v_a_4936_ = lean_ctor_get(v___x_4935_, 0);
lean_inc(v_a_4936_);
lean_dec_ref_known(v___x_4935_, 1);
v___x_4937_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4938_ = lean_unsigned_to_nat(4u);
v___x_4939_ = l_Lean_Expr_isAppOfArity(v_a_4936_, v___x_4937_, v___x_4938_);
if (v___x_4939_ == 0)
{
lean_object* v___x_4940_; lean_object* v___x_4941_; uint8_t v___x_4942_; 
v___x_4940_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4941_ = lean_unsigned_to_nat(3u);
v___x_4942_ = l_Lean_Expr_isAppOfArity(v_a_4936_, v___x_4940_, v___x_4941_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; 
lean_dec(v_i_4916_);
lean_inc(v___y_4920_);
lean_inc_ref(v___y_4919_);
lean_inc(v___y_4918_);
lean_inc_ref(v___y_4917_);
v___x_4943_ = lean_infer_type(v_b_4915_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v_a_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc(v_a_4944_);
lean_dec_ref_known(v___x_4943_, 1);
v___x_4945_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4946_ = l_Lean_MessageData_ofExpr(v_a_4936_);
v___x_4947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4945_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
v___x_4948_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4947_);
lean_ctor_set(v___x_4949_, 1, v___x_4948_);
v___x_4950_ = lean_unsigned_to_nat(30u);
v___x_4951_ = l_Lean_inlineExpr(v_a_4944_, v___x_4950_);
v___x_4952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4949_);
lean_ctor_set(v___x_4952_, 1, v___x_4951_);
v___x_4953_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4952_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
v_a_4954_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4953_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4953_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
else
{
lean_dec(v_a_4936_);
return v___x_4943_;
}
}
else
{
lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4962_ = l_Lean_Expr_appFn_x21(v_a_4936_);
lean_dec(v_a_4936_);
v___x_4963_ = l_Lean_Expr_appArg_x21(v___x_4962_);
lean_dec_ref(v___x_4962_);
v___x_4964_ = l_Lean_Meta_mkEqRefl(v___x_4963_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v___x_4966_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
v___x_4966_ = l_Lean_Expr_app___override(v_b_4915_, v_a_4965_);
v_a_4925_ = v___x_4966_;
goto v___jp_4924_;
}
else
{
lean_dec(v_i_4916_);
lean_dec_ref(v_b_4915_);
return v___x_4964_;
}
}
}
else
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4967_ = l_Lean_Expr_appFn_x21(v_a_4936_);
lean_dec(v_a_4936_);
v___x_4968_ = l_Lean_Expr_appFn_x21(v___x_4967_);
lean_dec_ref(v___x_4967_);
v___x_4969_ = l_Lean_Expr_appArg_x21(v___x_4968_);
lean_dec_ref(v___x_4968_);
v___x_4970_ = l_Lean_Meta_mkHEqRefl(v___x_4969_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; lean_object* v___x_4972_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
lean_inc(v_a_4971_);
lean_dec_ref_known(v___x_4970_, 1);
v___x_4972_ = l_Lean_Expr_app___override(v_b_4915_, v_a_4971_);
v_a_4925_ = v___x_4972_;
goto v___jp_4924_;
}
else
{
lean_dec(v_i_4916_);
lean_dec_ref(v_b_4915_);
return v___x_4970_;
}
}
}
else
{
lean_dec(v_i_4916_);
lean_dec_ref(v_b_4915_);
return v___x_4935_;
}
}
else
{
lean_dec(v_i_4916_);
lean_dec_ref(v_b_4915_);
return v___x_4932_;
}
}
else
{
lean_dec(v_i_4916_);
lean_dec_ref(v_b_4915_);
return v___x_4930_;
}
}
v___jp_4924_:
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_nat_add(v_i_4916_, v_step_4923_);
lean_dec(v_i_4916_);
v_b_4915_ = v_a_4925_;
v_i_4916_ = v___x_4926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4973_, lean_object* v_b_4974_, lean_object* v_i_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v_res_4981_; 
v_res_4981_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4973_, v_b_4974_, v_i_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec_ref(v_range_4973_);
return v_res_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4982_, lean_object* v_b_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v___x_4989_; 
lean_inc(v___y_4987_);
lean_inc_ref(v___y_4986_);
lean_inc(v___y_4985_);
lean_inc_ref(v___y_4984_);
v___x_4989_ = lean_apply_6(v_k_4982_, v_b_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, lean_box(0));
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4990_, lean_object* v_b_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4990_, v_b_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4998_, uint8_t v_bi_4999_, lean_object* v_type_5000_, lean_object* v_k_5001_, uint8_t v_kind_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v___f_5008_; lean_object* v___x_5009_; 
v___f_5008_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5008_, 0, v_k_5001_);
v___x_5009_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4998_, v_bi_4999_, v_type_5000_, v___f_5008_, v_kind_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_5009_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_5009_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
v_a_5018_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5009_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5009_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_5026_, lean_object* v_bi_5027_, lean_object* v_type_5028_, lean_object* v_k_5029_, lean_object* v_kind_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
uint8_t v_bi_boxed_5036_; uint8_t v_kind_boxed_5037_; lean_object* v_res_5038_; 
v_bi_boxed_5036_ = lean_unbox(v_bi_5027_);
v_kind_boxed_5037_ = lean_unbox(v_kind_5030_);
v_res_5038_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5026_, v_bi_boxed_5036_, v_type_5028_, v_k_5029_, v_kind_boxed_5037_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_5039_, lean_object* v_type_5040_, lean_object* v_k_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
uint8_t v___x_5047_; uint8_t v___x_5048_; lean_object* v___x_5049_; 
v___x_5047_ = 0;
v___x_5048_ = 0;
v___x_5049_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5039_, v___x_5047_, v_type_5040_, v_k_5041_, v___x_5048_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_5050_, lean_object* v_type_5051_, lean_object* v_k_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5050_, v_type_5051_, v_k_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
return v_res_5058_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_5066_ = l_Lean_MessageData_ofFormat(v___x_5065_);
return v___x_5066_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6(void){
_start:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5068_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__5));
v___x_5069_ = l_Lean_stringToMessageData(v___x_5068_);
return v___x_5069_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8(void){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5071_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__7));
v___x_5072_ = l_Lean_stringToMessageData(v___x_5071_);
return v___x_5072_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_5077_ = l_Lean_MessageData_ofFormat(v___x_5076_);
return v___x_5077_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__14(void){
_start:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5080_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__13));
v___x_5081_ = lean_unsigned_to_nat(10u);
v___x_5082_ = lean_unsigned_to_nat(511u);
v___x_5083_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5084_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5085_ = l_mkPanicMessageWithDecl(v___x_5084_, v___x_5083_, v___x_5082_, v___x_5081_, v___x_5080_);
return v___x_5085_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5087_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5088_ = l_Lean_stringToMessageData(v___x_5087_);
return v___x_5088_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__23(void){
_start:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__22));
v___x_5098_ = l_Lean_stringToMessageData(v___x_5097_);
return v___x_5098_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__24(void){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5100_ = l_Lean_MessageData_ofName(v___x_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5101_, lean_object* v_h_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_){
_start:
{
lean_object* v___x_5108_; 
lean_inc(v_a_5106_);
lean_inc_ref(v_a_5105_);
lean_inc(v_a_5104_);
lean_inc_ref(v_a_5103_);
lean_inc_ref(v_h_5102_);
v___x_5108_ = lean_infer_type(v_h_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5110_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___x_5108_, 1);
lean_inc(v_a_5106_);
lean_inc_ref(v_a_5105_);
lean_inc(v_a_5104_);
lean_inc_ref(v_a_5103_);
v___x_5110_ = lean_whnf(v_a_5109_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; uint8_t v___x_5114_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___x_5110_, 1);
v___x_5112_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5113_ = lean_unsigned_to_nat(3u);
v___x_5114_ = l_Lean_Expr_isAppOfArity(v_a_5111_, v___x_5112_, v___x_5113_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; 
lean_dec_ref(v_target_5101_);
v___x_5115_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5116_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5117_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5102_, v_a_5111_);
v___x_5118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5116_);
lean_ctor_set(v___x_5118_, 1, v___x_5117_);
v___x_5119_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5115_, v___x_5118_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
return v___x_5119_;
}
else
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v___y_5128_; lean_object* v___y_5129_; lean_object* v___x_5138_; 
v___x_5120_ = l_Lean_Expr_appFn_x21(v_a_5111_);
v___x_5121_ = l_Lean_Expr_appFn_x21(v___x_5120_);
v___x_5122_ = l_Lean_Expr_appArg_x21(v___x_5121_);
lean_dec_ref(v___x_5121_);
v___x_5123_ = l_Lean_Expr_appArg_x21(v___x_5120_);
lean_dec_ref(v___x_5120_);
v___x_5124_ = l_Lean_Expr_appArg_x21(v_a_5111_);
lean_dec(v_a_5111_);
v___x_5138_ = l_Lean_Meta_whnfD(v___x_5122_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v___y_5143_; lean_object* v___y_5144_; lean_object* v___x_5150_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_a_5139_);
lean_dec_ref_known(v___x_5138_, 1);
v___x_5150_ = l_Lean_Expr_getAppFn(v_a_5139_);
if (lean_obj_tag(v___x_5150_) == 4)
{
lean_object* v_declName_5151_; lean_object* v_us_5152_; lean_object* v___x_5153_; lean_object* v_env_5154_; uint8_t v___x_5155_; lean_object* v___x_5156_; 
v_declName_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_declName_5151_);
v_us_5152_ = lean_ctor_get(v___x_5150_, 1);
lean_inc(v_us_5152_);
lean_dec_ref_known(v___x_5150_, 2);
v___x_5153_ = lean_st_ref_get(v_a_5106_);
v_env_5154_ = lean_ctor_get(v___x_5153_, 0);
lean_inc_ref(v_env_5154_);
lean_dec(v___x_5153_);
v___x_5155_ = 0;
v___x_5156_ = l_Lean_Environment_find_x3f(v_env_5154_, v_declName_5151_, v___x_5155_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_dec(v_us_5152_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v___y_5141_ = v_a_5103_;
v___y_5142_ = v_a_5104_;
v___y_5143_ = v_a_5105_;
v___y_5144_ = v_a_5106_;
goto v___jp_5140_;
}
else
{
lean_object* v_val_5157_; 
v_val_5157_ = lean_ctor_get(v___x_5156_, 0);
lean_inc(v_val_5157_);
lean_dec_ref_known(v___x_5156_, 1);
if (lean_obj_tag(v_val_5157_) == 5)
{
lean_object* v_val_5158_; lean_object* v___x_5159_; 
v_val_5158_ = lean_ctor_get(v_val_5157_, 0);
lean_inc_ref(v_val_5158_);
lean_dec_ref_known(v_val_5157_, 1);
lean_inc_ref(v_target_5101_);
v___x_5159_ = l_Lean_Meta_getLevel(v_target_5101_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v___x_5161_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5159_, 1);
lean_inc_ref(v___x_5123_);
v___x_5161_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5123_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
if (lean_obj_tag(v_a_5162_) == 1)
{
lean_object* v_val_5163_; lean_object* v_fst_5164_; lean_object* v_snd_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5379_; 
v_val_5163_ = lean_ctor_get(v_a_5162_, 0);
lean_inc(v_val_5163_);
lean_dec_ref_known(v_a_5162_, 1);
v_fst_5164_ = lean_ctor_get(v_val_5163_, 0);
v_snd_5165_ = lean_ctor_get(v_val_5163_, 1);
v_isSharedCheck_5379_ = !lean_is_exclusive(v_val_5163_);
if (v_isSharedCheck_5379_ == 0)
{
v___x_5167_ = v_val_5163_;
v_isShared_5168_ = v_isSharedCheck_5379_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_snd_5165_);
lean_inc(v_fst_5164_);
lean_dec(v_val_5163_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5379_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5169_; 
lean_inc_ref(v___x_5124_);
v___x_5169_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5124_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
lean_dec_ref_known(v___x_5169_, 1);
if (lean_obj_tag(v_a_5170_) == 1)
{
lean_object* v_val_5171_; lean_object* v_fst_5172_; lean_object* v_snd_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5370_; 
v_val_5171_ = lean_ctor_get(v_a_5170_, 0);
lean_inc(v_val_5171_);
lean_dec_ref_known(v_a_5170_, 1);
v_fst_5172_ = lean_ctor_get(v_val_5171_, 0);
v_snd_5173_ = lean_ctor_get(v_val_5171_, 1);
v_isSharedCheck_5370_ = !lean_is_exclusive(v_val_5171_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5175_ = v_val_5171_;
v_isShared_5176_ = v_isSharedCheck_5370_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_snd_5173_);
lean_inc(v_fst_5172_);
lean_dec(v_val_5171_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5370_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v_toConstantVal_5177_; lean_object* v_cidx_5178_; lean_object* v_numParams_5179_; lean_object* v_numFields_5180_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___y_5184_; lean_object* v___y_5185_; lean_object* v___y_5186_; lean_object* v___y_5187_; uint8_t v___y_5272_; lean_object* v_cidx_5300_; uint8_t v___x_5301_; 
v_toConstantVal_5177_ = lean_ctor_get(v_fst_5164_, 0);
lean_inc_ref(v_toConstantVal_5177_);
v_cidx_5178_ = lean_ctor_get(v_fst_5164_, 2);
lean_inc(v_cidx_5178_);
v_numParams_5179_ = lean_ctor_get(v_fst_5164_, 3);
lean_inc(v_numParams_5179_);
v_numFields_5180_ = lean_ctor_get(v_fst_5164_, 4);
lean_inc(v_numFields_5180_);
lean_dec(v_fst_5164_);
v_cidx_5300_ = lean_ctor_get(v_fst_5172_, 2);
lean_inc(v_cidx_5300_);
lean_dec(v_fst_5172_);
v___x_5301_ = lean_nat_dec_eq(v_cidx_5178_, v_cidx_5300_);
lean_dec(v_cidx_5300_);
lean_dec(v_cidx_5178_);
if (v___x_5301_ == 0)
{
if (v___x_5114_ == 0)
{
lean_dec_ref(v_val_5158_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
v___y_5272_ = v___x_5114_;
goto v___jp_5271_;
}
else
{
lean_object* v_toConstantVal_5302_; lean_object* v_name_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v_a_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v_a_5310_; uint8_t v___x_5328_; 
lean_dec(v_numFields_5180_);
lean_dec(v_numParams_5179_);
lean_dec_ref(v_toConstantVal_5177_);
lean_del_object(v___x_5175_);
lean_dec(v_snd_5173_);
lean_del_object(v___x_5167_);
lean_dec(v_snd_5165_);
v_toConstantVal_5302_ = lean_ctor_get(v_val_5158_, 0);
lean_inc_ref(v_toConstantVal_5302_);
lean_dec_ref(v_val_5158_);
v_name_5303_ = lean_ctor_get(v_toConstantVal_5302_, 0);
lean_inc(v_name_5303_);
lean_dec_ref(v_toConstantVal_5302_);
v___x_5304_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__19));
v___x_5305_ = l_Lean_Name_str___override(v_name_5303_, v___x_5304_);
lean_inc(v___x_5305_);
v___x_5306_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5305_, v___x_5114_, v_a_5106_);
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5307_);
lean_dec_ref(v___x_5306_);
v___x_5308_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5309_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5308_, v___x_5114_, v_a_5106_);
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc(v_a_5310_);
lean_dec_ref(v___x_5309_);
v___x_5328_ = lean_unbox(v_a_5307_);
lean_dec(v_a_5307_);
if (v___x_5328_ == 0)
{
lean_dec(v_a_5310_);
lean_dec(v_a_5160_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
goto v___jp_5311_;
}
else
{
uint8_t v___x_5329_; 
v___x_5329_ = lean_unbox(v_a_5310_);
lean_dec(v_a_5310_);
if (v___x_5329_ == 0)
{
lean_dec(v_a_5160_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
goto v___jp_5311_;
}
else
{
lean_object* v___x_5330_; lean_object* v_dummy_5331_; lean_object* v_nargs_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5330_ = l_Lean_mkConst(v___x_5305_, v_us_5152_);
v_dummy_5331_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5332_ = l_Lean_Expr_getAppNumArgs(v_a_5139_);
lean_inc(v_nargs_5332_);
v___x_5333_ = lean_mk_array(v_nargs_5332_, v_dummy_5331_);
v___x_5334_ = lean_unsigned_to_nat(1u);
v___x_5335_ = lean_nat_sub(v_nargs_5332_, v___x_5334_);
lean_dec(v_nargs_5332_);
lean_inc_n(v_a_5139_, 2);
v___x_5336_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5139_, v___x_5333_, v___x_5335_);
v___x_5337_ = l_Lean_mkAppN(v___x_5330_, v___x_5336_);
lean_dec_ref(v___x_5336_);
v___x_5338_ = l_Lean_Meta_getLevel(v_a_5139_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
if (lean_obj_tag(v___x_5338_) == 0)
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5361_; 
v_a_5339_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5341_ = v___x_5338_;
v_isShared_5342_ = v_isSharedCheck_5361_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5338_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5361_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5359_; 
v___x_5343_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5344_ = lean_box(0);
v___x_5345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5345_, 0, v_a_5160_);
lean_ctor_set(v___x_5345_, 1, v___x_5344_);
v___x_5346_ = l_Lean_mkConst(v___x_5343_, v___x_5345_);
v___x_5347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5347_, 0, v_a_5339_);
lean_ctor_set(v___x_5347_, 1, v___x_5344_);
v___x_5348_ = l_Lean_mkConst(v___x_5308_, v___x_5347_);
v___x_5349_ = lean_unsigned_to_nat(5u);
v___x_5350_ = lean_mk_empty_array_with_capacity(v___x_5349_);
v___x_5351_ = lean_array_push(v___x_5350_, v_a_5139_);
v___x_5352_ = lean_array_push(v___x_5351_, v___x_5337_);
v___x_5353_ = lean_array_push(v___x_5352_, v___x_5123_);
v___x_5354_ = lean_array_push(v___x_5353_, v___x_5124_);
v___x_5355_ = lean_array_push(v___x_5354_, v_h_5102_);
v___x_5356_ = l_Lean_mkAppN(v___x_5348_, v___x_5355_);
lean_dec_ref(v___x_5355_);
v___x_5357_ = l_Lean_mkAppB(v___x_5346_, v_target_5101_, v___x_5356_);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 0, v___x_5357_);
v___x_5359_ = v___x_5341_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v___x_5357_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
lean_dec_ref(v___x_5337_);
lean_dec(v_a_5160_);
lean_dec(v_a_5139_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v_a_5362_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5338_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5338_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5362_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
}
v___jp_5311_:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
v___x_5312_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5313_ = l_Lean_MessageData_ofName(v___x_5305_);
v___x_5314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5312_);
lean_ctor_set(v___x_5314_, 1, v___x_5313_);
v___x_5315_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__23, &l_Lean_Meta_mkNoConfusion___closed__23_once, _init_l_Lean_Meta_mkNoConfusion___closed__23);
v___x_5316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5316_, 0, v___x_5314_);
lean_ctor_set(v___x_5316_, 1, v___x_5315_);
v___x_5317_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__24, &l_Lean_Meta_mkNoConfusion___closed__24_once, _init_l_Lean_Meta_mkNoConfusion___closed__24);
v___x_5318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5316_);
lean_ctor_set(v___x_5318_, 1, v___x_5317_);
v___x_5319_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5318_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
v_a_5320_ = lean_ctor_get(v___x_5319_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5319_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___x_5319_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5319_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5325_; 
if (v_isShared_5323_ == 0)
{
v___x_5325_ = v___x_5322_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5320_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
}
}
}
else
{
lean_dec_ref(v_val_5158_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
v___y_5272_ = v___x_5155_;
goto v___jp_5271_;
}
v___jp_5181_:
{
lean_object* v___x_5188_; 
lean_inc(v___y_5183_);
v___x_5188_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v_a_5189_; lean_object* v_nargs_5190_; lean_object* v_type_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5260_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
lean_inc(v_a_5189_);
lean_dec_ref_known(v___x_5188_, 1);
v_nargs_5190_ = l_Lean_Expr_getAppNumArgs(v_a_5139_);
v_type_5191_ = lean_ctor_get(v_a_5189_, 2);
v_isSharedCheck_5260_ = !lean_is_exclusive(v_a_5189_);
if (v_isSharedCheck_5260_ == 0)
{
lean_object* v_unused_5261_; lean_object* v_unused_5262_; 
v_unused_5261_ = lean_ctor_get(v_a_5189_, 1);
lean_dec(v_unused_5261_);
v_unused_5262_ = lean_ctor_get(v_a_5189_, 0);
lean_dec(v_unused_5262_);
v___x_5193_ = v_a_5189_;
v_isShared_5194_ = v_isSharedCheck_5260_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_type_5191_);
lean_dec(v_a_5189_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5260_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v_dummy_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v_start_5201_; lean_object* v_stop_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; uint8_t v___x_5216_; 
v_dummy_5195_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
lean_inc(v_nargs_5190_);
v___x_5196_ = lean_mk_array(v_nargs_5190_, v_dummy_5195_);
v___x_5197_ = lean_unsigned_to_nat(1u);
v___x_5198_ = lean_nat_sub(v_nargs_5190_, v___x_5197_);
lean_dec(v_nargs_5190_);
v___x_5199_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5139_, v___x_5196_, v___x_5198_);
lean_inc_n(v_numParams_5179_, 2);
lean_inc(v___y_5182_);
v___x_5200_ = l_Array_toSubarray___redArg(v___x_5199_, v___y_5182_, v_numParams_5179_);
v_start_5201_ = lean_ctor_get(v___x_5200_, 1);
v_stop_5202_ = lean_ctor_get(v___x_5200_, 2);
v___x_5203_ = lean_array_get_size(v_snd_5165_);
v___x_5204_ = l_Array_toSubarray___redArg(v_snd_5165_, v_numParams_5179_, v___x_5203_);
v___x_5205_ = lean_array_get_size(v_snd_5173_);
v___x_5206_ = l_Subarray_copy___redArg(v___x_5204_);
v___x_5207_ = l_Array_toSubarray___redArg(v_snd_5173_, v_numParams_5179_, v___x_5205_);
v___x_5208_ = l_Subarray_copy___redArg(v___x_5207_);
v___x_5209_ = l_Lean_Expr_getNumHeadForalls(v_type_5191_);
lean_dec_ref(v_type_5191_);
v___x_5210_ = lean_nat_sub(v_stop_5202_, v_start_5201_);
v___x_5211_ = lean_array_get_size(v___x_5206_);
v___x_5212_ = lean_nat_add(v___x_5210_, v___x_5211_);
lean_dec(v___x_5210_);
v___x_5213_ = lean_array_get_size(v___x_5208_);
v___x_5214_ = lean_nat_add(v___x_5212_, v___x_5213_);
lean_dec(v___x_5212_);
v___x_5215_ = lean_nat_add(v___x_5214_, v___x_5113_);
lean_dec(v___x_5214_);
v___x_5216_ = lean_nat_dec_le(v___x_5215_, v___x_5209_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; lean_object* v___x_5218_; 
lean_dec(v___x_5215_);
lean_dec(v___x_5209_);
lean_dec_ref(v___x_5208_);
lean_dec_ref(v___x_5206_);
lean_dec_ref(v___x_5200_);
lean_del_object(v___x_5193_);
lean_dec(v___y_5183_);
lean_dec(v___y_5182_);
lean_del_object(v___x_5175_);
lean_dec(v_a_5160_);
lean_dec(v_us_5152_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v___x_5217_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__14, &l_Lean_Meta_mkNoConfusion___closed__14_once, _init_l_Lean_Meta_mkNoConfusion___closed__14);
v___x_5218_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5217_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
return v___x_5218_;
}
else
{
lean_object* v___x_5220_; 
if (v_isShared_5176_ == 0)
{
lean_ctor_set_tag(v___x_5175_, 1);
lean_ctor_set(v___x_5175_, 1, v_us_5152_);
lean_ctor_set(v___x_5175_, 0, v_a_5160_);
v___x_5220_ = v___x_5175_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v_a_5160_);
lean_ctor_set(v_reuseFailAlloc_5259_, 1, v_us_5152_);
v___x_5220_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5231_; 
v___x_5221_ = l_Lean_mkConst(v___y_5183_, v___x_5220_);
v___x_5222_ = l_Subarray_copy___redArg(v___x_5200_);
v___x_5223_ = l_Lean_mkAppN(v___x_5221_, v___x_5222_);
lean_dec_ref(v___x_5222_);
v___x_5224_ = lean_mk_empty_array_with_capacity(v___x_5197_);
v___x_5225_ = lean_array_push(v___x_5224_, v_target_5101_);
v___x_5226_ = l_Array_append___redArg(v___x_5225_, v___x_5206_);
lean_dec_ref(v___x_5206_);
v___x_5227_ = l_Array_append___redArg(v___x_5226_, v___x_5208_);
lean_dec_ref(v___x_5208_);
v___x_5228_ = l_Lean_mkAppN(v___x_5223_, v___x_5227_);
lean_dec_ref(v___x_5227_);
v___x_5229_ = lean_nat_sub(v___x_5209_, v___x_5215_);
lean_dec(v___x_5215_);
lean_dec(v___x_5209_);
lean_inc(v___y_5182_);
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 2, v___x_5197_);
lean_ctor_set(v___x_5193_, 1, v___x_5229_);
lean_ctor_set(v___x_5193_, 0, v___y_5182_);
v___x_5231_ = v___x_5193_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v___y_5182_);
lean_ctor_set(v_reuseFailAlloc_5258_, 1, v___x_5229_);
lean_ctor_set(v_reuseFailAlloc_5258_, 2, v___x_5197_);
v___x_5231_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
lean_object* v___x_5232_; 
v___x_5232_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5231_, v___x_5228_, v___y_5182_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
lean_dec_ref(v___x_5231_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v___x_5234_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc_n(v_a_5233_, 2);
lean_dec_ref_known(v___x_5232_, 1);
lean_inc(v___y_5187_);
lean_inc_ref(v___y_5186_);
lean_inc(v___y_5185_);
lean_inc_ref(v___y_5184_);
v___x_5234_ = lean_infer_type(v_a_5233_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
if (lean_obj_tag(v___x_5234_) == 0)
{
lean_object* v_a_5235_; lean_object* v___x_5236_; 
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5235_);
lean_dec_ref_known(v___x_5234_, 1);
v___x_5236_ = l_Lean_Meta_whnfForall(v_a_5235_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
if (lean_obj_tag(v___x_5236_) == 0)
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5257_; 
v_a_5237_ = lean_ctor_get(v___x_5236_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5236_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5239_ = v___x_5236_;
v_isShared_5240_ = v_isSharedCheck_5257_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5236_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5257_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5241_; uint8_t v___x_5242_; 
v___x_5241_ = l_Lean_Expr_bindingDomain_x21(v_a_5237_);
lean_dec(v_a_5237_);
v___x_5242_ = l_Lean_Expr_isHEq(v___x_5241_);
lean_dec_ref(v___x_5241_);
if (v___x_5242_ == 0)
{
lean_object* v___x_5243_; lean_object* v___x_5245_; 
v___x_5243_ = l_Lean_Expr_app___override(v_a_5233_, v_h_5102_);
if (v_isShared_5240_ == 0)
{
lean_ctor_set(v___x_5239_, 0, v___x_5243_);
v___x_5245_ = v___x_5239_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5243_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
else
{
lean_object* v___x_5247_; 
lean_del_object(v___x_5239_);
v___x_5247_ = l_Lean_Meta_mkHEqOfEq(v_h_5102_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5256_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5250_ = v___x_5247_;
v_isShared_5251_ = v_isSharedCheck_5256_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5247_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5256_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5252_; lean_object* v___x_5254_; 
v___x_5252_ = l_Lean_Expr_app___override(v_a_5233_, v_a_5248_);
if (v_isShared_5251_ == 0)
{
lean_ctor_set(v___x_5250_, 0, v___x_5252_);
v___x_5254_ = v___x_5250_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5252_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
else
{
lean_dec(v_a_5233_);
return v___x_5247_;
}
}
}
}
else
{
lean_dec(v_a_5233_);
lean_dec_ref(v_h_5102_);
return v___x_5236_;
}
}
else
{
lean_dec(v_a_5233_);
lean_dec_ref(v_h_5102_);
return v___x_5234_;
}
}
else
{
lean_dec_ref(v_h_5102_);
return v___x_5232_;
}
}
}
}
}
}
else
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5270_; 
lean_dec(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec(v_numParams_5179_);
lean_del_object(v___x_5175_);
lean_dec(v_snd_5173_);
lean_dec(v_snd_5165_);
lean_dec(v_a_5160_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v_a_5263_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5265_ = v___x_5188_;
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v___x_5188_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
v___jp_5271_:
{
lean_object* v___x_5273_; uint8_t v___x_5274_; 
v___x_5273_ = lean_unsigned_to_nat(0u);
v___x_5274_ = lean_nat_dec_eq(v_numFields_5180_, v___x_5273_);
lean_dec(v_numFields_5180_);
if (v___x_5274_ == 0)
{
lean_object* v_name_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v_a_5279_; uint8_t v___x_5280_; 
v_name_5275_ = lean_ctor_get(v_toConstantVal_5177_, 0);
lean_inc(v_name_5275_);
lean_dec_ref(v_toConstantVal_5177_);
v___x_5276_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5277_ = l_Lean_Name_str___override(v_name_5275_, v___x_5276_);
lean_inc(v___x_5277_);
v___x_5278_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5277_, v___x_5114_, v_a_5106_);
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
lean_inc(v_a_5279_);
lean_dec_ref(v___x_5278_);
v___x_5280_ = lean_unbox(v_a_5279_);
lean_dec(v_a_5279_);
if (v___x_5280_ == 0)
{
lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5284_; 
lean_dec(v_numParams_5179_);
lean_del_object(v___x_5175_);
lean_dec(v_snd_5173_);
lean_dec(v_snd_5165_);
lean_dec(v_a_5160_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v___x_5281_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5282_ = l_Lean_MessageData_ofName(v___x_5277_);
if (v_isShared_5168_ == 0)
{
lean_ctor_set_tag(v___x_5167_, 7);
lean_ctor_set(v___x_5167_, 1, v___x_5282_);
lean_ctor_set(v___x_5167_, 0, v___x_5281_);
v___x_5284_ = v___x_5167_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v___x_5281_);
lean_ctor_set(v_reuseFailAlloc_5294_, 1, v___x_5282_);
v___x_5284_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
lean_object* v___x_5285_; lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
v___x_5285_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5284_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___x_5285_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5285_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
else
{
lean_del_object(v___x_5167_);
v___y_5182_ = v___x_5273_;
v___y_5183_ = v___x_5277_;
v___y_5184_ = v_a_5103_;
v___y_5185_ = v_a_5104_;
v___y_5186_ = v_a_5105_;
v___y_5187_ = v_a_5106_;
goto v___jp_5181_;
}
}
else
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___f_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
lean_dec(v_numParams_5179_);
lean_dec_ref(v_toConstantVal_5177_);
lean_del_object(v___x_5175_);
lean_dec(v_snd_5173_);
lean_del_object(v___x_5167_);
lean_dec(v_snd_5165_);
lean_dec(v_a_5160_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v_h_5102_);
v___x_5295_ = lean_box(v___y_5272_);
v___x_5296_ = lean_box(v___x_5274_);
v___f_5297_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5297_, 0, v___x_5295_);
lean_closure_set(v___f_5297_, 1, v___x_5296_);
v___x_5298_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__18));
v___x_5299_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5298_, v_target_5101_, v___f_5297_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
return v___x_5299_;
}
}
}
}
else
{
lean_dec(v_a_5170_);
lean_del_object(v___x_5167_);
lean_dec(v_snd_5165_);
lean_dec(v_fst_5164_);
lean_dec(v_a_5160_);
lean_dec_ref(v_val_5158_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v___y_5126_ = v_a_5103_;
v___y_5127_ = v_a_5104_;
v___y_5128_ = v_a_5105_;
v___y_5129_ = v_a_5106_;
goto v___jp_5125_;
}
}
else
{
lean_object* v_a_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5378_; 
lean_del_object(v___x_5167_);
lean_dec(v_snd_5165_);
lean_dec(v_fst_5164_);
lean_dec(v_a_5160_);
lean_dec_ref(v_val_5158_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v_a_5371_ = lean_ctor_get(v___x_5169_, 0);
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5169_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5373_ = v___x_5169_;
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_a_5371_);
lean_dec(v___x_5169_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5376_; 
if (v_isShared_5374_ == 0)
{
v___x_5376_ = v___x_5373_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
return v___x_5376_;
}
}
}
}
}
else
{
lean_dec(v_a_5162_);
lean_dec(v_a_5160_);
lean_dec_ref(v_val_5158_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v___y_5126_ = v_a_5103_;
v___y_5127_ = v_a_5104_;
v___y_5128_ = v_a_5105_;
v___y_5129_ = v_a_5106_;
goto v___jp_5125_;
}
}
else
{
lean_object* v_a_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5387_; 
lean_dec(v_a_5160_);
lean_dec_ref(v_val_5158_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v_a_5380_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5382_ = v___x_5161_;
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_a_5380_);
lean_dec(v___x_5161_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5385_; 
if (v_isShared_5383_ == 0)
{
v___x_5385_ = v___x_5382_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_a_5380_);
v___x_5385_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
return v___x_5385_;
}
}
}
}
else
{
lean_object* v_a_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5395_; 
lean_dec_ref(v_val_5158_);
lean_dec(v_us_5152_);
lean_dec(v_a_5139_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v_a_5388_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5390_ = v___x_5159_;
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_a_5388_);
lean_dec(v___x_5159_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5393_; 
if (v_isShared_5391_ == 0)
{
v___x_5393_ = v___x_5390_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_a_5388_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
else
{
lean_dec(v_val_5157_);
lean_dec(v_us_5152_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v___y_5141_ = v_a_5103_;
v___y_5142_ = v_a_5104_;
v___y_5143_ = v_a_5105_;
v___y_5144_ = v_a_5106_;
goto v___jp_5140_;
}
}
}
else
{
lean_dec_ref(v___x_5150_);
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
v___y_5141_ = v_a_5103_;
v___y_5142_ = v_a_5104_;
v___y_5143_ = v_a_5105_;
v___y_5144_ = v_a_5106_;
goto v___jp_5140_;
}
v___jp_5140_:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5145_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5146_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5147_ = l_Lean_indentExpr(v_a_5139_);
v___x_5148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5148_, 0, v___x_5146_);
lean_ctor_set(v___x_5148_, 1, v___x_5147_);
v___x_5149_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5145_, v___x_5148_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
return v___x_5149_;
}
}
else
{
lean_dec_ref(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
return v___x_5138_;
}
v___jp_5125_:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5130_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__6, &l_Lean_Meta_mkNoConfusion___closed__6_once, _init_l_Lean_Meta_mkNoConfusion___closed__6);
v___x_5131_ = l_Lean_MessageData_ofExpr(v___x_5123_);
v___x_5132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5132_, 0, v___x_5130_);
lean_ctor_set(v___x_5132_, 1, v___x_5131_);
v___x_5133_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__8, &l_Lean_Meta_mkNoConfusion___closed__8_once, _init_l_Lean_Meta_mkNoConfusion___closed__8);
v___x_5134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5134_, 0, v___x_5132_);
lean_ctor_set(v___x_5134_, 1, v___x_5133_);
v___x_5135_ = l_Lean_MessageData_ofExpr(v___x_5124_);
v___x_5136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5136_, 0, v___x_5134_);
lean_ctor_set(v___x_5136_, 1, v___x_5135_);
v___x_5137_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5136_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
return v___x_5137_;
}
}
}
else
{
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
return v___x_5110_;
}
}
else
{
lean_dec_ref(v_h_5102_);
lean_dec_ref(v_target_5101_);
return v___x_5108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5396_, lean_object* v_h_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l_Lean_Meta_mkNoConfusion(v_target_5396_, v_h_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_);
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5404_, lean_object* v_b_5405_, lean_object* v_i_5406_, lean_object* v_hs_5407_, lean_object* v_hl_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_){
_start:
{
lean_object* v___x_5414_; 
v___x_5414_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5404_, v_b_5405_, v_i_5406_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5415_, lean_object* v_b_5416_, lean_object* v_i_5417_, lean_object* v_hs_5418_, lean_object* v_hl_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5415_, v_b_5416_, v_i_5417_, v_hs_5418_, v_hl_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec_ref(v_range_5415_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5426_, lean_object* v_name_5427_, uint8_t v_bi_5428_, lean_object* v_type_5429_, lean_object* v_k_5430_, uint8_t v_kind_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
lean_object* v___x_5437_; 
v___x_5437_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5427_, v_bi_5428_, v_type_5429_, v_k_5430_, v_kind_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
return v___x_5437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5438_, lean_object* v_name_5439_, lean_object* v_bi_5440_, lean_object* v_type_5441_, lean_object* v_k_5442_, lean_object* v_kind_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_){
_start:
{
uint8_t v_bi_boxed_5449_; uint8_t v_kind_boxed_5450_; lean_object* v_res_5451_; 
v_bi_boxed_5449_ = lean_unbox(v_bi_5440_);
v_kind_boxed_5450_ = lean_unbox(v_kind_5443_);
v_res_5451_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5438_, v_name_5439_, v_bi_boxed_5449_, v_type_5441_, v_k_5442_, v_kind_boxed_5450_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
lean_dec(v___y_5447_);
lean_dec_ref(v___y_5446_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5452_, lean_object* v_name_5453_, lean_object* v_type_5454_, lean_object* v_k_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v___x_5461_; 
v___x_5461_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5453_, v_type_5454_, v_k_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5462_, lean_object* v_name_5463_, lean_object* v_type_5464_, lean_object* v_k_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_){
_start:
{
lean_object* v_res_5471_; 
v_res_5471_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5462_, v_name_5463_, v_type_5464_, v_k_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
return v_res_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5477_, lean_object* v_e_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_){
_start:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; 
v___x_5484_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5485_, 0, v_monad_5477_);
v___x_5486_ = lean_box(0);
v___x_5487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5487_, 0, v_e_5478_);
v___x_5488_ = lean_unsigned_to_nat(4u);
v___x_5489_ = lean_mk_empty_array_with_capacity(v___x_5488_);
v___x_5490_ = lean_array_push(v___x_5489_, v___x_5485_);
v___x_5491_ = lean_array_push(v___x_5490_, v___x_5486_);
v___x_5492_ = lean_array_push(v___x_5491_, v___x_5486_);
v___x_5493_ = lean_array_push(v___x_5492_, v___x_5487_);
v___x_5494_ = l_Lean_Meta_mkAppOptM(v___x_5484_, v___x_5493_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_);
return v___x_5494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5495_, lean_object* v_e_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_){
_start:
{
lean_object* v_res_5502_; 
v_res_5502_ = l_Lean_Meta_mkPure(v_monad_5495_, v_e_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
return v_res_5502_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5512_; lean_object* v___x_5513_; 
v___x_5512_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5513_ = l_Lean_MessageData_ofFormat(v___x_5512_);
return v___x_5513_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; 
v___x_5517_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5518_ = l_Lean_MessageData_ofFormat(v___x_5517_);
return v___x_5518_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5522_; lean_object* v___x_5523_; 
v___x_5522_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5523_ = l_Lean_MessageData_ofFormat(v___x_5522_);
return v___x_5523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5524_, lean_object* v_fieldName_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_){
_start:
{
lean_object* v___x_5531_; 
lean_inc(v_a_5529_);
lean_inc_ref(v_a_5528_);
lean_inc(v_a_5527_);
lean_inc_ref(v_a_5526_);
lean_inc_ref(v_s_5524_);
v___x_5531_ = lean_infer_type(v_s_5524_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5628_; 
v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5534_ = v___x_5531_;
v_isShared_5535_ = v_isSharedCheck_5628_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5531_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5628_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5536_; 
lean_inc(v_a_5529_);
lean_inc_ref(v_a_5528_);
lean_inc(v_a_5527_);
lean_inc_ref(v_a_5526_);
v___x_5536_ = lean_whnf(v_a_5532_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5627_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5627_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5539_ = v___x_5536_;
v_isShared_5540_ = v_isSharedCheck_5627_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v___x_5536_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5627_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___x_5560_; 
v___x_5560_ = l_Lean_Expr_getAppFn(v_a_5537_);
if (lean_obj_tag(v___x_5560_) == 4)
{
lean_object* v_declName_5561_; lean_object* v_us_5562_; lean_object* v___x_5563_; lean_object* v_env_5564_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5569_; uint8_t v___x_5608_; 
v_declName_5561_ = lean_ctor_get(v___x_5560_, 0);
lean_inc_n(v_declName_5561_, 2);
v_us_5562_ = lean_ctor_get(v___x_5560_, 1);
lean_inc(v_us_5562_);
lean_dec_ref_known(v___x_5560_, 2);
v___x_5563_ = lean_st_ref_get(v_a_5529_);
v_env_5564_ = lean_ctor_get(v___x_5563_, 0);
lean_inc_ref_n(v_env_5564_, 2);
lean_dec(v___x_5563_);
v___x_5608_ = l_Lean_isStructure(v_env_5564_, v_declName_5561_);
if (v___x_5608_ == 0)
{
lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5609_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5610_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5537_);
lean_inc_ref(v_s_5524_);
v___x_5611_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5524_, v_a_5537_);
v___x_5612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5610_);
lean_ctor_set(v___x_5612_, 1, v___x_5611_);
v___x_5613_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5609_, v___x_5612_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_dec_ref_known(v___x_5613_, 1);
v___y_5566_ = v_a_5526_;
v___y_5567_ = v_a_5527_;
v___y_5568_ = v_a_5528_;
v___y_5569_ = v_a_5529_;
goto v___jp_5565_;
}
else
{
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5621_; 
lean_dec_ref(v_env_5564_);
lean_dec(v_us_5562_);
lean_dec(v_declName_5561_);
lean_del_object(v___x_5539_);
lean_dec(v_a_5537_);
lean_del_object(v___x_5534_);
lean_dec(v_fieldName_5525_);
lean_dec_ref(v_s_5524_);
v_a_5614_ = lean_ctor_get(v___x_5613_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5616_ = v___x_5613_;
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5613_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v___x_5619_; 
if (v_isShared_5617_ == 0)
{
v___x_5619_ = v___x_5616_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
}
else
{
v___y_5566_ = v_a_5526_;
v___y_5567_ = v_a_5527_;
v___y_5568_ = v_a_5528_;
v___y_5569_ = v_a_5529_;
goto v___jp_5565_;
}
v___jp_5565_:
{
lean_object* v___x_5570_; 
lean_inc(v_fieldName_5525_);
lean_inc(v_declName_5561_);
lean_inc_ref(v_env_5564_);
v___x_5570_ = l_Lean_getProjFnForField_x3f(v_env_5564_, v_declName_5561_, v_fieldName_5525_);
if (lean_obj_tag(v___x_5570_) == 0)
{
lean_object* v___x_5571_; lean_object* v___x_5572_; size_t v_sz_5573_; size_t v___x_5574_; lean_object* v___x_5575_; 
lean_dec(v_us_5562_);
lean_del_object(v___x_5539_);
lean_inc(v_declName_5561_);
lean_inc_ref(v_env_5564_);
v___x_5571_ = l_Lean_getStructureFields(v_env_5564_, v_declName_5561_);
v___x_5572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5573_ = lean_array_size(v___x_5571_);
v___x_5574_ = ((size_t)0ULL);
lean_inc(v_fieldName_5525_);
lean_inc_ref(v_s_5524_);
v___x_5575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5564_, v_declName_5561_, v_s_5524_, v_fieldName_5525_, v___x_5571_, v_sz_5573_, v___x_5574_, v___x_5572_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_);
lean_dec_ref(v___x_5571_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v_a_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5586_; 
v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5578_ = v___x_5575_;
v_isShared_5579_ = v_isSharedCheck_5586_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_a_5576_);
lean_dec(v___x_5575_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5586_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v_fst_5580_; 
v_fst_5580_ = lean_ctor_get(v_a_5576_, 0);
lean_inc(v_fst_5580_);
lean_dec(v_a_5576_);
if (lean_obj_tag(v_fst_5580_) == 0)
{
lean_del_object(v___x_5578_);
v___y_5542_ = v___y_5568_;
v___y_5543_ = v___y_5566_;
v___y_5544_ = v___y_5569_;
v___y_5545_ = v___y_5567_;
goto v___jp_5541_;
}
else
{
lean_object* v_val_5581_; 
v_val_5581_ = lean_ctor_get(v_fst_5580_, 0);
lean_inc(v_val_5581_);
lean_dec_ref_known(v_fst_5580_, 1);
if (lean_obj_tag(v_val_5581_) == 0)
{
lean_del_object(v___x_5578_);
v___y_5542_ = v___y_5568_;
v___y_5543_ = v___y_5566_;
v___y_5544_ = v___y_5569_;
v___y_5545_ = v___y_5567_;
goto v___jp_5541_;
}
else
{
lean_object* v_val_5582_; lean_object* v___x_5584_; 
lean_dec(v_a_5537_);
lean_del_object(v___x_5534_);
lean_dec(v_fieldName_5525_);
lean_dec_ref(v_s_5524_);
v_val_5582_ = lean_ctor_get(v_val_5581_, 0);
lean_inc(v_val_5582_);
lean_dec_ref_known(v_val_5581_, 1);
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 0, v_val_5582_);
v___x_5584_ = v___x_5578_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_val_5582_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
lean_dec(v_a_5537_);
lean_del_object(v___x_5534_);
lean_dec(v_fieldName_5525_);
lean_dec_ref(v_s_5524_);
v_a_5587_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___x_5575_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v___x_5575_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5592_; 
if (v_isShared_5590_ == 0)
{
v___x_5592_ = v___x_5589_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
return v___x_5592_;
}
}
}
}
else
{
lean_object* v_val_5595_; lean_object* v_dummy_5596_; lean_object* v_nargs_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5606_; 
lean_dec_ref(v_env_5564_);
lean_dec(v_declName_5561_);
lean_del_object(v___x_5534_);
lean_dec(v_fieldName_5525_);
v_val_5595_ = lean_ctor_get(v___x_5570_, 0);
lean_inc(v_val_5595_);
lean_dec_ref_known(v___x_5570_, 1);
v_dummy_5596_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5597_ = l_Lean_Expr_getAppNumArgs(v_a_5537_);
lean_inc(v_nargs_5597_);
v___x_5598_ = lean_mk_array(v_nargs_5597_, v_dummy_5596_);
v___x_5599_ = lean_unsigned_to_nat(1u);
v___x_5600_ = lean_nat_sub(v_nargs_5597_, v___x_5599_);
lean_dec(v_nargs_5597_);
v___x_5601_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5537_, v___x_5598_, v___x_5600_);
v___x_5602_ = l_Lean_mkConst(v_val_5595_, v_us_5562_);
v___x_5603_ = l_Lean_mkAppN(v___x_5602_, v___x_5601_);
lean_dec_ref(v___x_5601_);
v___x_5604_ = l_Lean_Expr_app___override(v___x_5603_, v_s_5524_);
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 0, v___x_5604_);
v___x_5606_ = v___x_5539_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v___x_5604_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
return v___x_5606_;
}
}
}
}
else
{
lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; 
lean_dec_ref(v___x_5560_);
lean_del_object(v___x_5539_);
lean_del_object(v___x_5534_);
lean_dec(v_fieldName_5525_);
v___x_5622_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5623_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5624_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5524_, v_a_5537_);
v___x_5625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5623_);
lean_ctor_set(v___x_5625_, 1, v___x_5624_);
v___x_5626_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5622_, v___x_5625_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_);
return v___x_5626_;
}
v___jp_5541_:
{
lean_object* v___x_5546_; lean_object* v___x_5547_; uint8_t v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5551_; 
v___x_5546_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5547_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5548_ = 1;
v___x_5549_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5525_, v___x_5548_);
if (v_isShared_5535_ == 0)
{
lean_ctor_set_tag(v___x_5534_, 3);
lean_ctor_set(v___x_5534_, 0, v___x_5549_);
v___x_5551_ = v___x_5534_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5549_);
v___x_5551_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5552_ = l_Lean_MessageData_ofFormat(v___x_5551_);
v___x_5553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5553_, 0, v___x_5547_);
lean_ctor_set(v___x_5553_, 1, v___x_5552_);
v___x_5554_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5553_);
lean_ctor_set(v___x_5555_, 1, v___x_5554_);
v___x_5556_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5524_, v_a_5537_);
v___x_5557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5555_);
lean_ctor_set(v___x_5557_, 1, v___x_5556_);
v___x_5558_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5546_, v___x_5557_, v___y_5543_, v___y_5545_, v___y_5542_, v___y_5544_);
return v___x_5558_;
}
}
}
}
else
{
lean_del_object(v___x_5534_);
lean_dec(v_fieldName_5525_);
lean_dec_ref(v_s_5524_);
return v___x_5536_;
}
}
}
else
{
lean_dec(v_fieldName_5525_);
lean_dec_ref(v_s_5524_);
return v___x_5531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5629_, lean_object* v_declName_5630_, lean_object* v_s_5631_, lean_object* v_fieldName_5632_, lean_object* v_as_5633_, size_t v_sz_5634_, size_t v_i_5635_, lean_object* v_b_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_){
_start:
{
lean_object* v_a_5643_; uint8_t v___x_5647_; 
v___x_5647_ = lean_usize_dec_lt(v_i_5635_, v_sz_5634_);
if (v___x_5647_ == 0)
{
lean_object* v___x_5648_; 
lean_dec(v_fieldName_5632_);
lean_dec_ref(v_s_5631_);
lean_dec(v_declName_5630_);
lean_dec_ref(v___x_5629_);
v___x_5648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5648_, 0, v_b_5636_);
return v___x_5648_;
}
else
{
lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v_a_5651_; lean_object* v___x_5652_; 
lean_dec_ref(v_b_5636_);
v___x_5649_ = lean_box(0);
v___x_5650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5651_ = lean_array_uget_borrowed(v_as_5633_, v_i_5635_);
lean_inc(v_a_5651_);
lean_inc(v_declName_5630_);
lean_inc_ref(v___x_5629_);
v___x_5652_ = l_Lean_isSubobjectField_x3f(v___x_5629_, v_declName_5630_, v_a_5651_);
if (lean_obj_tag(v___x_5652_) == 0)
{
v_a_5643_ = v___x_5650_;
goto v___jp_5642_;
}
else
{
lean_object* v___x_5654_; uint8_t v_isShared_5655_; uint8_t v_isSharedCheck_5711_; 
v_isSharedCheck_5711_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5711_ == 0)
{
lean_object* v_unused_5712_; 
v_unused_5712_ = lean_ctor_get(v___x_5652_, 0);
lean_dec(v_unused_5712_);
v___x_5654_ = v___x_5652_;
v_isShared_5655_ = v_isSharedCheck_5711_;
goto v_resetjp_5653_;
}
else
{
lean_dec(v___x_5652_);
v___x_5654_ = lean_box(0);
v_isShared_5655_ = v_isSharedCheck_5711_;
goto v_resetjp_5653_;
}
v_resetjp_5653_:
{
lean_object* v___x_5656_; 
lean_inc(v_a_5651_);
lean_inc_ref(v_s_5631_);
v___x_5656_ = l_Lean_Meta_mkProjection(v_s_5631_, v_a_5651_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; lean_object* v___x_5658_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref_known(v___x_5656_, 1);
v___x_5658_ = l_Lean_Meta_saveState___redArg(v___y_5638_, v___y_5640_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; lean_object* v___x_5660_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
lean_inc(v_a_5659_);
lean_dec_ref_known(v___x_5658_, 1);
lean_inc(v_fieldName_5632_);
v___x_5660_ = l_Lean_Meta_mkProjection(v_a_5657_, v_fieldName_5632_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
if (lean_obj_tag(v___x_5660_) == 0)
{
lean_object* v_a_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5673_; 
lean_dec(v_a_5659_);
lean_dec(v_fieldName_5632_);
lean_dec_ref(v_s_5631_);
lean_dec(v_declName_5630_);
lean_dec_ref(v___x_5629_);
v_a_5661_ = lean_ctor_get(v___x_5660_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5663_ = v___x_5660_;
v_isShared_5664_ = v_isSharedCheck_5673_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_a_5661_);
lean_dec(v___x_5660_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5673_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5666_; 
if (v_isShared_5655_ == 0)
{
lean_ctor_set(v___x_5654_, 0, v_a_5661_);
v___x_5666_ = v___x_5654_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5661_);
v___x_5666_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5670_; 
v___x_5667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5666_);
v___x_5668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set(v___x_5668_, 1, v___x_5649_);
if (v_isShared_5664_ == 0)
{
lean_ctor_set(v___x_5663_, 0, v___x_5668_);
v___x_5670_ = v___x_5663_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v___x_5668_);
v___x_5670_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
return v___x_5670_;
}
}
}
}
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5694_; 
lean_del_object(v___x_5654_);
v_a_5674_ = lean_ctor_get(v___x_5660_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5694_ == 0)
{
v___x_5676_ = v___x_5660_;
v_isShared_5677_ = v_isSharedCheck_5694_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5660_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5694_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
uint8_t v___y_5679_; uint8_t v___x_5692_; 
v___x_5692_ = l_Lean_Exception_isInterrupt(v_a_5674_);
if (v___x_5692_ == 0)
{
uint8_t v___x_5693_; 
lean_inc(v_a_5674_);
v___x_5693_ = l_Lean_Exception_isRuntime(v_a_5674_);
v___y_5679_ = v___x_5693_;
goto v___jp_5678_;
}
else
{
v___y_5679_ = v___x_5692_;
goto v___jp_5678_;
}
v___jp_5678_:
{
if (v___y_5679_ == 0)
{
lean_object* v___x_5680_; 
lean_del_object(v___x_5676_);
lean_dec(v_a_5674_);
v___x_5680_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5659_, v___y_5638_, v___y_5640_);
if (lean_obj_tag(v___x_5680_) == 0)
{
lean_dec_ref_known(v___x_5680_, 1);
v_a_5643_ = v___x_5650_;
goto v___jp_5642_;
}
else
{
lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
lean_dec(v_fieldName_5632_);
lean_dec_ref(v_s_5631_);
lean_dec(v_declName_5630_);
lean_dec_ref(v___x_5629_);
v_a_5681_ = lean_ctor_get(v___x_5680_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5680_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5680_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_dec(v___x_5680_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
else
{
lean_object* v___x_5690_; 
lean_dec(v_a_5659_);
lean_dec(v_fieldName_5632_);
lean_dec_ref(v_s_5631_);
lean_dec(v_declName_5630_);
lean_dec_ref(v___x_5629_);
if (v_isShared_5677_ == 0)
{
v___x_5690_ = v___x_5676_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_a_5674_);
v___x_5690_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
return v___x_5690_;
}
}
}
}
}
}
else
{
lean_object* v_a_5695_; lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5702_; 
lean_dec(v_a_5657_);
lean_del_object(v___x_5654_);
lean_dec(v_fieldName_5632_);
lean_dec_ref(v_s_5631_);
lean_dec(v_declName_5630_);
lean_dec_ref(v___x_5629_);
v_a_5695_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5697_ = v___x_5658_;
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
else
{
lean_inc(v_a_5695_);
lean_dec(v___x_5658_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5700_; 
if (v_isShared_5698_ == 0)
{
v___x_5700_ = v___x_5697_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_a_5695_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
}
else
{
lean_object* v_a_5703_; lean_object* v___x_5705_; uint8_t v_isShared_5706_; uint8_t v_isSharedCheck_5710_; 
lean_del_object(v___x_5654_);
lean_dec(v_fieldName_5632_);
lean_dec_ref(v_s_5631_);
lean_dec(v_declName_5630_);
lean_dec_ref(v___x_5629_);
v_a_5703_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5710_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5710_ == 0)
{
v___x_5705_ = v___x_5656_;
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
else
{
lean_inc(v_a_5703_);
lean_dec(v___x_5656_);
v___x_5705_ = lean_box(0);
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
v_resetjp_5704_:
{
lean_object* v___x_5708_; 
if (v_isShared_5706_ == 0)
{
v___x_5708_ = v___x_5705_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v_a_5703_);
v___x_5708_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
return v___x_5708_;
}
}
}
}
}
}
v___jp_5642_:
{
size_t v___x_5644_; size_t v___x_5645_; 
v___x_5644_ = ((size_t)1ULL);
v___x_5645_ = lean_usize_add(v_i_5635_, v___x_5644_);
lean_inc_ref(v_a_5643_);
v_i_5635_ = v___x_5645_;
v_b_5636_ = v_a_5643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5713_, lean_object* v_declName_5714_, lean_object* v_s_5715_, lean_object* v_fieldName_5716_, lean_object* v_as_5717_, lean_object* v_sz_5718_, lean_object* v_i_5719_, lean_object* v_b_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
size_t v_sz_boxed_5726_; size_t v_i_boxed_5727_; lean_object* v_res_5728_; 
v_sz_boxed_5726_ = lean_unbox_usize(v_sz_5718_);
lean_dec(v_sz_5718_);
v_i_boxed_5727_ = lean_unbox_usize(v_i_5719_);
lean_dec(v_i_5719_);
v_res_5728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5713_, v_declName_5714_, v_s_5715_, v_fieldName_5716_, v_as_5717_, v_sz_boxed_5726_, v_i_boxed_5727_, v_b_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec_ref(v_as_5717_);
return v_res_5728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5729_, lean_object* v_fieldName_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_){
_start:
{
lean_object* v_res_5736_; 
v_res_5736_ = l_Lean_Meta_mkProjection(v_s_5729_, v_fieldName_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_);
lean_dec(v_a_5734_);
lean_dec_ref(v_a_5733_);
lean_dec(v_a_5732_);
lean_dec_ref(v_a_5731_);
return v_res_5736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5737_, lean_object* v_cons_5738_, lean_object* v_x_5739_){
_start:
{
if (lean_obj_tag(v_x_5739_) == 0)
{
lean_dec_ref(v_cons_5738_);
lean_inc_ref(v_nil_5737_);
return v_nil_5737_;
}
else
{
lean_object* v_head_5740_; lean_object* v_tail_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; 
v_head_5740_ = lean_ctor_get(v_x_5739_, 0);
lean_inc(v_head_5740_);
v_tail_5741_ = lean_ctor_get(v_x_5739_, 1);
lean_inc(v_tail_5741_);
lean_dec_ref_known(v_x_5739_, 2);
lean_inc_ref(v_cons_5738_);
v___x_5742_ = l_Lean_Expr_app___override(v_cons_5738_, v_head_5740_);
v___x_5743_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5737_, v_cons_5738_, v_tail_5741_);
v___x_5744_ = l_Lean_Expr_app___override(v___x_5742_, v___x_5743_);
return v___x_5744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5745_, lean_object* v_cons_5746_, lean_object* v_x_5747_){
_start:
{
lean_object* v_res_5748_; 
v_res_5748_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5745_, v_cons_5746_, v_x_5747_);
lean_dec_ref(v_nil_5745_);
return v_res_5748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5758_, lean_object* v_xs_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_){
_start:
{
lean_object* v___x_5765_; 
lean_inc_ref(v_type_5758_);
v___x_5765_ = l_Lean_Meta_getDecLevel(v_type_5758_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_a_5766_; lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5785_; 
v_a_5766_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5785_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5785_ == 0)
{
v___x_5768_ = v___x_5765_;
v_isShared_5769_ = v_isSharedCheck_5785_;
goto v_resetjp_5767_;
}
else
{
lean_inc(v_a_5766_);
lean_dec(v___x_5765_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5785_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; 
v___x_5770_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5771_ = lean_box(0);
v___x_5772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5772_, 0, v_a_5766_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
lean_inc_ref(v___x_5772_);
v___x_5773_ = l_Lean_mkConst(v___x_5770_, v___x_5772_);
lean_inc_ref(v_type_5758_);
v___x_5774_ = l_Lean_Expr_app___override(v___x_5773_, v_type_5758_);
if (lean_obj_tag(v_xs_5759_) == 0)
{
lean_object* v___x_5776_; 
lean_dec_ref_known(v___x_5772_, 2);
lean_dec_ref(v_type_5758_);
if (v_isShared_5769_ == 0)
{
lean_ctor_set(v___x_5768_, 0, v___x_5774_);
v___x_5776_ = v___x_5768_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v___x_5774_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
else
{
lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5783_; 
v___x_5778_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5779_ = l_Lean_mkConst(v___x_5778_, v___x_5772_);
v___x_5780_ = l_Lean_Expr_app___override(v___x_5779_, v_type_5758_);
v___x_5781_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5774_, v___x_5780_, v_xs_5759_);
lean_dec_ref(v___x_5774_);
if (v_isShared_5769_ == 0)
{
lean_ctor_set(v___x_5768_, 0, v___x_5781_);
v___x_5783_ = v___x_5768_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5781_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5793_; 
lean_dec(v_xs_5759_);
lean_dec_ref(v_type_5758_);
v_a_5786_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5793_ == 0)
{
v___x_5788_ = v___x_5765_;
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
else
{
lean_inc(v_a_5786_);
lean_dec(v___x_5765_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5791_; 
if (v_isShared_5789_ == 0)
{
v___x_5791_ = v___x_5788_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_a_5786_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5794_, lean_object* v_xs_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_){
_start:
{
lean_object* v_res_5801_; 
v_res_5801_ = l_Lean_Meta_mkListLit(v_type_5794_, v_xs_5795_, v_a_5796_, v_a_5797_, v_a_5798_, v_a_5799_);
lean_dec(v_a_5799_);
lean_dec_ref(v_a_5798_);
lean_dec(v_a_5797_);
lean_dec_ref(v_a_5796_);
return v_res_5801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5806_, lean_object* v_xs_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_){
_start:
{
lean_object* v___x_5813_; 
lean_inc_ref(v_type_5806_);
v___x_5813_ = l_Lean_Meta_getDecLevel(v_type_5806_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; lean_object* v___x_5815_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_a_5814_);
lean_dec_ref_known(v___x_5813_, 1);
lean_inc_ref(v_type_5806_);
v___x_5815_ = l_Lean_Meta_mkListLit(v_type_5806_, v_xs_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_);
if (lean_obj_tag(v___x_5815_) == 0)
{
lean_object* v_a_5816_; lean_object* v___x_5818_; uint8_t v_isShared_5819_; uint8_t v_isSharedCheck_5829_; 
v_a_5816_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5829_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5829_ == 0)
{
v___x_5818_ = v___x_5815_;
v_isShared_5819_ = v_isSharedCheck_5829_;
goto v_resetjp_5817_;
}
else
{
lean_inc(v_a_5816_);
lean_dec(v___x_5815_);
v___x_5818_ = lean_box(0);
v_isShared_5819_ = v_isSharedCheck_5829_;
goto v_resetjp_5817_;
}
v_resetjp_5817_:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5827_; 
v___x_5820_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5821_ = lean_box(0);
v___x_5822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5822_, 0, v_a_5814_);
lean_ctor_set(v___x_5822_, 1, v___x_5821_);
v___x_5823_ = l_Lean_mkConst(v___x_5820_, v___x_5822_);
v___x_5824_ = l_Lean_Expr_app___override(v___x_5823_, v_type_5806_);
v___x_5825_ = l_Lean_Expr_app___override(v___x_5824_, v_a_5816_);
if (v_isShared_5819_ == 0)
{
lean_ctor_set(v___x_5818_, 0, v___x_5825_);
v___x_5827_ = v___x_5818_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5825_);
v___x_5827_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5826_;
}
v_reusejp_5826_:
{
return v___x_5827_;
}
}
}
else
{
lean_dec(v_a_5814_);
lean_dec_ref(v_type_5806_);
return v___x_5815_;
}
}
else
{
lean_object* v_a_5830_; lean_object* v___x_5832_; uint8_t v_isShared_5833_; uint8_t v_isSharedCheck_5837_; 
lean_dec(v_xs_5807_);
lean_dec_ref(v_type_5806_);
v_a_5830_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5837_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5837_ == 0)
{
v___x_5832_ = v___x_5813_;
v_isShared_5833_ = v_isSharedCheck_5837_;
goto v_resetjp_5831_;
}
else
{
lean_inc(v_a_5830_);
lean_dec(v___x_5813_);
v___x_5832_ = lean_box(0);
v_isShared_5833_ = v_isSharedCheck_5837_;
goto v_resetjp_5831_;
}
v_resetjp_5831_:
{
lean_object* v___x_5835_; 
if (v_isShared_5833_ == 0)
{
v___x_5835_ = v___x_5832_;
goto v_reusejp_5834_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5830_);
v___x_5835_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5834_;
}
v_reusejp_5834_:
{
return v___x_5835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5838_, lean_object* v_xs_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_){
_start:
{
lean_object* v_res_5845_; 
v_res_5845_ = l_Lean_Meta_mkArrayLit(v_type_5838_, v_xs_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_);
lean_dec(v_a_5843_);
lean_dec_ref(v_a_5842_);
lean_dec(v_a_5841_);
lean_dec_ref(v_a_5840_);
return v_res_5845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_){
_start:
{
lean_object* v___x_5857_; 
lean_inc_ref(v_type_5851_);
v___x_5857_ = l_Lean_Meta_getDecLevel(v_type_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_);
if (lean_obj_tag(v___x_5857_) == 0)
{
lean_object* v_a_5858_; lean_object* v___x_5860_; uint8_t v_isShared_5861_; uint8_t v_isSharedCheck_5870_; 
v_a_5858_ = lean_ctor_get(v___x_5857_, 0);
v_isSharedCheck_5870_ = !lean_is_exclusive(v___x_5857_);
if (v_isSharedCheck_5870_ == 0)
{
v___x_5860_ = v___x_5857_;
v_isShared_5861_ = v_isSharedCheck_5870_;
goto v_resetjp_5859_;
}
else
{
lean_inc(v_a_5858_);
lean_dec(v___x_5857_);
v___x_5860_ = lean_box(0);
v_isShared_5861_ = v_isSharedCheck_5870_;
goto v_resetjp_5859_;
}
v_resetjp_5859_:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5868_; 
v___x_5862_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5863_ = lean_box(0);
v___x_5864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5864_, 0, v_a_5858_);
lean_ctor_set(v___x_5864_, 1, v___x_5863_);
v___x_5865_ = l_Lean_mkConst(v___x_5862_, v___x_5864_);
v___x_5866_ = l_Lean_Expr_app___override(v___x_5865_, v_type_5851_);
if (v_isShared_5861_ == 0)
{
lean_ctor_set(v___x_5860_, 0, v___x_5866_);
v___x_5868_ = v___x_5860_;
goto v_reusejp_5867_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v___x_5866_);
v___x_5868_ = v_reuseFailAlloc_5869_;
goto v_reusejp_5867_;
}
v_reusejp_5867_:
{
return v___x_5868_;
}
}
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_dec_ref(v_type_5851_);
v_a_5871_ = lean_ctor_get(v___x_5857_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5857_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5857_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5857_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_){
_start:
{
lean_object* v_res_5885_; 
v_res_5885_ = l_Lean_Meta_mkNone(v_type_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_);
lean_dec(v_a_5883_);
lean_dec_ref(v_a_5882_);
lean_dec(v_a_5881_);
lean_dec_ref(v_a_5880_);
return v_res_5885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5890_, lean_object* v_value_5891_, lean_object* v_a_5892_, lean_object* v_a_5893_, lean_object* v_a_5894_, lean_object* v_a_5895_){
_start:
{
lean_object* v___x_5897_; 
lean_inc_ref(v_type_5890_);
v___x_5897_ = l_Lean_Meta_getDecLevel(v_type_5890_, v_a_5892_, v_a_5893_, v_a_5894_, v_a_5895_);
if (lean_obj_tag(v___x_5897_) == 0)
{
lean_object* v_a_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5910_; 
v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
v_isSharedCheck_5910_ = !lean_is_exclusive(v___x_5897_);
if (v_isSharedCheck_5910_ == 0)
{
v___x_5900_ = v___x_5897_;
v_isShared_5901_ = v_isSharedCheck_5910_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_a_5898_);
lean_dec(v___x_5897_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5910_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5908_; 
v___x_5902_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5903_ = lean_box(0);
v___x_5904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5904_, 0, v_a_5898_);
lean_ctor_set(v___x_5904_, 1, v___x_5903_);
v___x_5905_ = l_Lean_mkConst(v___x_5902_, v___x_5904_);
v___x_5906_ = l_Lean_mkAppB(v___x_5905_, v_type_5890_, v_value_5891_);
if (v_isShared_5901_ == 0)
{
lean_ctor_set(v___x_5900_, 0, v___x_5906_);
v___x_5908_ = v___x_5900_;
goto v_reusejp_5907_;
}
else
{
lean_object* v_reuseFailAlloc_5909_; 
v_reuseFailAlloc_5909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5909_, 0, v___x_5906_);
v___x_5908_ = v_reuseFailAlloc_5909_;
goto v_reusejp_5907_;
}
v_reusejp_5907_:
{
return v___x_5908_;
}
}
}
else
{
lean_object* v_a_5911_; lean_object* v___x_5913_; uint8_t v_isShared_5914_; uint8_t v_isSharedCheck_5918_; 
lean_dec_ref(v_value_5891_);
lean_dec_ref(v_type_5890_);
v_a_5911_ = lean_ctor_get(v___x_5897_, 0);
v_isSharedCheck_5918_ = !lean_is_exclusive(v___x_5897_);
if (v_isSharedCheck_5918_ == 0)
{
v___x_5913_ = v___x_5897_;
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
else
{
lean_inc(v_a_5911_);
lean_dec(v___x_5897_);
v___x_5913_ = lean_box(0);
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
v_resetjp_5912_:
{
lean_object* v___x_5916_; 
if (v_isShared_5914_ == 0)
{
v___x_5916_ = v___x_5913_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5917_; 
v_reuseFailAlloc_5917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_a_5911_);
v___x_5916_ = v_reuseFailAlloc_5917_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
return v___x_5916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5919_, lean_object* v_value_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_){
_start:
{
lean_object* v_res_5926_; 
v_res_5926_ = l_Lean_Meta_mkSome(v_type_5919_, v_value_5920_, v_a_5921_, v_a_5922_, v_a_5923_, v_a_5924_);
lean_dec(v_a_5924_);
lean_dec_ref(v_a_5923_);
lean_dec(v_a_5922_);
lean_dec_ref(v_a_5921_);
return v_res_5926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_){
_start:
{
lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; 
v___x_5938_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5939_, 0, v_p_5932_);
v___x_5940_ = lean_box(0);
v___x_5941_ = lean_unsigned_to_nat(2u);
v___x_5942_ = lean_mk_empty_array_with_capacity(v___x_5941_);
v___x_5943_ = lean_array_push(v___x_5942_, v___x_5939_);
v___x_5944_ = lean_array_push(v___x_5943_, v___x_5940_);
v___x_5945_ = l_Lean_Meta_mkAppOptM(v___x_5938_, v___x_5944_, v_a_5933_, v_a_5934_, v_a_5935_, v_a_5936_);
return v___x_5945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_){
_start:
{
lean_object* v_res_5952_; 
v_res_5952_ = l_Lean_Meta_mkDecide(v_p_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_);
lean_dec(v_a_5950_);
lean_dec_ref(v_a_5949_);
lean_dec(v_a_5948_);
lean_dec_ref(v_a_5947_);
return v_res_5952_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; 
v___x_5958_ = lean_box(0);
v___x_5959_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5960_ = l_Lean_mkConst(v___x_5959_, v___x_5958_);
return v___x_5960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_){
_start:
{
lean_object* v___x_5970_; 
v___x_5970_ = l_Lean_Meta_mkDecide(v_p_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_);
if (lean_obj_tag(v___x_5970_) == 0)
{
lean_object* v_a_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; 
v_a_5971_ = lean_ctor_get(v___x_5970_, 0);
lean_inc(v_a_5971_);
lean_dec_ref_known(v___x_5970_, 1);
v___x_5972_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5973_ = l_Lean_Meta_mkEq(v_a_5971_, v___x_5972_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_);
if (lean_obj_tag(v___x_5973_) == 0)
{
lean_object* v_a_5974_; lean_object* v___x_5975_; 
v_a_5974_ = lean_ctor_get(v___x_5973_, 0);
lean_inc(v_a_5974_);
lean_dec_ref_known(v___x_5973_, 1);
v___x_5975_ = l_Lean_Meta_mkEqRefl(v___x_5972_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_);
if (lean_obj_tag(v___x_5975_) == 0)
{
lean_object* v_a_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; 
v_a_5976_ = lean_ctor_get(v___x_5975_, 0);
lean_inc(v_a_5976_);
lean_dec_ref_known(v___x_5975_, 1);
v___x_5977_ = l_Lean_Meta_mkExpectedPropHint(v_a_5976_, v_a_5974_);
v___x_5978_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5979_ = lean_unsigned_to_nat(1u);
v___x_5980_ = lean_mk_empty_array_with_capacity(v___x_5979_);
v___x_5981_ = lean_array_push(v___x_5980_, v___x_5977_);
v___x_5982_ = l_Lean_Meta_mkAppM(v___x_5978_, v___x_5981_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_);
return v___x_5982_;
}
else
{
lean_dec(v_a_5974_);
return v___x_5975_;
}
}
else
{
return v___x_5973_;
}
}
else
{
return v___x_5970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_){
_start:
{
lean_object* v_res_5989_; 
v_res_5989_ = l_Lean_Meta_mkDecideProof(v_p_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_);
lean_dec(v_a_5987_);
lean_dec_ref(v_a_5986_);
lean_dec(v_a_5985_);
lean_dec_ref(v_a_5984_);
return v_res_5989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5995_, lean_object* v_b_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_){
_start:
{
lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6002_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6003_ = lean_unsigned_to_nat(2u);
v___x_6004_ = lean_mk_empty_array_with_capacity(v___x_6003_);
v___x_6005_ = lean_array_push(v___x_6004_, v_a_5995_);
v___x_6006_ = lean_array_push(v___x_6005_, v_b_5996_);
v___x_6007_ = l_Lean_Meta_mkAppM(v___x_6002_, v___x_6006_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_);
return v___x_6007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_6008_, lean_object* v_b_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_, lean_object* v_a_6014_){
_start:
{
lean_object* v_res_6015_; 
v_res_6015_ = l_Lean_Meta_mkLt(v_a_6008_, v_b_6009_, v_a_6010_, v_a_6011_, v_a_6012_, v_a_6013_);
lean_dec(v_a_6013_);
lean_dec_ref(v_a_6012_);
lean_dec(v_a_6011_);
lean_dec_ref(v_a_6010_);
return v_res_6015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_6021_, lean_object* v_b_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_){
_start:
{
lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; 
v___x_6028_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6029_ = lean_unsigned_to_nat(2u);
v___x_6030_ = lean_mk_empty_array_with_capacity(v___x_6029_);
v___x_6031_ = lean_array_push(v___x_6030_, v_a_6021_);
v___x_6032_ = lean_array_push(v___x_6031_, v_b_6022_);
v___x_6033_ = l_Lean_Meta_mkAppM(v___x_6028_, v___x_6032_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_);
return v___x_6033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_6034_, lean_object* v_b_6035_, lean_object* v_a_6036_, lean_object* v_a_6037_, lean_object* v_a_6038_, lean_object* v_a_6039_, lean_object* v_a_6040_){
_start:
{
lean_object* v_res_6041_; 
v_res_6041_ = l_Lean_Meta_mkLe(v_a_6034_, v_b_6035_, v_a_6036_, v_a_6037_, v_a_6038_, v_a_6039_);
lean_dec(v_a_6039_);
lean_dec_ref(v_a_6038_);
lean_dec(v_a_6037_);
lean_dec_ref(v_a_6036_);
return v_res_6041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_6047_, lean_object* v_a_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_){
_start:
{
lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6053_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_6054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6054_, 0, v_00_u03b1_6047_);
v___x_6055_ = lean_box(0);
v___x_6056_ = lean_unsigned_to_nat(2u);
v___x_6057_ = lean_mk_empty_array_with_capacity(v___x_6056_);
v___x_6058_ = lean_array_push(v___x_6057_, v___x_6054_);
v___x_6059_ = lean_array_push(v___x_6058_, v___x_6055_);
v___x_6060_ = l_Lean_Meta_mkAppOptM(v___x_6053_, v___x_6059_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_);
return v___x_6060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_){
_start:
{
lean_object* v_res_6067_; 
v_res_6067_ = l_Lean_Meta_mkDefault(v_00_u03b1_6061_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_);
lean_dec(v_a_6065_);
lean_dec_ref(v_a_6064_);
lean_dec(v_a_6063_);
lean_dec_ref(v_a_6062_);
return v_res_6067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_, lean_object* v_a_6077_){
_start:
{
lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
v___x_6079_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_6080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6080_, 0, v_00_u03b1_6073_);
v___x_6081_ = lean_box(0);
v___x_6082_ = lean_unsigned_to_nat(2u);
v___x_6083_ = lean_mk_empty_array_with_capacity(v___x_6082_);
v___x_6084_ = lean_array_push(v___x_6083_, v___x_6080_);
v___x_6085_ = lean_array_push(v___x_6084_, v___x_6081_);
v___x_6086_ = l_Lean_Meta_mkAppOptM(v___x_6079_, v___x_6085_, v_a_6074_, v_a_6075_, v_a_6076_, v_a_6077_);
return v___x_6086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_, lean_object* v_a_6090_, lean_object* v_a_6091_, lean_object* v_a_6092_){
_start:
{
lean_object* v_res_6093_; 
v_res_6093_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6087_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_);
lean_dec(v_a_6091_);
lean_dec_ref(v_a_6090_);
lean_dec(v_a_6089_);
lean_dec_ref(v_a_6088_);
return v_res_6093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6097_, lean_object* v_a_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_, lean_object* v_a_6101_){
_start:
{
lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___x_6103_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6104_ = lean_unsigned_to_nat(1u);
v___x_6105_ = lean_mk_empty_array_with_capacity(v___x_6104_);
v___x_6106_ = lean_array_push(v___x_6105_, v_h_6097_);
v___x_6107_ = l_Lean_Meta_mkAppM(v___x_6103_, v___x_6106_, v_a_6098_, v_a_6099_, v_a_6100_, v_a_6101_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6108_, lean_object* v_a_6109_, lean_object* v_a_6110_, lean_object* v_a_6111_, lean_object* v_a_6112_, lean_object* v_a_6113_){
_start:
{
lean_object* v_res_6114_; 
v_res_6114_ = l_Lean_Meta_mkFunExt(v_h_6108_, v_a_6109_, v_a_6110_, v_a_6111_, v_a_6112_);
lean_dec(v_a_6112_);
lean_dec_ref(v_a_6111_);
lean_dec(v_a_6110_);
lean_dec_ref(v_a_6109_);
return v_res_6114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6118_, lean_object* v_a_6119_, lean_object* v_a_6120_, lean_object* v_a_6121_, lean_object* v_a_6122_){
_start:
{
lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; 
v___x_6124_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6125_ = lean_unsigned_to_nat(1u);
v___x_6126_ = lean_mk_empty_array_with_capacity(v___x_6125_);
v___x_6127_ = lean_array_push(v___x_6126_, v_h_6118_);
v___x_6128_ = l_Lean_Meta_mkAppM(v___x_6124_, v___x_6127_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_);
return v___x_6128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6129_, lean_object* v_a_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_, lean_object* v_a_6133_, lean_object* v_a_6134_){
_start:
{
lean_object* v_res_6135_; 
v_res_6135_ = l_Lean_Meta_mkPropExt(v_h_6129_, v_a_6130_, v_a_6131_, v_a_6132_, v_a_6133_);
lean_dec(v_a_6133_);
lean_dec_ref(v_a_6132_);
lean_dec(v_a_6131_);
lean_dec_ref(v_a_6130_);
return v_res_6135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6139_, lean_object* v_h_u2082_6140_, lean_object* v_a_6141_, lean_object* v_a_6142_, lean_object* v_a_6143_, lean_object* v_a_6144_){
_start:
{
lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; 
v___x_6146_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6147_ = lean_unsigned_to_nat(2u);
v___x_6148_ = lean_mk_empty_array_with_capacity(v___x_6147_);
v___x_6149_ = lean_array_push(v___x_6148_, v_h_u2081_6139_);
v___x_6150_ = lean_array_push(v___x_6149_, v_h_u2082_6140_);
v___x_6151_ = l_Lean_Meta_mkAppM(v___x_6146_, v___x_6150_, v_a_6141_, v_a_6142_, v_a_6143_, v_a_6144_);
return v___x_6151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6152_, lean_object* v_h_u2082_6153_, lean_object* v_a_6154_, lean_object* v_a_6155_, lean_object* v_a_6156_, lean_object* v_a_6157_, lean_object* v_a_6158_){
_start:
{
lean_object* v_res_6159_; 
v_res_6159_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6152_, v_h_u2082_6153_, v_a_6154_, v_a_6155_, v_a_6156_, v_a_6157_);
lean_dec(v_a_6157_);
lean_dec_ref(v_a_6156_);
lean_dec(v_a_6155_);
lean_dec_ref(v_a_6154_);
return v_res_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6163_, lean_object* v_h_6164_, lean_object* v_a_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_, lean_object* v_a_6168_){
_start:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; 
v___x_6170_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6171_ = lean_unsigned_to_nat(2u);
v___x_6172_ = lean_mk_empty_array_with_capacity(v___x_6171_);
v___x_6173_ = lean_array_push(v___x_6172_, v_b_6163_);
v___x_6174_ = lean_array_push(v___x_6173_, v_h_6164_);
v___x_6175_ = l_Lean_Meta_mkAppM(v___x_6170_, v___x_6174_, v_a_6165_, v_a_6166_, v_a_6167_, v_a_6168_);
return v___x_6175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6176_, lean_object* v_h_6177_, lean_object* v_a_6178_, lean_object* v_a_6179_, lean_object* v_a_6180_, lean_object* v_a_6181_, lean_object* v_a_6182_){
_start:
{
lean_object* v_res_6183_; 
v_res_6183_ = l_Lean_Meta_mkLetValCongr(v_b_6176_, v_h_6177_, v_a_6178_, v_a_6179_, v_a_6180_, v_a_6181_);
lean_dec(v_a_6181_);
lean_dec_ref(v_a_6180_);
lean_dec(v_a_6179_);
lean_dec_ref(v_a_6178_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6187_, lean_object* v_h_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_, lean_object* v_a_6191_, lean_object* v_a_6192_){
_start:
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; 
v___x_6194_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6195_ = lean_unsigned_to_nat(2u);
v___x_6196_ = lean_mk_empty_array_with_capacity(v___x_6195_);
v___x_6197_ = lean_array_push(v___x_6196_, v_a_6187_);
v___x_6198_ = lean_array_push(v___x_6197_, v_h_6188_);
v___x_6199_ = l_Lean_Meta_mkAppM(v___x_6194_, v___x_6198_, v_a_6189_, v_a_6190_, v_a_6191_, v_a_6192_);
return v___x_6199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6200_, lean_object* v_h_6201_, lean_object* v_a_6202_, lean_object* v_a_6203_, lean_object* v_a_6204_, lean_object* v_a_6205_, lean_object* v_a_6206_){
_start:
{
lean_object* v_res_6207_; 
v_res_6207_ = l_Lean_Meta_mkLetBodyCongr(v_a_6200_, v_h_6201_, v_a_6202_, v_a_6203_, v_a_6204_, v_a_6205_);
lean_dec(v_a_6205_);
lean_dec_ref(v_a_6204_);
lean_dec(v_a_6203_);
lean_dec_ref(v_a_6202_);
return v_res_6207_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___x_6211_ = lean_box(0);
v___x_6212_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6213_ = l_Lean_mkConst(v___x_6212_, v___x_6211_);
return v___x_6213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6217_, lean_object* v_h_6218_){
_start:
{
lean_object* v___x_6222_; uint8_t v___x_6223_; 
lean_inc_ref(v_h_6218_);
v___x_6222_ = l_Lean_Expr_cleanupAnnotations(v_h_6218_);
v___x_6223_ = l_Lean_Expr_isApp(v___x_6222_);
if (v___x_6223_ == 0)
{
lean_dec_ref(v___x_6222_);
goto v___jp_6219_;
}
else
{
lean_object* v_arg_6224_; lean_object* v___x_6225_; uint8_t v___x_6226_; 
v_arg_6224_ = lean_ctor_get(v___x_6222_, 1);
lean_inc_ref(v_arg_6224_);
v___x_6225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6222_);
v___x_6226_ = l_Lean_Expr_isApp(v___x_6225_);
if (v___x_6226_ == 0)
{
lean_dec_ref(v___x_6225_);
lean_dec_ref(v_arg_6224_);
goto v___jp_6219_;
}
else
{
lean_object* v___x_6227_; lean_object* v___x_6228_; uint8_t v___x_6229_; 
v___x_6227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6225_);
v___x_6228_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6229_ = l_Lean_Expr_isConstOf(v___x_6227_, v___x_6228_);
lean_dec_ref(v___x_6227_);
if (v___x_6229_ == 0)
{
lean_dec_ref(v_arg_6224_);
goto v___jp_6219_;
}
else
{
lean_dec_ref(v_h_6218_);
lean_dec_ref(v_p_6217_);
return v_arg_6224_;
}
}
}
v___jp_6219_:
{
lean_object* v___x_6220_; lean_object* v___x_6221_; 
v___x_6220_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6221_ = l_Lean_mkAppB(v___x_6220_, v_p_6217_, v_h_6218_);
return v___x_6221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6230_, lean_object* v_a_6231_, lean_object* v_a_6232_, lean_object* v_a_6233_, lean_object* v_a_6234_){
_start:
{
lean_object* v___y_6237_; lean_object* v___y_6238_; lean_object* v___y_6239_; lean_object* v___y_6240_; lean_object* v___x_6246_; 
lean_inc_ref(v_h_6230_);
v___x_6246_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6230_, v_a_6232_);
if (lean_obj_tag(v___x_6246_) == 0)
{
lean_object* v_a_6247_; lean_object* v___x_6249_; uint8_t v_isShared_6250_; uint8_t v_isSharedCheck_6262_; 
v_a_6247_ = lean_ctor_get(v___x_6246_, 0);
v_isSharedCheck_6262_ = !lean_is_exclusive(v___x_6246_);
if (v_isSharedCheck_6262_ == 0)
{
v___x_6249_ = v___x_6246_;
v_isShared_6250_ = v_isSharedCheck_6262_;
goto v_resetjp_6248_;
}
else
{
lean_inc(v_a_6247_);
lean_dec(v___x_6246_);
v___x_6249_ = lean_box(0);
v_isShared_6250_ = v_isSharedCheck_6262_;
goto v_resetjp_6248_;
}
v_resetjp_6248_:
{
lean_object* v___x_6251_; uint8_t v___x_6252_; 
v___x_6251_ = l_Lean_Expr_cleanupAnnotations(v_a_6247_);
v___x_6252_ = l_Lean_Expr_isApp(v___x_6251_);
if (v___x_6252_ == 0)
{
lean_dec_ref(v___x_6251_);
lean_del_object(v___x_6249_);
v___y_6237_ = v_a_6231_;
v___y_6238_ = v_a_6232_;
v___y_6239_ = v_a_6233_;
v___y_6240_ = v_a_6234_;
goto v___jp_6236_;
}
else
{
lean_object* v_arg_6253_; lean_object* v___x_6254_; uint8_t v___x_6255_; 
v_arg_6253_ = lean_ctor_get(v___x_6251_, 1);
lean_inc_ref(v_arg_6253_);
v___x_6254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6251_);
v___x_6255_ = l_Lean_Expr_isApp(v___x_6254_);
if (v___x_6255_ == 0)
{
lean_dec_ref(v___x_6254_);
lean_dec_ref(v_arg_6253_);
lean_del_object(v___x_6249_);
v___y_6237_ = v_a_6231_;
v___y_6238_ = v_a_6232_;
v___y_6239_ = v_a_6233_;
v___y_6240_ = v_a_6234_;
goto v___jp_6236_;
}
else
{
lean_object* v___x_6256_; lean_object* v___x_6257_; uint8_t v___x_6258_; 
v___x_6256_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6254_);
v___x_6257_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6258_ = l_Lean_Expr_isConstOf(v___x_6256_, v___x_6257_);
lean_dec_ref(v___x_6256_);
if (v___x_6258_ == 0)
{
lean_dec_ref(v_arg_6253_);
lean_del_object(v___x_6249_);
v___y_6237_ = v_a_6231_;
v___y_6238_ = v_a_6232_;
v___y_6239_ = v_a_6233_;
v___y_6240_ = v_a_6234_;
goto v___jp_6236_;
}
else
{
lean_object* v___x_6260_; 
lean_dec_ref(v_h_6230_);
if (v_isShared_6250_ == 0)
{
lean_ctor_set(v___x_6249_, 0, v_arg_6253_);
v___x_6260_ = v___x_6249_;
goto v_reusejp_6259_;
}
else
{
lean_object* v_reuseFailAlloc_6261_; 
v_reuseFailAlloc_6261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_arg_6253_);
v___x_6260_ = v_reuseFailAlloc_6261_;
goto v_reusejp_6259_;
}
v_reusejp_6259_:
{
return v___x_6260_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6230_);
return v___x_6246_;
}
v___jp_6236_:
{
lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; 
v___x_6241_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6242_ = lean_unsigned_to_nat(1u);
v___x_6243_ = lean_mk_empty_array_with_capacity(v___x_6242_);
v___x_6244_ = lean_array_push(v___x_6243_, v_h_6230_);
v___x_6245_ = l_Lean_Meta_mkAppM(v___x_6241_, v___x_6244_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
return v___x_6245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6263_, lean_object* v_a_6264_, lean_object* v_a_6265_, lean_object* v_a_6266_, lean_object* v_a_6267_, lean_object* v_a_6268_){
_start:
{
lean_object* v_res_6269_; 
v_res_6269_ = l_Lean_Meta_mkOfEqFalse(v_h_6263_, v_a_6264_, v_a_6265_, v_a_6266_, v_a_6267_);
lean_dec(v_a_6267_);
lean_dec_ref(v_a_6266_);
lean_dec(v_a_6265_);
lean_dec_ref(v_a_6264_);
return v_res_6269_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; 
v___x_6273_ = lean_box(0);
v___x_6274_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6275_ = l_Lean_mkConst(v___x_6274_, v___x_6273_);
return v___x_6275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6279_, lean_object* v_h_6280_){
_start:
{
lean_object* v___x_6284_; uint8_t v___x_6285_; 
lean_inc_ref(v_h_6280_);
v___x_6284_ = l_Lean_Expr_cleanupAnnotations(v_h_6280_);
v___x_6285_ = l_Lean_Expr_isApp(v___x_6284_);
if (v___x_6285_ == 0)
{
lean_dec_ref(v___x_6284_);
goto v___jp_6281_;
}
else
{
lean_object* v_arg_6286_; lean_object* v___x_6287_; uint8_t v___x_6288_; 
v_arg_6286_ = lean_ctor_get(v___x_6284_, 1);
lean_inc_ref(v_arg_6286_);
v___x_6287_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6284_);
v___x_6288_ = l_Lean_Expr_isApp(v___x_6287_);
if (v___x_6288_ == 0)
{
lean_dec_ref(v___x_6287_);
lean_dec_ref(v_arg_6286_);
goto v___jp_6281_;
}
else
{
lean_object* v___x_6289_; lean_object* v___x_6290_; uint8_t v___x_6291_; 
v___x_6289_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6287_);
v___x_6290_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6291_ = l_Lean_Expr_isConstOf(v___x_6289_, v___x_6290_);
lean_dec_ref(v___x_6289_);
if (v___x_6291_ == 0)
{
lean_dec_ref(v_arg_6286_);
goto v___jp_6281_;
}
else
{
lean_dec_ref(v_h_6280_);
lean_dec_ref(v_p_6279_);
return v_arg_6286_;
}
}
}
v___jp_6281_:
{
lean_object* v___x_6282_; lean_object* v___x_6283_; 
v___x_6282_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6283_ = l_Lean_mkAppB(v___x_6282_, v_p_6279_, v_h_6280_);
return v___x_6283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_, lean_object* v_a_6295_, lean_object* v_a_6296_){
_start:
{
lean_object* v___y_6299_; lean_object* v___y_6300_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___x_6308_; 
lean_inc_ref(v_h_6292_);
v___x_6308_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6292_, v_a_6294_);
if (lean_obj_tag(v___x_6308_) == 0)
{
lean_object* v_a_6309_; lean_object* v___x_6311_; uint8_t v_isShared_6312_; uint8_t v_isSharedCheck_6324_; 
v_a_6309_ = lean_ctor_get(v___x_6308_, 0);
v_isSharedCheck_6324_ = !lean_is_exclusive(v___x_6308_);
if (v_isSharedCheck_6324_ == 0)
{
v___x_6311_ = v___x_6308_;
v_isShared_6312_ = v_isSharedCheck_6324_;
goto v_resetjp_6310_;
}
else
{
lean_inc(v_a_6309_);
lean_dec(v___x_6308_);
v___x_6311_ = lean_box(0);
v_isShared_6312_ = v_isSharedCheck_6324_;
goto v_resetjp_6310_;
}
v_resetjp_6310_:
{
lean_object* v___x_6313_; uint8_t v___x_6314_; 
v___x_6313_ = l_Lean_Expr_cleanupAnnotations(v_a_6309_);
v___x_6314_ = l_Lean_Expr_isApp(v___x_6313_);
if (v___x_6314_ == 0)
{
lean_dec_ref(v___x_6313_);
lean_del_object(v___x_6311_);
v___y_6299_ = v_a_6293_;
v___y_6300_ = v_a_6294_;
v___y_6301_ = v_a_6295_;
v___y_6302_ = v_a_6296_;
goto v___jp_6298_;
}
else
{
lean_object* v_arg_6315_; lean_object* v___x_6316_; uint8_t v___x_6317_; 
v_arg_6315_ = lean_ctor_get(v___x_6313_, 1);
lean_inc_ref(v_arg_6315_);
v___x_6316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6313_);
v___x_6317_ = l_Lean_Expr_isApp(v___x_6316_);
if (v___x_6317_ == 0)
{
lean_dec_ref(v___x_6316_);
lean_dec_ref(v_arg_6315_);
lean_del_object(v___x_6311_);
v___y_6299_ = v_a_6293_;
v___y_6300_ = v_a_6294_;
v___y_6301_ = v_a_6295_;
v___y_6302_ = v_a_6296_;
goto v___jp_6298_;
}
else
{
lean_object* v___x_6318_; lean_object* v___x_6319_; uint8_t v___x_6320_; 
v___x_6318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6316_);
v___x_6319_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6320_ = l_Lean_Expr_isConstOf(v___x_6318_, v___x_6319_);
lean_dec_ref(v___x_6318_);
if (v___x_6320_ == 0)
{
lean_dec_ref(v_arg_6315_);
lean_del_object(v___x_6311_);
v___y_6299_ = v_a_6293_;
v___y_6300_ = v_a_6294_;
v___y_6301_ = v_a_6295_;
v___y_6302_ = v_a_6296_;
goto v___jp_6298_;
}
else
{
lean_object* v___x_6322_; 
lean_dec_ref(v_h_6292_);
if (v_isShared_6312_ == 0)
{
lean_ctor_set(v___x_6311_, 0, v_arg_6315_);
v___x_6322_ = v___x_6311_;
goto v_reusejp_6321_;
}
else
{
lean_object* v_reuseFailAlloc_6323_; 
v_reuseFailAlloc_6323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6323_, 0, v_arg_6315_);
v___x_6322_ = v_reuseFailAlloc_6323_;
goto v_reusejp_6321_;
}
v_reusejp_6321_:
{
return v___x_6322_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6292_);
return v___x_6308_;
}
v___jp_6298_:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; 
v___x_6303_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6304_ = lean_unsigned_to_nat(1u);
v___x_6305_ = lean_mk_empty_array_with_capacity(v___x_6304_);
v___x_6306_ = lean_array_push(v___x_6305_, v_h_6292_);
v___x_6307_ = l_Lean_Meta_mkAppM(v___x_6303_, v___x_6306_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_);
return v___x_6307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6325_, lean_object* v_a_6326_, lean_object* v_a_6327_, lean_object* v_a_6328_, lean_object* v_a_6329_, lean_object* v_a_6330_){
_start:
{
lean_object* v_res_6331_; 
v_res_6331_ = l_Lean_Meta_mkOfEqTrue(v_h_6325_, v_a_6326_, v_a_6327_, v_a_6328_, v_a_6329_);
lean_dec(v_a_6329_);
lean_dec_ref(v_a_6328_);
lean_dec(v_a_6327_);
lean_dec_ref(v_a_6326_);
return v_res_6331_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; 
v___x_6332_ = lean_box(0);
v___x_6333_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6334_ = l_Lean_mkConst(v___x_6333_, v___x_6332_);
return v___x_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6335_, lean_object* v_h_6336_){
_start:
{
lean_object* v___x_6340_; uint8_t v___x_6341_; 
lean_inc_ref(v_h_6336_);
v___x_6340_ = l_Lean_Expr_cleanupAnnotations(v_h_6336_);
v___x_6341_ = l_Lean_Expr_isApp(v___x_6340_);
if (v___x_6341_ == 0)
{
lean_dec_ref(v___x_6340_);
goto v___jp_6337_;
}
else
{
lean_object* v_arg_6342_; lean_object* v___x_6343_; uint8_t v___x_6344_; 
v_arg_6342_ = lean_ctor_get(v___x_6340_, 1);
lean_inc_ref(v_arg_6342_);
v___x_6343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6340_);
v___x_6344_ = l_Lean_Expr_isApp(v___x_6343_);
if (v___x_6344_ == 0)
{
lean_dec_ref(v___x_6343_);
lean_dec_ref(v_arg_6342_);
goto v___jp_6337_;
}
else
{
lean_object* v___x_6345_; lean_object* v___x_6346_; uint8_t v___x_6347_; 
v___x_6345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6343_);
v___x_6346_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6347_ = l_Lean_Expr_isConstOf(v___x_6345_, v___x_6346_);
lean_dec_ref(v___x_6345_);
if (v___x_6347_ == 0)
{
lean_dec_ref(v_arg_6342_);
goto v___jp_6337_;
}
else
{
lean_dec_ref(v_h_6336_);
lean_dec_ref(v_p_6335_);
return v_arg_6342_;
}
}
}
v___jp_6337_:
{
lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6338_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6339_ = l_Lean_mkAppB(v___x_6338_, v_p_6335_, v_h_6336_);
return v___x_6339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6348_, lean_object* v_a_6349_, lean_object* v_a_6350_, lean_object* v_a_6351_, lean_object* v_a_6352_){
_start:
{
lean_object* v___y_6355_; lean_object* v___y_6356_; lean_object* v___y_6357_; lean_object* v___y_6358_; lean_object* v___x_6370_; 
lean_inc_ref(v_h_6348_);
v___x_6370_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6348_, v_a_6350_);
if (lean_obj_tag(v___x_6370_) == 0)
{
lean_object* v_a_6371_; lean_object* v___x_6373_; uint8_t v_isShared_6374_; uint8_t v_isSharedCheck_6386_; 
v_a_6371_ = lean_ctor_get(v___x_6370_, 0);
v_isSharedCheck_6386_ = !lean_is_exclusive(v___x_6370_);
if (v_isSharedCheck_6386_ == 0)
{
v___x_6373_ = v___x_6370_;
v_isShared_6374_ = v_isSharedCheck_6386_;
goto v_resetjp_6372_;
}
else
{
lean_inc(v_a_6371_);
lean_dec(v___x_6370_);
v___x_6373_ = lean_box(0);
v_isShared_6374_ = v_isSharedCheck_6386_;
goto v_resetjp_6372_;
}
v_resetjp_6372_:
{
lean_object* v___x_6375_; uint8_t v___x_6376_; 
v___x_6375_ = l_Lean_Expr_cleanupAnnotations(v_a_6371_);
v___x_6376_ = l_Lean_Expr_isApp(v___x_6375_);
if (v___x_6376_ == 0)
{
lean_dec_ref(v___x_6375_);
lean_del_object(v___x_6373_);
v___y_6355_ = v_a_6349_;
v___y_6356_ = v_a_6350_;
v___y_6357_ = v_a_6351_;
v___y_6358_ = v_a_6352_;
goto v___jp_6354_;
}
else
{
lean_object* v_arg_6377_; lean_object* v___x_6378_; uint8_t v___x_6379_; 
v_arg_6377_ = lean_ctor_get(v___x_6375_, 1);
lean_inc_ref(v_arg_6377_);
v___x_6378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6375_);
v___x_6379_ = l_Lean_Expr_isApp(v___x_6378_);
if (v___x_6379_ == 0)
{
lean_dec_ref(v___x_6378_);
lean_dec_ref(v_arg_6377_);
lean_del_object(v___x_6373_);
v___y_6355_ = v_a_6349_;
v___y_6356_ = v_a_6350_;
v___y_6357_ = v_a_6351_;
v___y_6358_ = v_a_6352_;
goto v___jp_6354_;
}
else
{
lean_object* v___x_6380_; lean_object* v___x_6381_; uint8_t v___x_6382_; 
v___x_6380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6378_);
v___x_6381_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6382_ = l_Lean_Expr_isConstOf(v___x_6380_, v___x_6381_);
lean_dec_ref(v___x_6380_);
if (v___x_6382_ == 0)
{
lean_dec_ref(v_arg_6377_);
lean_del_object(v___x_6373_);
v___y_6355_ = v_a_6349_;
v___y_6356_ = v_a_6350_;
v___y_6357_ = v_a_6351_;
v___y_6358_ = v_a_6352_;
goto v___jp_6354_;
}
else
{
lean_object* v___x_6384_; 
lean_dec_ref(v_h_6348_);
if (v_isShared_6374_ == 0)
{
lean_ctor_set(v___x_6373_, 0, v_arg_6377_);
v___x_6384_ = v___x_6373_;
goto v_reusejp_6383_;
}
else
{
lean_object* v_reuseFailAlloc_6385_; 
v_reuseFailAlloc_6385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6385_, 0, v_arg_6377_);
v___x_6384_ = v_reuseFailAlloc_6385_;
goto v_reusejp_6383_;
}
v_reusejp_6383_:
{
return v___x_6384_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6348_);
return v___x_6370_;
}
v___jp_6354_:
{
lean_object* v___x_6359_; 
lean_inc(v___y_6358_);
lean_inc_ref(v___y_6357_);
lean_inc(v___y_6356_);
lean_inc_ref(v___y_6355_);
lean_inc_ref(v_h_6348_);
v___x_6359_ = lean_infer_type(v_h_6348_, v___y_6355_, v___y_6356_, v___y_6357_, v___y_6358_);
if (lean_obj_tag(v___x_6359_) == 0)
{
lean_object* v_a_6360_; lean_object* v___x_6362_; uint8_t v_isShared_6363_; uint8_t v_isSharedCheck_6369_; 
v_a_6360_ = lean_ctor_get(v___x_6359_, 0);
v_isSharedCheck_6369_ = !lean_is_exclusive(v___x_6359_);
if (v_isSharedCheck_6369_ == 0)
{
v___x_6362_ = v___x_6359_;
v_isShared_6363_ = v_isSharedCheck_6369_;
goto v_resetjp_6361_;
}
else
{
lean_inc(v_a_6360_);
lean_dec(v___x_6359_);
v___x_6362_ = lean_box(0);
v_isShared_6363_ = v_isSharedCheck_6369_;
goto v_resetjp_6361_;
}
v_resetjp_6361_:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6367_; 
v___x_6364_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6365_ = l_Lean_mkAppB(v___x_6364_, v_a_6360_, v_h_6348_);
if (v_isShared_6363_ == 0)
{
lean_ctor_set(v___x_6362_, 0, v___x_6365_);
v___x_6367_ = v___x_6362_;
goto v_reusejp_6366_;
}
else
{
lean_object* v_reuseFailAlloc_6368_; 
v_reuseFailAlloc_6368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6368_, 0, v___x_6365_);
v___x_6367_ = v_reuseFailAlloc_6368_;
goto v_reusejp_6366_;
}
v_reusejp_6366_:
{
return v___x_6367_;
}
}
}
else
{
lean_dec_ref(v_h_6348_);
return v___x_6359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_, lean_object* v_a_6391_, lean_object* v_a_6392_){
_start:
{
lean_object* v_res_6393_; 
v_res_6393_ = l_Lean_Meta_mkEqTrue(v_h_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
lean_dec(v_a_6391_);
lean_dec_ref(v_a_6390_);
lean_dec(v_a_6389_);
lean_dec_ref(v_a_6388_);
return v_res_6393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6394_, lean_object* v_a_6395_, lean_object* v_a_6396_, lean_object* v_a_6397_, lean_object* v_a_6398_){
_start:
{
lean_object* v___y_6401_; lean_object* v___y_6402_; lean_object* v___y_6403_; lean_object* v___y_6404_; lean_object* v___x_6410_; uint8_t v___x_6411_; 
lean_inc_ref(v_h_6394_);
v___x_6410_ = l_Lean_Expr_cleanupAnnotations(v_h_6394_);
v___x_6411_ = l_Lean_Expr_isApp(v___x_6410_);
if (v___x_6411_ == 0)
{
lean_dec_ref(v___x_6410_);
v___y_6401_ = v_a_6395_;
v___y_6402_ = v_a_6396_;
v___y_6403_ = v_a_6397_;
v___y_6404_ = v_a_6398_;
goto v___jp_6400_;
}
else
{
lean_object* v_arg_6412_; lean_object* v___x_6413_; uint8_t v___x_6414_; 
v_arg_6412_ = lean_ctor_get(v___x_6410_, 1);
lean_inc_ref(v_arg_6412_);
v___x_6413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6410_);
v___x_6414_ = l_Lean_Expr_isApp(v___x_6413_);
if (v___x_6414_ == 0)
{
lean_dec_ref(v___x_6413_);
lean_dec_ref(v_arg_6412_);
v___y_6401_ = v_a_6395_;
v___y_6402_ = v_a_6396_;
v___y_6403_ = v_a_6397_;
v___y_6404_ = v_a_6398_;
goto v___jp_6400_;
}
else
{
lean_object* v___x_6415_; lean_object* v___x_6416_; uint8_t v___x_6417_; 
v___x_6415_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6413_);
v___x_6416_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6417_ = l_Lean_Expr_isConstOf(v___x_6415_, v___x_6416_);
lean_dec_ref(v___x_6415_);
if (v___x_6417_ == 0)
{
lean_dec_ref(v_arg_6412_);
v___y_6401_ = v_a_6395_;
v___y_6402_ = v_a_6396_;
v___y_6403_ = v_a_6397_;
v___y_6404_ = v_a_6398_;
goto v___jp_6400_;
}
else
{
lean_object* v___x_6418_; 
lean_dec_ref(v_h_6394_);
v___x_6418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6418_, 0, v_arg_6412_);
return v___x_6418_;
}
}
}
v___jp_6400_:
{
lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; 
v___x_6405_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6406_ = lean_unsigned_to_nat(1u);
v___x_6407_ = lean_mk_empty_array_with_capacity(v___x_6406_);
v___x_6408_ = lean_array_push(v___x_6407_, v_h_6394_);
v___x_6409_ = l_Lean_Meta_mkAppM(v___x_6405_, v___x_6408_, v___y_6401_, v___y_6402_, v___y_6403_, v___y_6404_);
return v___x_6409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6419_, lean_object* v_a_6420_, lean_object* v_a_6421_, lean_object* v_a_6422_, lean_object* v_a_6423_, lean_object* v_a_6424_){
_start:
{
lean_object* v_res_6425_; 
v_res_6425_ = l_Lean_Meta_mkEqFalse(v_h_6419_, v_a_6420_, v_a_6421_, v_a_6422_, v_a_6423_);
lean_dec(v_a_6423_);
lean_dec_ref(v_a_6422_);
lean_dec(v_a_6421_);
lean_dec_ref(v_a_6420_);
return v_res_6425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6429_, lean_object* v_a_6430_, lean_object* v_a_6431_, lean_object* v_a_6432_, lean_object* v_a_6433_){
_start:
{
lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; 
v___x_6435_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6436_ = lean_unsigned_to_nat(1u);
v___x_6437_ = lean_mk_empty_array_with_capacity(v___x_6436_);
v___x_6438_ = lean_array_push(v___x_6437_, v_h_6429_);
v___x_6439_ = l_Lean_Meta_mkAppM(v___x_6435_, v___x_6438_, v_a_6430_, v_a_6431_, v_a_6432_, v_a_6433_);
return v___x_6439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6440_, lean_object* v_a_6441_, lean_object* v_a_6442_, lean_object* v_a_6443_, lean_object* v_a_6444_, lean_object* v_a_6445_){
_start:
{
lean_object* v_res_6446_; 
v_res_6446_ = l_Lean_Meta_mkEqFalse_x27(v_h_6440_, v_a_6441_, v_a_6442_, v_a_6443_, v_a_6444_);
lean_dec(v_a_6444_);
lean_dec_ref(v_a_6443_);
lean_dec(v_a_6442_);
lean_dec_ref(v_a_6441_);
return v_res_6446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6450_, lean_object* v_h_u2082_6451_, lean_object* v_a_6452_, lean_object* v_a_6453_, lean_object* v_a_6454_, lean_object* v_a_6455_){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; 
v___x_6457_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6458_ = lean_unsigned_to_nat(2u);
v___x_6459_ = lean_mk_empty_array_with_capacity(v___x_6458_);
v___x_6460_ = lean_array_push(v___x_6459_, v_h_u2081_6450_);
v___x_6461_ = lean_array_push(v___x_6460_, v_h_u2082_6451_);
v___x_6462_ = l_Lean_Meta_mkAppM(v___x_6457_, v___x_6461_, v_a_6452_, v_a_6453_, v_a_6454_, v_a_6455_);
return v___x_6462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6463_, lean_object* v_h_u2082_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_, lean_object* v_a_6467_, lean_object* v_a_6468_, lean_object* v_a_6469_){
_start:
{
lean_object* v_res_6470_; 
v_res_6470_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6463_, v_h_u2082_6464_, v_a_6465_, v_a_6466_, v_a_6467_, v_a_6468_);
lean_dec(v_a_6468_);
lean_dec_ref(v_a_6467_);
lean_dec(v_a_6466_);
lean_dec_ref(v_a_6465_);
return v_res_6470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6474_, lean_object* v_h_u2082_6475_, lean_object* v_a_6476_, lean_object* v_a_6477_, lean_object* v_a_6478_, lean_object* v_a_6479_){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; 
v___x_6481_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6482_ = lean_unsigned_to_nat(2u);
v___x_6483_ = lean_mk_empty_array_with_capacity(v___x_6482_);
v___x_6484_ = lean_array_push(v___x_6483_, v_h_u2081_6474_);
v___x_6485_ = lean_array_push(v___x_6484_, v_h_u2082_6475_);
v___x_6486_ = l_Lean_Meta_mkAppM(v___x_6481_, v___x_6485_, v_a_6476_, v_a_6477_, v_a_6478_, v_a_6479_);
return v___x_6486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6487_, lean_object* v_h_u2082_6488_, lean_object* v_a_6489_, lean_object* v_a_6490_, lean_object* v_a_6491_, lean_object* v_a_6492_, lean_object* v_a_6493_){
_start:
{
lean_object* v_res_6494_; 
v_res_6494_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6487_, v_h_u2082_6488_, v_a_6489_, v_a_6490_, v_a_6491_, v_a_6492_);
lean_dec(v_a_6492_);
lean_dec_ref(v_a_6491_);
lean_dec(v_a_6490_);
lean_dec_ref(v_a_6489_);
return v_res_6494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6498_, lean_object* v_h_u2082_6499_, lean_object* v_a_6500_, lean_object* v_a_6501_, lean_object* v_a_6502_, lean_object* v_a_6503_){
_start:
{
lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; 
v___x_6505_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6506_ = lean_unsigned_to_nat(2u);
v___x_6507_ = lean_mk_empty_array_with_capacity(v___x_6506_);
v___x_6508_ = lean_array_push(v___x_6507_, v_h_u2081_6498_);
v___x_6509_ = lean_array_push(v___x_6508_, v_h_u2082_6499_);
v___x_6510_ = l_Lean_Meta_mkAppM(v___x_6505_, v___x_6509_, v_a_6500_, v_a_6501_, v_a_6502_, v_a_6503_);
return v___x_6510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6511_, lean_object* v_h_u2082_6512_, lean_object* v_a_6513_, lean_object* v_a_6514_, lean_object* v_a_6515_, lean_object* v_a_6516_, lean_object* v_a_6517_){
_start:
{
lean_object* v_res_6518_; 
v_res_6518_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6511_, v_h_u2082_6512_, v_a_6513_, v_a_6514_, v_a_6515_, v_a_6516_);
lean_dec(v_a_6516_);
lean_dec_ref(v_a_6515_);
lean_dec(v_a_6514_);
lean_dec_ref(v_a_6513_);
return v_res_6518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6522_, lean_object* v_a_6523_, lean_object* v_a_6524_, lean_object* v_a_6525_, lean_object* v_a_6526_){
_start:
{
lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; 
v___x_6528_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6529_ = lean_unsigned_to_nat(1u);
v___x_6530_ = lean_mk_empty_array_with_capacity(v___x_6529_);
v___x_6531_ = lean_array_push(v___x_6530_, v_h_6522_);
v___x_6532_ = l_Lean_Meta_mkAppM(v___x_6528_, v___x_6531_, v_a_6523_, v_a_6524_, v_a_6525_, v_a_6526_);
return v___x_6532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6533_, lean_object* v_a_6534_, lean_object* v_a_6535_, lean_object* v_a_6536_, lean_object* v_a_6537_, lean_object* v_a_6538_){
_start:
{
lean_object* v_res_6539_; 
v_res_6539_ = l_Lean_Meta_mkForallCongr(v_h_6533_, v_a_6534_, v_a_6535_, v_a_6536_, v_a_6537_);
lean_dec(v_a_6537_);
lean_dec_ref(v_a_6536_);
lean_dec(v_a_6535_);
lean_dec_ref(v_a_6534_);
return v_res_6539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6543_, lean_object* v_a_6544_, lean_object* v_a_6545_, lean_object* v_a_6546_, lean_object* v_a_6547_){
_start:
{
lean_object* v___y_6550_; uint8_t v___y_6551_; lean_object* v___y_6555_; lean_object* v_a_6556_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; 
v___x_6559_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6560_ = lean_unsigned_to_nat(1u);
v___x_6561_ = lean_mk_empty_array_with_capacity(v___x_6560_);
v___x_6562_ = lean_array_push(v___x_6561_, v_m_6543_);
v___x_6563_ = l_Lean_Meta_mkAppM(v___x_6559_, v___x_6562_, v_a_6544_, v_a_6545_, v_a_6546_, v_a_6547_);
if (lean_obj_tag(v___x_6563_) == 0)
{
lean_object* v_a_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; 
v_a_6564_ = lean_ctor_get(v___x_6563_, 0);
lean_inc(v_a_6564_);
lean_dec_ref_known(v___x_6563_, 1);
v___x_6565_ = lean_box(0);
v___x_6566_ = l_Lean_Meta_trySynthInstance(v_a_6564_, v___x_6565_, v_a_6544_, v_a_6545_, v_a_6546_, v_a_6547_);
if (lean_obj_tag(v___x_6566_) == 0)
{
lean_object* v_a_6567_; lean_object* v___x_6569_; uint8_t v_isShared_6570_; uint8_t v_isSharedCheck_6585_; 
v_a_6567_ = lean_ctor_get(v___x_6566_, 0);
v_isSharedCheck_6585_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6585_ == 0)
{
v___x_6569_ = v___x_6566_;
v_isShared_6570_ = v_isSharedCheck_6585_;
goto v_resetjp_6568_;
}
else
{
lean_inc(v_a_6567_);
lean_dec(v___x_6566_);
v___x_6569_ = lean_box(0);
v_isShared_6570_ = v_isSharedCheck_6585_;
goto v_resetjp_6568_;
}
v_resetjp_6568_:
{
if (lean_obj_tag(v_a_6567_) == 1)
{
lean_object* v_a_6571_; lean_object* v___x_6573_; uint8_t v_isShared_6574_; uint8_t v_isSharedCheck_6581_; 
v_a_6571_ = lean_ctor_get(v_a_6567_, 0);
v_isSharedCheck_6581_ = !lean_is_exclusive(v_a_6567_);
if (v_isSharedCheck_6581_ == 0)
{
v___x_6573_ = v_a_6567_;
v_isShared_6574_ = v_isSharedCheck_6581_;
goto v_resetjp_6572_;
}
else
{
lean_inc(v_a_6571_);
lean_dec(v_a_6567_);
v___x_6573_ = lean_box(0);
v_isShared_6574_ = v_isSharedCheck_6581_;
goto v_resetjp_6572_;
}
v_resetjp_6572_:
{
lean_object* v___x_6576_; 
if (v_isShared_6574_ == 0)
{
v___x_6576_ = v___x_6573_;
goto v_reusejp_6575_;
}
else
{
lean_object* v_reuseFailAlloc_6580_; 
v_reuseFailAlloc_6580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_a_6571_);
v___x_6576_ = v_reuseFailAlloc_6580_;
goto v_reusejp_6575_;
}
v_reusejp_6575_:
{
lean_object* v___x_6578_; 
if (v_isShared_6570_ == 0)
{
lean_ctor_set(v___x_6569_, 0, v___x_6576_);
v___x_6578_ = v___x_6569_;
goto v_reusejp_6577_;
}
else
{
lean_object* v_reuseFailAlloc_6579_; 
v_reuseFailAlloc_6579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6579_, 0, v___x_6576_);
v___x_6578_ = v_reuseFailAlloc_6579_;
goto v_reusejp_6577_;
}
v_reusejp_6577_:
{
return v___x_6578_;
}
}
}
}
else
{
lean_object* v___x_6583_; 
lean_dec(v_a_6567_);
if (v_isShared_6570_ == 0)
{
lean_ctor_set(v___x_6569_, 0, v___x_6565_);
v___x_6583_ = v___x_6569_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6584_; 
v_reuseFailAlloc_6584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6584_, 0, v___x_6565_);
v___x_6583_ = v_reuseFailAlloc_6584_;
goto v_reusejp_6582_;
}
v_reusejp_6582_:
{
return v___x_6583_;
}
}
}
}
else
{
lean_object* v_a_6586_; lean_object* v___x_6588_; uint8_t v_isShared_6589_; uint8_t v_isSharedCheck_6593_; 
v_a_6586_ = lean_ctor_get(v___x_6566_, 0);
v_isSharedCheck_6593_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6593_ == 0)
{
v___x_6588_ = v___x_6566_;
v_isShared_6589_ = v_isSharedCheck_6593_;
goto v_resetjp_6587_;
}
else
{
lean_inc(v_a_6586_);
lean_dec(v___x_6566_);
v___x_6588_ = lean_box(0);
v_isShared_6589_ = v_isSharedCheck_6593_;
goto v_resetjp_6587_;
}
v_resetjp_6587_:
{
lean_object* v___x_6591_; 
lean_inc(v_a_6586_);
if (v_isShared_6589_ == 0)
{
v___x_6591_ = v___x_6588_;
goto v_reusejp_6590_;
}
else
{
lean_object* v_reuseFailAlloc_6592_; 
v_reuseFailAlloc_6592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6592_, 0, v_a_6586_);
v___x_6591_ = v_reuseFailAlloc_6592_;
goto v_reusejp_6590_;
}
v_reusejp_6590_:
{
v___y_6555_ = v___x_6591_;
v_a_6556_ = v_a_6586_;
goto v___jp_6554_;
}
}
}
}
else
{
lean_object* v_a_6594_; lean_object* v___x_6596_; uint8_t v_isShared_6597_; uint8_t v_isSharedCheck_6601_; 
v_a_6594_ = lean_ctor_get(v___x_6563_, 0);
v_isSharedCheck_6601_ = !lean_is_exclusive(v___x_6563_);
if (v_isSharedCheck_6601_ == 0)
{
v___x_6596_ = v___x_6563_;
v_isShared_6597_ = v_isSharedCheck_6601_;
goto v_resetjp_6595_;
}
else
{
lean_inc(v_a_6594_);
lean_dec(v___x_6563_);
v___x_6596_ = lean_box(0);
v_isShared_6597_ = v_isSharedCheck_6601_;
goto v_resetjp_6595_;
}
v_resetjp_6595_:
{
lean_object* v___x_6599_; 
lean_inc(v_a_6594_);
if (v_isShared_6597_ == 0)
{
v___x_6599_ = v___x_6596_;
goto v_reusejp_6598_;
}
else
{
lean_object* v_reuseFailAlloc_6600_; 
v_reuseFailAlloc_6600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6600_, 0, v_a_6594_);
v___x_6599_ = v_reuseFailAlloc_6600_;
goto v_reusejp_6598_;
}
v_reusejp_6598_:
{
v___y_6555_ = v___x_6599_;
v_a_6556_ = v_a_6594_;
goto v___jp_6554_;
}
}
}
v___jp_6549_:
{
if (v___y_6551_ == 0)
{
lean_object* v___x_6552_; lean_object* v___x_6553_; 
lean_dec_ref(v___y_6550_);
v___x_6552_ = lean_box(0);
v___x_6553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6553_, 0, v___x_6552_);
return v___x_6553_;
}
else
{
return v___y_6550_;
}
}
v___jp_6554_:
{
uint8_t v___x_6557_; 
v___x_6557_ = l_Lean_Exception_isInterrupt(v_a_6556_);
if (v___x_6557_ == 0)
{
uint8_t v___x_6558_; 
v___x_6558_ = l_Lean_Exception_isRuntime(v_a_6556_);
v___y_6550_ = v___y_6555_;
v___y_6551_ = v___x_6558_;
goto v___jp_6549_;
}
else
{
lean_dec_ref(v_a_6556_);
v___y_6550_ = v___y_6555_;
v___y_6551_ = v___x_6557_;
goto v___jp_6549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6602_, lean_object* v_a_6603_, lean_object* v_a_6604_, lean_object* v_a_6605_, lean_object* v_a_6606_, lean_object* v_a_6607_){
_start:
{
lean_object* v_res_6608_; 
v_res_6608_ = l_Lean_Meta_isMonad_x3f(v_m_6602_, v_a_6603_, v_a_6604_, v_a_6605_, v_a_6606_);
lean_dec(v_a_6606_);
lean_dec_ref(v_a_6605_);
lean_dec(v_a_6604_);
lean_dec_ref(v_a_6603_);
return v_res_6608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6616_, lean_object* v_n_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_){
_start:
{
lean_object* v___x_6623_; 
lean_inc_ref(v_type_6616_);
v___x_6623_ = l_Lean_Meta_getDecLevel(v_type_6616_, v_a_6618_, v_a_6619_, v_a_6620_, v_a_6621_);
if (lean_obj_tag(v___x_6623_) == 0)
{
lean_object* v_a_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; 
v_a_6624_ = lean_ctor_get(v___x_6623_, 0);
lean_inc(v_a_6624_);
lean_dec_ref_known(v___x_6623_, 1);
v___x_6625_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6626_ = lean_box(0);
v___x_6627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6627_, 0, v_a_6624_);
lean_ctor_set(v___x_6627_, 1, v___x_6626_);
lean_inc_ref(v___x_6627_);
v___x_6628_ = l_Lean_mkConst(v___x_6625_, v___x_6627_);
v___x_6629_ = l_Lean_mkRawNatLit(v_n_6617_);
lean_inc_ref(v___x_6629_);
lean_inc_ref(v_type_6616_);
v___x_6630_ = l_Lean_mkAppB(v___x_6628_, v_type_6616_, v___x_6629_);
v___x_6631_ = lean_box(0);
v___x_6632_ = l_Lean_Meta_synthInstance(v___x_6630_, v___x_6631_, v_a_6618_, v_a_6619_, v_a_6620_, v_a_6621_);
if (lean_obj_tag(v___x_6632_) == 0)
{
lean_object* v_a_6633_; lean_object* v___x_6635_; uint8_t v_isShared_6636_; uint8_t v_isSharedCheck_6643_; 
v_a_6633_ = lean_ctor_get(v___x_6632_, 0);
v_isSharedCheck_6643_ = !lean_is_exclusive(v___x_6632_);
if (v_isSharedCheck_6643_ == 0)
{
v___x_6635_ = v___x_6632_;
v_isShared_6636_ = v_isSharedCheck_6643_;
goto v_resetjp_6634_;
}
else
{
lean_inc(v_a_6633_);
lean_dec(v___x_6632_);
v___x_6635_ = lean_box(0);
v_isShared_6636_ = v_isSharedCheck_6643_;
goto v_resetjp_6634_;
}
v_resetjp_6634_:
{
lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6641_; 
v___x_6637_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6638_ = l_Lean_mkConst(v___x_6637_, v___x_6627_);
v___x_6639_ = l_Lean_mkApp3(v___x_6638_, v_type_6616_, v___x_6629_, v_a_6633_);
if (v_isShared_6636_ == 0)
{
lean_ctor_set(v___x_6635_, 0, v___x_6639_);
v___x_6641_ = v___x_6635_;
goto v_reusejp_6640_;
}
else
{
lean_object* v_reuseFailAlloc_6642_; 
v_reuseFailAlloc_6642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6642_, 0, v___x_6639_);
v___x_6641_ = v_reuseFailAlloc_6642_;
goto v_reusejp_6640_;
}
v_reusejp_6640_:
{
return v___x_6641_;
}
}
}
else
{
lean_dec_ref(v___x_6629_);
lean_dec_ref_known(v___x_6627_, 2);
lean_dec_ref(v_type_6616_);
return v___x_6632_;
}
}
else
{
lean_object* v_a_6644_; lean_object* v___x_6646_; uint8_t v_isShared_6647_; uint8_t v_isSharedCheck_6651_; 
lean_dec(v_n_6617_);
lean_dec_ref(v_type_6616_);
v_a_6644_ = lean_ctor_get(v___x_6623_, 0);
v_isSharedCheck_6651_ = !lean_is_exclusive(v___x_6623_);
if (v_isSharedCheck_6651_ == 0)
{
v___x_6646_ = v___x_6623_;
v_isShared_6647_ = v_isSharedCheck_6651_;
goto v_resetjp_6645_;
}
else
{
lean_inc(v_a_6644_);
lean_dec(v___x_6623_);
v___x_6646_ = lean_box(0);
v_isShared_6647_ = v_isSharedCheck_6651_;
goto v_resetjp_6645_;
}
v_resetjp_6645_:
{
lean_object* v___x_6649_; 
if (v_isShared_6647_ == 0)
{
v___x_6649_ = v___x_6646_;
goto v_reusejp_6648_;
}
else
{
lean_object* v_reuseFailAlloc_6650_; 
v_reuseFailAlloc_6650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6650_, 0, v_a_6644_);
v___x_6649_ = v_reuseFailAlloc_6650_;
goto v_reusejp_6648_;
}
v_reusejp_6648_:
{
return v___x_6649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6652_, lean_object* v_n_6653_, lean_object* v_a_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_, lean_object* v_a_6657_, lean_object* v_a_6658_){
_start:
{
lean_object* v_res_6659_; 
v_res_6659_ = l_Lean_Meta_mkNumeral(v_type_6652_, v_n_6653_, v_a_6654_, v_a_6655_, v_a_6656_, v_a_6657_);
lean_dec(v_a_6657_);
lean_dec_ref(v_a_6656_);
lean_dec(v_a_6655_);
lean_dec_ref(v_a_6654_);
return v_res_6659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6660_, lean_object* v_opName_6661_, lean_object* v_a_6662_, lean_object* v_b_6663_, lean_object* v_a_6664_, lean_object* v_a_6665_, lean_object* v_a_6666_, lean_object* v_a_6667_){
_start:
{
lean_object* v___x_6669_; 
lean_inc(v_a_6667_);
lean_inc_ref(v_a_6666_);
lean_inc(v_a_6665_);
lean_inc_ref(v_a_6664_);
lean_inc_ref(v_a_6662_);
v___x_6669_ = lean_infer_type(v_a_6662_, v_a_6664_, v_a_6665_, v_a_6666_, v_a_6667_);
if (lean_obj_tag(v___x_6669_) == 0)
{
lean_object* v_a_6670_; lean_object* v___x_6671_; 
v_a_6670_ = lean_ctor_get(v___x_6669_, 0);
lean_inc_n(v_a_6670_, 2);
lean_dec_ref_known(v___x_6669_, 1);
v___x_6671_ = l_Lean_Meta_getDecLevel(v_a_6670_, v_a_6664_, v_a_6665_, v_a_6666_, v_a_6667_);
if (lean_obj_tag(v___x_6671_) == 0)
{
lean_object* v_a_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; 
v_a_6672_ = lean_ctor_get(v___x_6671_, 0);
lean_inc_n(v_a_6672_, 3);
lean_dec_ref_known(v___x_6671_, 1);
v___x_6673_ = lean_box(0);
v___x_6674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6674_, 0, v_a_6672_);
lean_ctor_set(v___x_6674_, 1, v___x_6673_);
v___x_6675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6675_, 0, v_a_6672_);
lean_ctor_set(v___x_6675_, 1, v___x_6674_);
v___x_6676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6676_, 0, v_a_6672_);
lean_ctor_set(v___x_6676_, 1, v___x_6675_);
lean_inc_ref(v___x_6676_);
v___x_6677_ = l_Lean_mkConst(v_className_6660_, v___x_6676_);
lean_inc_n(v_a_6670_, 3);
v___x_6678_ = l_Lean_mkApp3(v___x_6677_, v_a_6670_, v_a_6670_, v_a_6670_);
v___x_6679_ = lean_box(0);
v___x_6680_ = l_Lean_Meta_synthInstance(v___x_6678_, v___x_6679_, v_a_6664_, v_a_6665_, v_a_6666_, v_a_6667_);
if (lean_obj_tag(v___x_6680_) == 0)
{
lean_object* v_a_6681_; lean_object* v___x_6683_; uint8_t v_isShared_6684_; uint8_t v_isSharedCheck_6690_; 
v_a_6681_ = lean_ctor_get(v___x_6680_, 0);
v_isSharedCheck_6690_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6690_ == 0)
{
v___x_6683_ = v___x_6680_;
v_isShared_6684_ = v_isSharedCheck_6690_;
goto v_resetjp_6682_;
}
else
{
lean_inc(v_a_6681_);
lean_dec(v___x_6680_);
v___x_6683_ = lean_box(0);
v_isShared_6684_ = v_isSharedCheck_6690_;
goto v_resetjp_6682_;
}
v_resetjp_6682_:
{
lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6688_; 
v___x_6685_ = l_Lean_mkConst(v_opName_6661_, v___x_6676_);
lean_inc_n(v_a_6670_, 2);
v___x_6686_ = l_Lean_mkApp6(v___x_6685_, v_a_6670_, v_a_6670_, v_a_6670_, v_a_6681_, v_a_6662_, v_b_6663_);
if (v_isShared_6684_ == 0)
{
lean_ctor_set(v___x_6683_, 0, v___x_6686_);
v___x_6688_ = v___x_6683_;
goto v_reusejp_6687_;
}
else
{
lean_object* v_reuseFailAlloc_6689_; 
v_reuseFailAlloc_6689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6689_, 0, v___x_6686_);
v___x_6688_ = v_reuseFailAlloc_6689_;
goto v_reusejp_6687_;
}
v_reusejp_6687_:
{
return v___x_6688_;
}
}
}
else
{
lean_dec_ref_known(v___x_6676_, 2);
lean_dec(v_a_6670_);
lean_dec_ref(v_b_6663_);
lean_dec_ref(v_a_6662_);
lean_dec(v_opName_6661_);
return v___x_6680_;
}
}
else
{
lean_object* v_a_6691_; lean_object* v___x_6693_; uint8_t v_isShared_6694_; uint8_t v_isSharedCheck_6698_; 
lean_dec(v_a_6670_);
lean_dec_ref(v_b_6663_);
lean_dec_ref(v_a_6662_);
lean_dec(v_opName_6661_);
lean_dec(v_className_6660_);
v_a_6691_ = lean_ctor_get(v___x_6671_, 0);
v_isSharedCheck_6698_ = !lean_is_exclusive(v___x_6671_);
if (v_isSharedCheck_6698_ == 0)
{
v___x_6693_ = v___x_6671_;
v_isShared_6694_ = v_isSharedCheck_6698_;
goto v_resetjp_6692_;
}
else
{
lean_inc(v_a_6691_);
lean_dec(v___x_6671_);
v___x_6693_ = lean_box(0);
v_isShared_6694_ = v_isSharedCheck_6698_;
goto v_resetjp_6692_;
}
v_resetjp_6692_:
{
lean_object* v___x_6696_; 
if (v_isShared_6694_ == 0)
{
v___x_6696_ = v___x_6693_;
goto v_reusejp_6695_;
}
else
{
lean_object* v_reuseFailAlloc_6697_; 
v_reuseFailAlloc_6697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6697_, 0, v_a_6691_);
v___x_6696_ = v_reuseFailAlloc_6697_;
goto v_reusejp_6695_;
}
v_reusejp_6695_:
{
return v___x_6696_;
}
}
}
}
else
{
lean_dec_ref(v_b_6663_);
lean_dec_ref(v_a_6662_);
lean_dec(v_opName_6661_);
lean_dec(v_className_6660_);
return v___x_6669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6699_, lean_object* v_opName_6700_, lean_object* v_a_6701_, lean_object* v_b_6702_, lean_object* v_a_6703_, lean_object* v_a_6704_, lean_object* v_a_6705_, lean_object* v_a_6706_, lean_object* v_a_6707_){
_start:
{
lean_object* v_res_6708_; 
v_res_6708_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6699_, v_opName_6700_, v_a_6701_, v_b_6702_, v_a_6703_, v_a_6704_, v_a_6705_, v_a_6706_);
lean_dec(v_a_6706_);
lean_dec_ref(v_a_6705_);
lean_dec(v_a_6704_);
lean_dec_ref(v_a_6703_);
return v_res_6708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6716_, lean_object* v_b_6717_, lean_object* v_a_6718_, lean_object* v_a_6719_, lean_object* v_a_6720_, lean_object* v_a_6721_){
_start:
{
lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; 
v___x_6723_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6724_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6725_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6723_, v___x_6724_, v_a_6716_, v_b_6717_, v_a_6718_, v_a_6719_, v_a_6720_, v_a_6721_);
return v___x_6725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6726_, lean_object* v_b_6727_, lean_object* v_a_6728_, lean_object* v_a_6729_, lean_object* v_a_6730_, lean_object* v_a_6731_, lean_object* v_a_6732_){
_start:
{
lean_object* v_res_6733_; 
v_res_6733_ = l_Lean_Meta_mkAdd(v_a_6726_, v_b_6727_, v_a_6728_, v_a_6729_, v_a_6730_, v_a_6731_);
lean_dec(v_a_6731_);
lean_dec_ref(v_a_6730_);
lean_dec(v_a_6729_);
lean_dec_ref(v_a_6728_);
return v_res_6733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6741_, lean_object* v_b_6742_, lean_object* v_a_6743_, lean_object* v_a_6744_, lean_object* v_a_6745_, lean_object* v_a_6746_){
_start:
{
lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; 
v___x_6748_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6749_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6750_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6748_, v___x_6749_, v_a_6741_, v_b_6742_, v_a_6743_, v_a_6744_, v_a_6745_, v_a_6746_);
return v___x_6750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6751_, lean_object* v_b_6752_, lean_object* v_a_6753_, lean_object* v_a_6754_, lean_object* v_a_6755_, lean_object* v_a_6756_, lean_object* v_a_6757_){
_start:
{
lean_object* v_res_6758_; 
v_res_6758_ = l_Lean_Meta_mkSub(v_a_6751_, v_b_6752_, v_a_6753_, v_a_6754_, v_a_6755_, v_a_6756_);
lean_dec(v_a_6756_);
lean_dec_ref(v_a_6755_);
lean_dec(v_a_6754_);
lean_dec_ref(v_a_6753_);
return v_res_6758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6766_, lean_object* v_b_6767_, lean_object* v_a_6768_, lean_object* v_a_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_){
_start:
{
lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; 
v___x_6773_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6774_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6775_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6773_, v___x_6774_, v_a_6766_, v_b_6767_, v_a_6768_, v_a_6769_, v_a_6770_, v_a_6771_);
return v___x_6775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6776_, lean_object* v_b_6777_, lean_object* v_a_6778_, lean_object* v_a_6779_, lean_object* v_a_6780_, lean_object* v_a_6781_, lean_object* v_a_6782_){
_start:
{
lean_object* v_res_6783_; 
v_res_6783_ = l_Lean_Meta_mkMul(v_a_6776_, v_b_6777_, v_a_6778_, v_a_6779_, v_a_6780_, v_a_6781_);
lean_dec(v_a_6781_);
lean_dec_ref(v_a_6780_);
lean_dec(v_a_6779_);
lean_dec_ref(v_a_6778_);
return v_res_6783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6784_, lean_object* v_rName_6785_, lean_object* v_a_6786_, lean_object* v_b_6787_, lean_object* v_a_6788_, lean_object* v_a_6789_, lean_object* v_a_6790_, lean_object* v_a_6791_){
_start:
{
lean_object* v___x_6793_; 
lean_inc(v_a_6791_);
lean_inc_ref(v_a_6790_);
lean_inc(v_a_6789_);
lean_inc_ref(v_a_6788_);
lean_inc_ref(v_a_6786_);
v___x_6793_ = lean_infer_type(v_a_6786_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_);
if (lean_obj_tag(v___x_6793_) == 0)
{
lean_object* v_a_6794_; lean_object* v___x_6795_; 
v_a_6794_ = lean_ctor_get(v___x_6793_, 0);
lean_inc_n(v_a_6794_, 2);
lean_dec_ref_known(v___x_6793_, 1);
v___x_6795_ = l_Lean_Meta_getDecLevel(v_a_6794_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_);
if (lean_obj_tag(v___x_6795_) == 0)
{
lean_object* v_a_6796_; lean_object* v___x_6797_; lean_object* v___x_6798_; lean_object* v___x_6799_; lean_object* v___x_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; 
v_a_6796_ = lean_ctor_get(v___x_6795_, 0);
lean_inc(v_a_6796_);
lean_dec_ref_known(v___x_6795_, 1);
v___x_6797_ = lean_box(0);
v___x_6798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6798_, 0, v_a_6796_);
lean_ctor_set(v___x_6798_, 1, v___x_6797_);
lean_inc_ref(v___x_6798_);
v___x_6799_ = l_Lean_mkConst(v_className_6784_, v___x_6798_);
lean_inc(v_a_6794_);
v___x_6800_ = l_Lean_Expr_app___override(v___x_6799_, v_a_6794_);
v___x_6801_ = lean_box(0);
v___x_6802_ = l_Lean_Meta_synthInstance(v___x_6800_, v___x_6801_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_);
if (lean_obj_tag(v___x_6802_) == 0)
{
lean_object* v_a_6803_; lean_object* v___x_6805_; uint8_t v_isShared_6806_; uint8_t v_isSharedCheck_6812_; 
v_a_6803_ = lean_ctor_get(v___x_6802_, 0);
v_isSharedCheck_6812_ = !lean_is_exclusive(v___x_6802_);
if (v_isSharedCheck_6812_ == 0)
{
v___x_6805_ = v___x_6802_;
v_isShared_6806_ = v_isSharedCheck_6812_;
goto v_resetjp_6804_;
}
else
{
lean_inc(v_a_6803_);
lean_dec(v___x_6802_);
v___x_6805_ = lean_box(0);
v_isShared_6806_ = v_isSharedCheck_6812_;
goto v_resetjp_6804_;
}
v_resetjp_6804_:
{
lean_object* v___x_6807_; lean_object* v___x_6808_; lean_object* v___x_6810_; 
v___x_6807_ = l_Lean_mkConst(v_rName_6785_, v___x_6798_);
v___x_6808_ = l_Lean_mkApp4(v___x_6807_, v_a_6794_, v_a_6803_, v_a_6786_, v_b_6787_);
if (v_isShared_6806_ == 0)
{
lean_ctor_set(v___x_6805_, 0, v___x_6808_);
v___x_6810_ = v___x_6805_;
goto v_reusejp_6809_;
}
else
{
lean_object* v_reuseFailAlloc_6811_; 
v_reuseFailAlloc_6811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6811_, 0, v___x_6808_);
v___x_6810_ = v_reuseFailAlloc_6811_;
goto v_reusejp_6809_;
}
v_reusejp_6809_:
{
return v___x_6810_;
}
}
}
else
{
lean_dec_ref_known(v___x_6798_, 2);
lean_dec(v_a_6794_);
lean_dec_ref(v_b_6787_);
lean_dec_ref(v_a_6786_);
lean_dec(v_rName_6785_);
return v___x_6802_;
}
}
else
{
lean_object* v_a_6813_; lean_object* v___x_6815_; uint8_t v_isShared_6816_; uint8_t v_isSharedCheck_6820_; 
lean_dec(v_a_6794_);
lean_dec_ref(v_b_6787_);
lean_dec_ref(v_a_6786_);
lean_dec(v_rName_6785_);
lean_dec(v_className_6784_);
v_a_6813_ = lean_ctor_get(v___x_6795_, 0);
v_isSharedCheck_6820_ = !lean_is_exclusive(v___x_6795_);
if (v_isSharedCheck_6820_ == 0)
{
v___x_6815_ = v___x_6795_;
v_isShared_6816_ = v_isSharedCheck_6820_;
goto v_resetjp_6814_;
}
else
{
lean_inc(v_a_6813_);
lean_dec(v___x_6795_);
v___x_6815_ = lean_box(0);
v_isShared_6816_ = v_isSharedCheck_6820_;
goto v_resetjp_6814_;
}
v_resetjp_6814_:
{
lean_object* v___x_6818_; 
if (v_isShared_6816_ == 0)
{
v___x_6818_ = v___x_6815_;
goto v_reusejp_6817_;
}
else
{
lean_object* v_reuseFailAlloc_6819_; 
v_reuseFailAlloc_6819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6819_, 0, v_a_6813_);
v___x_6818_ = v_reuseFailAlloc_6819_;
goto v_reusejp_6817_;
}
v_reusejp_6817_:
{
return v___x_6818_;
}
}
}
}
else
{
lean_dec_ref(v_b_6787_);
lean_dec_ref(v_a_6786_);
lean_dec(v_rName_6785_);
lean_dec(v_className_6784_);
return v___x_6793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6821_, lean_object* v_rName_6822_, lean_object* v_a_6823_, lean_object* v_b_6824_, lean_object* v_a_6825_, lean_object* v_a_6826_, lean_object* v_a_6827_, lean_object* v_a_6828_, lean_object* v_a_6829_){
_start:
{
lean_object* v_res_6830_; 
v_res_6830_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6821_, v_rName_6822_, v_a_6823_, v_b_6824_, v_a_6825_, v_a_6826_, v_a_6827_, v_a_6828_);
lean_dec(v_a_6828_);
lean_dec_ref(v_a_6827_);
lean_dec(v_a_6826_);
lean_dec_ref(v_a_6825_);
return v_res_6830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6833_, lean_object* v_b_6834_, lean_object* v_a_6835_, lean_object* v_a_6836_, lean_object* v_a_6837_, lean_object* v_a_6838_){
_start:
{
lean_object* v___x_6840_; lean_object* v___x_6841_; lean_object* v___x_6842_; 
v___x_6840_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6841_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6842_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6840_, v___x_6841_, v_a_6833_, v_b_6834_, v_a_6835_, v_a_6836_, v_a_6837_, v_a_6838_);
return v___x_6842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6843_, lean_object* v_b_6844_, lean_object* v_a_6845_, lean_object* v_a_6846_, lean_object* v_a_6847_, lean_object* v_a_6848_, lean_object* v_a_6849_){
_start:
{
lean_object* v_res_6850_; 
v_res_6850_ = l_Lean_Meta_mkLE(v_a_6843_, v_b_6844_, v_a_6845_, v_a_6846_, v_a_6847_, v_a_6848_);
lean_dec(v_a_6848_);
lean_dec_ref(v_a_6847_);
lean_dec(v_a_6846_);
lean_dec_ref(v_a_6845_);
return v_res_6850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6853_, lean_object* v_b_6854_, lean_object* v_a_6855_, lean_object* v_a_6856_, lean_object* v_a_6857_, lean_object* v_a_6858_){
_start:
{
lean_object* v___x_6860_; lean_object* v___x_6861_; lean_object* v___x_6862_; 
v___x_6860_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6861_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6862_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6860_, v___x_6861_, v_a_6853_, v_b_6854_, v_a_6855_, v_a_6856_, v_a_6857_, v_a_6858_);
return v___x_6862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6863_, lean_object* v_b_6864_, lean_object* v_a_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_){
_start:
{
lean_object* v_res_6870_; 
v_res_6870_ = l_Lean_Meta_mkLT(v_a_6863_, v_b_6864_, v_a_6865_, v_a_6866_, v_a_6867_, v_a_6868_);
lean_dec(v_a_6868_);
lean_dec_ref(v_a_6867_);
lean_dec(v_a_6866_);
lean_dec_ref(v_a_6865_);
return v_res_6870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6876_, lean_object* v_a_6877_, lean_object* v_a_6878_, lean_object* v_a_6879_, lean_object* v_a_6880_){
_start:
{
lean_object* v___x_6882_; lean_object* v___x_6883_; uint8_t v___x_6884_; 
v___x_6882_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6883_ = lean_unsigned_to_nat(3u);
v___x_6884_ = l_Lean_Expr_isAppOfArity(v_h_6876_, v___x_6882_, v___x_6883_);
if (v___x_6884_ == 0)
{
lean_object* v___x_6885_; lean_object* v___x_6886_; lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___x_6889_; 
v___x_6885_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6886_ = lean_unsigned_to_nat(1u);
v___x_6887_ = lean_mk_empty_array_with_capacity(v___x_6886_);
v___x_6888_ = lean_array_push(v___x_6887_, v_h_6876_);
v___x_6889_ = l_Lean_Meta_mkAppM(v___x_6885_, v___x_6888_, v_a_6877_, v_a_6878_, v_a_6879_, v_a_6880_);
return v___x_6889_;
}
else
{
lean_object* v___x_6890_; lean_object* v___x_6891_; 
v___x_6890_ = l_Lean_Expr_appArg_x21(v_h_6876_);
lean_dec_ref(v_h_6876_);
v___x_6891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6891_, 0, v___x_6890_);
return v___x_6891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6892_, lean_object* v_a_6893_, lean_object* v_a_6894_, lean_object* v_a_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_){
_start:
{
lean_object* v_res_6898_; 
v_res_6898_ = l_Lean_Meta_mkIffOfEq(v_h_6892_, v_a_6893_, v_a_6894_, v_a_6895_, v_a_6896_);
lean_dec(v_a_6896_);
lean_dec_ref(v_a_6895_);
lean_dec(v_a_6894_);
lean_dec_ref(v_a_6893_);
return v_res_6898_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6904_; lean_object* v___x_6905_; lean_object* v___x_6906_; 
v___x_6904_ = lean_box(0);
v___x_6905_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6906_ = l_Lean_mkConst(v___x_6905_, v___x_6904_);
return v___x_6906_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6909_; lean_object* v___x_6910_; lean_object* v___x_6911_; 
v___x_6909_ = lean_box(0);
v___x_6910_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6911_ = l_Lean_mkConst(v___x_6910_, v___x_6909_);
return v___x_6911_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6912_; lean_object* v___x_6913_; lean_object* v___x_6914_; 
v___x_6912_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6913_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6914_, 0, v___x_6913_);
lean_ctor_set(v___x_6914_, 1, v___x_6912_);
return v___x_6914_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6919_; lean_object* v___x_6920_; lean_object* v___x_6921_; 
v___x_6919_ = lean_box(0);
v___x_6920_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6921_ = l_Lean_mkConst(v___x_6920_, v___x_6919_);
return v___x_6921_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6924_; lean_object* v___x_6925_; lean_object* v___x_6926_; 
v___x_6924_ = lean_box(0);
v___x_6925_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6926_ = l_Lean_mkConst(v___x_6925_, v___x_6924_);
return v___x_6926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_, lean_object* v_a_6930_, lean_object* v_a_6931_){
_start:
{
if (lean_obj_tag(v_a_6927_) == 0)
{
lean_object* v___x_6933_; lean_object* v___x_6934_; 
v___x_6933_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6934_, 0, v___x_6933_);
return v___x_6934_;
}
else
{
lean_object* v_tail_6935_; 
v_tail_6935_ = lean_ctor_get(v_a_6927_, 1);
if (lean_obj_tag(v_tail_6935_) == 0)
{
lean_object* v_head_6936_; lean_object* v___x_6938_; uint8_t v_isShared_6939_; uint8_t v_isSharedCheck_6960_; 
v_head_6936_ = lean_ctor_get(v_a_6927_, 0);
v_isSharedCheck_6960_ = !lean_is_exclusive(v_a_6927_);
if (v_isSharedCheck_6960_ == 0)
{
lean_object* v_unused_6961_; 
v_unused_6961_ = lean_ctor_get(v_a_6927_, 1);
lean_dec(v_unused_6961_);
v___x_6938_ = v_a_6927_;
v_isShared_6939_ = v_isSharedCheck_6960_;
goto v_resetjp_6937_;
}
else
{
lean_inc(v_head_6936_);
lean_dec(v_a_6927_);
v___x_6938_ = lean_box(0);
v_isShared_6939_ = v_isSharedCheck_6960_;
goto v_resetjp_6937_;
}
v_resetjp_6937_:
{
lean_object* v___x_6940_; 
lean_inc(v_a_6931_);
lean_inc_ref(v_a_6930_);
lean_inc(v_a_6929_);
lean_inc_ref(v_a_6928_);
lean_inc(v_head_6936_);
v___x_6940_ = lean_infer_type(v_head_6936_, v_a_6928_, v_a_6929_, v_a_6930_, v_a_6931_);
if (lean_obj_tag(v___x_6940_) == 0)
{
lean_object* v_a_6941_; lean_object* v___x_6943_; uint8_t v_isShared_6944_; uint8_t v_isSharedCheck_6951_; 
v_a_6941_ = lean_ctor_get(v___x_6940_, 0);
v_isSharedCheck_6951_ = !lean_is_exclusive(v___x_6940_);
if (v_isSharedCheck_6951_ == 0)
{
v___x_6943_ = v___x_6940_;
v_isShared_6944_ = v_isSharedCheck_6951_;
goto v_resetjp_6942_;
}
else
{
lean_inc(v_a_6941_);
lean_dec(v___x_6940_);
v___x_6943_ = lean_box(0);
v_isShared_6944_ = v_isSharedCheck_6951_;
goto v_resetjp_6942_;
}
v_resetjp_6942_:
{
lean_object* v___x_6946_; 
if (v_isShared_6939_ == 0)
{
lean_ctor_set_tag(v___x_6938_, 0);
lean_ctor_set(v___x_6938_, 1, v_a_6941_);
v___x_6946_ = v___x_6938_;
goto v_reusejp_6945_;
}
else
{
lean_object* v_reuseFailAlloc_6950_; 
v_reuseFailAlloc_6950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6950_, 0, v_head_6936_);
lean_ctor_set(v_reuseFailAlloc_6950_, 1, v_a_6941_);
v___x_6946_ = v_reuseFailAlloc_6950_;
goto v_reusejp_6945_;
}
v_reusejp_6945_:
{
lean_object* v___x_6948_; 
if (v_isShared_6944_ == 0)
{
lean_ctor_set(v___x_6943_, 0, v___x_6946_);
v___x_6948_ = v___x_6943_;
goto v_reusejp_6947_;
}
else
{
lean_object* v_reuseFailAlloc_6949_; 
v_reuseFailAlloc_6949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6949_, 0, v___x_6946_);
v___x_6948_ = v_reuseFailAlloc_6949_;
goto v_reusejp_6947_;
}
v_reusejp_6947_:
{
return v___x_6948_;
}
}
}
}
else
{
lean_object* v_a_6952_; lean_object* v___x_6954_; uint8_t v_isShared_6955_; uint8_t v_isSharedCheck_6959_; 
lean_del_object(v___x_6938_);
lean_dec(v_head_6936_);
v_a_6952_ = lean_ctor_get(v___x_6940_, 0);
v_isSharedCheck_6959_ = !lean_is_exclusive(v___x_6940_);
if (v_isSharedCheck_6959_ == 0)
{
v___x_6954_ = v___x_6940_;
v_isShared_6955_ = v_isSharedCheck_6959_;
goto v_resetjp_6953_;
}
else
{
lean_inc(v_a_6952_);
lean_dec(v___x_6940_);
v___x_6954_ = lean_box(0);
v_isShared_6955_ = v_isSharedCheck_6959_;
goto v_resetjp_6953_;
}
v_resetjp_6953_:
{
lean_object* v___x_6957_; 
if (v_isShared_6955_ == 0)
{
v___x_6957_ = v___x_6954_;
goto v_reusejp_6956_;
}
else
{
lean_object* v_reuseFailAlloc_6958_; 
v_reuseFailAlloc_6958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_a_6952_);
v___x_6957_ = v_reuseFailAlloc_6958_;
goto v_reusejp_6956_;
}
v_reusejp_6956_:
{
return v___x_6957_;
}
}
}
}
}
else
{
lean_object* v_head_6962_; lean_object* v___x_6963_; 
lean_inc(v_tail_6935_);
v_head_6962_ = lean_ctor_get(v_a_6927_, 0);
lean_inc(v_head_6962_);
lean_dec_ref_known(v_a_6927_, 2);
v___x_6963_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6935_, v_a_6928_, v_a_6929_, v_a_6930_, v_a_6931_);
if (lean_obj_tag(v___x_6963_) == 0)
{
lean_object* v_a_6964_; lean_object* v_fst_6965_; lean_object* v_snd_6966_; lean_object* v___x_6968_; uint8_t v_isShared_6969_; uint8_t v_isSharedCheck_6994_; 
v_a_6964_ = lean_ctor_get(v___x_6963_, 0);
lean_inc(v_a_6964_);
lean_dec_ref_known(v___x_6963_, 1);
v_fst_6965_ = lean_ctor_get(v_a_6964_, 0);
v_snd_6966_ = lean_ctor_get(v_a_6964_, 1);
v_isSharedCheck_6994_ = !lean_is_exclusive(v_a_6964_);
if (v_isSharedCheck_6994_ == 0)
{
v___x_6968_ = v_a_6964_;
v_isShared_6969_ = v_isSharedCheck_6994_;
goto v_resetjp_6967_;
}
else
{
lean_inc(v_snd_6966_);
lean_inc(v_fst_6965_);
lean_dec(v_a_6964_);
v___x_6968_ = lean_box(0);
v_isShared_6969_ = v_isSharedCheck_6994_;
goto v_resetjp_6967_;
}
v_resetjp_6967_:
{
lean_object* v___x_6970_; 
lean_inc(v_a_6931_);
lean_inc_ref(v_a_6930_);
lean_inc(v_a_6929_);
lean_inc_ref(v_a_6928_);
lean_inc(v_head_6962_);
v___x_6970_ = lean_infer_type(v_head_6962_, v_a_6928_, v_a_6929_, v_a_6930_, v_a_6931_);
if (lean_obj_tag(v___x_6970_) == 0)
{
lean_object* v_a_6971_; lean_object* v___x_6973_; uint8_t v_isShared_6974_; uint8_t v_isSharedCheck_6985_; 
v_a_6971_ = lean_ctor_get(v___x_6970_, 0);
v_isSharedCheck_6985_ = !lean_is_exclusive(v___x_6970_);
if (v_isSharedCheck_6985_ == 0)
{
v___x_6973_ = v___x_6970_;
v_isShared_6974_ = v_isSharedCheck_6985_;
goto v_resetjp_6972_;
}
else
{
lean_inc(v_a_6971_);
lean_dec(v___x_6970_);
v___x_6973_ = lean_box(0);
v_isShared_6974_ = v_isSharedCheck_6985_;
goto v_resetjp_6972_;
}
v_resetjp_6972_:
{
lean_object* v___x_6975_; lean_object* v___x_6976_; lean_object* v___x_6977_; lean_object* v___x_6978_; lean_object* v___x_6980_; 
v___x_6975_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6966_);
lean_inc(v_a_6971_);
v___x_6976_ = l_Lean_mkApp4(v___x_6975_, v_a_6971_, v_snd_6966_, v_head_6962_, v_fst_6965_);
v___x_6977_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6978_ = l_Lean_mkAppB(v___x_6977_, v_a_6971_, v_snd_6966_);
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 1, v___x_6978_);
lean_ctor_set(v___x_6968_, 0, v___x_6976_);
v___x_6980_ = v___x_6968_;
goto v_reusejp_6979_;
}
else
{
lean_object* v_reuseFailAlloc_6984_; 
v_reuseFailAlloc_6984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6984_, 0, v___x_6976_);
lean_ctor_set(v_reuseFailAlloc_6984_, 1, v___x_6978_);
v___x_6980_ = v_reuseFailAlloc_6984_;
goto v_reusejp_6979_;
}
v_reusejp_6979_:
{
lean_object* v___x_6982_; 
if (v_isShared_6974_ == 0)
{
lean_ctor_set(v___x_6973_, 0, v___x_6980_);
v___x_6982_ = v___x_6973_;
goto v_reusejp_6981_;
}
else
{
lean_object* v_reuseFailAlloc_6983_; 
v_reuseFailAlloc_6983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6983_, 0, v___x_6980_);
v___x_6982_ = v_reuseFailAlloc_6983_;
goto v_reusejp_6981_;
}
v_reusejp_6981_:
{
return v___x_6982_;
}
}
}
}
else
{
lean_object* v_a_6986_; lean_object* v___x_6988_; uint8_t v_isShared_6989_; uint8_t v_isSharedCheck_6993_; 
lean_del_object(v___x_6968_);
lean_dec(v_snd_6966_);
lean_dec(v_fst_6965_);
lean_dec(v_head_6962_);
v_a_6986_ = lean_ctor_get(v___x_6970_, 0);
v_isSharedCheck_6993_ = !lean_is_exclusive(v___x_6970_);
if (v_isSharedCheck_6993_ == 0)
{
v___x_6988_ = v___x_6970_;
v_isShared_6989_ = v_isSharedCheck_6993_;
goto v_resetjp_6987_;
}
else
{
lean_inc(v_a_6986_);
lean_dec(v___x_6970_);
v___x_6988_ = lean_box(0);
v_isShared_6989_ = v_isSharedCheck_6993_;
goto v_resetjp_6987_;
}
v_resetjp_6987_:
{
lean_object* v___x_6991_; 
if (v_isShared_6989_ == 0)
{
v___x_6991_ = v___x_6988_;
goto v_reusejp_6990_;
}
else
{
lean_object* v_reuseFailAlloc_6992_; 
v_reuseFailAlloc_6992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6992_, 0, v_a_6986_);
v___x_6991_ = v_reuseFailAlloc_6992_;
goto v_reusejp_6990_;
}
v_reusejp_6990_:
{
return v___x_6991_;
}
}
}
}
}
else
{
lean_dec(v_head_6962_);
return v___x_6963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6995_, lean_object* v_a_6996_, lean_object* v_a_6997_, lean_object* v_a_6998_, lean_object* v_a_6999_, lean_object* v_a_7000_){
_start:
{
lean_object* v_res_7001_; 
v_res_7001_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6995_, v_a_6996_, v_a_6997_, v_a_6998_, v_a_6999_);
lean_dec(v_a_6999_);
lean_dec_ref(v_a_6998_);
lean_dec(v_a_6997_);
lean_dec_ref(v_a_6996_);
return v_res_7001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_7002_, lean_object* v_a_7003_, lean_object* v_a_7004_, lean_object* v_a_7005_, lean_object* v_a_7006_){
_start:
{
lean_object* v___x_7008_; 
v___x_7008_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_7002_, v_a_7003_, v_a_7004_, v_a_7005_, v_a_7006_);
if (lean_obj_tag(v___x_7008_) == 0)
{
lean_object* v_a_7009_; lean_object* v___x_7011_; uint8_t v_isShared_7012_; uint8_t v_isSharedCheck_7017_; 
v_a_7009_ = lean_ctor_get(v___x_7008_, 0);
v_isSharedCheck_7017_ = !lean_is_exclusive(v___x_7008_);
if (v_isSharedCheck_7017_ == 0)
{
v___x_7011_ = v___x_7008_;
v_isShared_7012_ = v_isSharedCheck_7017_;
goto v_resetjp_7010_;
}
else
{
lean_inc(v_a_7009_);
lean_dec(v___x_7008_);
v___x_7011_ = lean_box(0);
v_isShared_7012_ = v_isSharedCheck_7017_;
goto v_resetjp_7010_;
}
v_resetjp_7010_:
{
lean_object* v_fst_7013_; lean_object* v___x_7015_; 
v_fst_7013_ = lean_ctor_get(v_a_7009_, 0);
lean_inc(v_fst_7013_);
lean_dec(v_a_7009_);
if (v_isShared_7012_ == 0)
{
lean_ctor_set(v___x_7011_, 0, v_fst_7013_);
v___x_7015_ = v___x_7011_;
goto v_reusejp_7014_;
}
else
{
lean_object* v_reuseFailAlloc_7016_; 
v_reuseFailAlloc_7016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7016_, 0, v_fst_7013_);
v___x_7015_ = v_reuseFailAlloc_7016_;
goto v_reusejp_7014_;
}
v_reusejp_7014_:
{
return v___x_7015_;
}
}
}
else
{
lean_object* v_a_7018_; lean_object* v___x_7020_; uint8_t v_isShared_7021_; uint8_t v_isSharedCheck_7025_; 
v_a_7018_ = lean_ctor_get(v___x_7008_, 0);
v_isSharedCheck_7025_ = !lean_is_exclusive(v___x_7008_);
if (v_isSharedCheck_7025_ == 0)
{
v___x_7020_ = v___x_7008_;
v_isShared_7021_ = v_isSharedCheck_7025_;
goto v_resetjp_7019_;
}
else
{
lean_inc(v_a_7018_);
lean_dec(v___x_7008_);
v___x_7020_ = lean_box(0);
v_isShared_7021_ = v_isSharedCheck_7025_;
goto v_resetjp_7019_;
}
v_resetjp_7019_:
{
lean_object* v___x_7023_; 
if (v_isShared_7021_ == 0)
{
v___x_7023_ = v___x_7020_;
goto v_reusejp_7022_;
}
else
{
lean_object* v_reuseFailAlloc_7024_; 
v_reuseFailAlloc_7024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7024_, 0, v_a_7018_);
v___x_7023_ = v_reuseFailAlloc_7024_;
goto v_reusejp_7022_;
}
v_reusejp_7022_:
{
return v___x_7023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_7026_, lean_object* v_a_7027_, lean_object* v_a_7028_, lean_object* v_a_7029_, lean_object* v_a_7030_, lean_object* v_a_7031_){
_start:
{
lean_object* v_res_7032_; 
v_res_7032_ = l_Lean_Meta_mkAndIntroN(v_hs_7026_, v_a_7027_, v_a_7028_, v_a_7029_, v_a_7030_);
lean_dec(v_a_7030_);
lean_dec_ref(v_a_7029_);
lean_dec(v_a_7028_);
lean_dec_ref(v_a_7027_);
return v_res_7032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7089_; uint8_t v___x_7090_; lean_object* v___x_7091_; lean_object* v___x_7092_; 
v___x_7089_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7090_ = 0;
v___x_7091_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7092_ = l_Lean_registerTraceClass(v___x_7089_, v___x_7090_, v___x_7091_);
if (lean_obj_tag(v___x_7092_) == 0)
{
lean_object* v___x_7093_; uint8_t v___x_7094_; lean_object* v___x_7095_; 
lean_dec_ref_known(v___x_7092_, 1);
v___x_7093_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7094_ = 1;
v___x_7095_ = l_Lean_registerTraceClass(v___x_7093_, v___x_7094_, v___x_7091_);
if (lean_obj_tag(v___x_7095_) == 0)
{
lean_object* v___x_7096_; lean_object* v___x_7097_; 
lean_dec_ref_known(v___x_7095_, 1);
v___x_7096_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7097_ = l_Lean_registerTraceClass(v___x_7096_, v___x_7094_, v___x_7091_);
return v___x_7097_;
}
else
{
return v___x_7095_;
}
}
else
{
return v___x_7092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7098_){
_start:
{
lean_object* v_res_7099_; 
v_res_7099_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7099_;
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
