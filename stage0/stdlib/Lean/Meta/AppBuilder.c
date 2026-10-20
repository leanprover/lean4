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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
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
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__12 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__12_value;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "noConfusion_of_Nat"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__13 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__13_value;
static const lean_ctor_object l_Lean_Meta_mkNoConfusion___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNoConfusion___closed__13_value),LEAN_SCALAR_PTR_LITERAL(151, 214, 13, 141, 28, 69, 207, 64)}};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__14 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__14_value;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "mkNoConfusion: Missing "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__15 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__15_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__16;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " or "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__17 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__17_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__18;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__19;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.mkNoConfusion"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__20 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__20_value;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 81, .m_data = "assertion violation: arity ≥ xs.size + fields1.size + fields2.size + 3\n          "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__21 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__21_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__22;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "P"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__23 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__23_value;
static const lean_ctor_object l_Lean_Meta_mkNoConfusion___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkNoConfusion___closed__23_value),LEAN_SCALAR_PTR_LITERAL(160, 230, 119, 31, 245, 11, 149, 236)}};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__24 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__24_value;
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
size_t v_x_1980__boxed_1677_; size_t v_x_1981__boxed_1678_; lean_object* v_res_1679_; 
v_x_1980__boxed_1677_ = lean_unbox_usize(v_x_1673_);
lean_dec(v_x_1673_);
v_x_1981__boxed_1678_ = lean_unbox_usize(v_x_1674_);
lean_dec(v_x_1674_);
v_res_1679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1672_, v_x_1980__boxed_1677_, v_x_1981__boxed_1678_, v_x_1675_, v_x_1676_);
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
lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_array_get_size(v_instMVars_1791_);
v___x_1833_ = lean_nat_dec_lt(v___x_1831_, v___x_1832_);
if (v___x_1833_ == 0)
{
goto v___jp_1797_;
}
else
{
lean_object* v___x_1834_; size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1832_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1791_, v___x_1835_, v___x_1836_, v___x_1834_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_dec_ref_known(v___x_1837_, 1);
goto v___jp_1797_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v_f_1789_);
lean_dec(v_methodName_1788_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* v_methodName_1846_, lean_object* v_f_1847_, lean_object* v_args_1848_, lean_object* v_instMVars_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v_methodName_1846_, v_f_1847_, v_args_1848_, v_instMVars_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec_ref(v_instMVars_1849_);
lean_dec_ref(v_args_1848_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object* v_mvarId_1856_, lean_object* v_val_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1856_, v_val_1857_, v___y_1859_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object* v_mvarId_1864_, lean_object* v_val_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(v_mvarId_1864_, v_val_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object* v_00_u03b2_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_x_1873_, v_x_1874_, v_x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, size_t v_x_1879_, size_t v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1878_, v_x_1879_, v_x_1880_, v_x_1881_, v_x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
size_t v_x_2408__boxed_1890_; size_t v_x_2409__boxed_1891_; lean_object* v_res_1892_; 
v_x_2408__boxed_1890_ = lean_unbox_usize(v_x_1886_);
lean_dec(v_x_1886_);
v_x_2409__boxed_1891_ = lean_unbox_usize(v_x_1887_);
lean_dec(v_x_1887_);
v_res_1892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1884_, v_x_1885_, v_x_2408__boxed_1890_, v_x_2409__boxed_1891_, v_x_1888_, v_x_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1893_, lean_object* v_n_1894_, lean_object* v_k_1895_, lean_object* v_v_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1894_, v_k_1895_, v_v_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1898_, size_t v_depth_1899_, lean_object* v_keys_1900_, lean_object* v_vals_1901_, lean_object* v_heq_1902_, lean_object* v_i_1903_, lean_object* v_entries_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1899_, v_keys_1900_, v_vals_1901_, v_i_1903_, v_entries_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1906_, lean_object* v_depth_1907_, lean_object* v_keys_1908_, lean_object* v_vals_1909_, lean_object* v_heq_1910_, lean_object* v_i_1911_, lean_object* v_entries_1912_){
_start:
{
size_t v_depth_boxed_1913_; lean_object* v_res_1914_; 
v_depth_boxed_1913_ = lean_unbox_usize(v_depth_1907_);
lean_dec(v_depth_1907_);
v_res_1914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1906_, v_depth_boxed_1913_, v_keys_1908_, v_vals_1909_, v_heq_1910_, v_i_1911_, v_entries_1912_);
lean_dec_ref(v_vals_1909_);
lean_dec_ref(v_keys_1908_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1916_, v_x_1917_, v_x_1918_, v_x_1919_);
return v___x_1920_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2));
v___x_1926_ = l_Lean_stringToMessageData(v___x_1925_);
return v___x_1926_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4));
v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
return v___x_1929_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7));
v___x_1934_ = l_Lean_MessageData_ofFormat(v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* v_f_1935_, lean_object* v_xs_1936_, lean_object* v_type_1937_, lean_object* v_i_1938_, lean_object* v_j_1939_, lean_object* v_args_1940_, lean_object* v_instMVars_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1947_ = lean_array_get_size(v_xs_1936_);
v___x_1948_ = lean_nat_dec_le(v___x_1947_, v_i_1938_);
if (v___x_1948_ == 0)
{
if (lean_obj_tag(v_type_1937_) == 7)
{
lean_object* v_binderName_1949_; lean_object* v_binderType_1950_; lean_object* v_body_1951_; uint8_t v_binderInfo_1952_; lean_object* v___x_1953_; lean_object* v_d_1954_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; 
v_binderName_1949_ = lean_ctor_get(v_type_1937_, 0);
lean_inc(v_binderName_1949_);
v_binderType_1950_ = lean_ctor_get(v_type_1937_, 1);
lean_inc_ref(v_binderType_1950_);
v_body_1951_ = lean_ctor_get(v_type_1937_, 2);
lean_inc_ref(v_body_1951_);
v_binderInfo_1952_ = lean_ctor_get_uint8(v_type_1937_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1937_, 3);
v___x_1953_ = lean_array_get_size(v_args_1940_);
v_d_1954_ = lean_expr_instantiate_rev_range(v_binderType_1950_, v_j_1939_, v___x_1953_, v_args_1940_);
lean_dec_ref(v_binderType_1950_);
switch(v_binderInfo_1952_)
{
case 1:
{
v___y_1956_ = v_a_1942_;
v___y_1957_ = v_a_1943_;
v___y_1958_ = v_a_1944_;
v___y_1959_ = v_a_1945_;
goto v___jp_1955_;
}
case 2:
{
v___y_1956_ = v_a_1942_;
v___y_1957_ = v_a_1943_;
v___y_1958_ = v_a_1944_;
v___y_1959_ = v_a_1945_;
goto v___jp_1955_;
}
case 3:
{
lean_object* v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_d_1954_);
v___x_1967_ = 1;
v___x_1968_ = l_Lean_Meta_mkFreshExprMVar(v___x_1966_, v___x_1967_, v_binderName_1949_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc_n(v_a_1969_, 2);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = lean_array_push(v_args_1940_, v_a_1969_);
v___x_1971_ = l_Lean_Expr_mvarId_x21(v_a_1969_);
lean_dec(v_a_1969_);
v___x_1972_ = lean_array_push(v_instMVars_1941_, v___x_1971_);
v_type_1937_ = v_body_1951_;
v_args_1940_ = v___x_1970_;
v_instMVars_1941_ = v___x_1972_;
goto _start;
}
else
{
lean_dec_ref(v_body_1951_);
lean_dec_ref(v_instMVars_1941_);
lean_dec_ref(v_args_1940_);
lean_dec(v_j_1939_);
lean_dec(v_i_1938_);
lean_dec_ref(v_f_1935_);
return v___x_1968_;
}
}
default: 
{
lean_object* v_x_1974_; lean_object* v___y_1976_; lean_object* v___x_1993_; 
lean_dec(v_binderName_1949_);
v_x_1974_ = lean_array_fget_borrowed(v_xs_1936_, v_i_1938_);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
lean_inc(v_x_1974_);
v___x_1993_ = lean_infer_type(v_x_1974_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; uint8_t v_transparency_1996_; uint8_t v___x_1997_; uint8_t v___x_1998_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = l_Lean_Meta_Context_config(v_a_1942_);
v_transparency_1996_ = lean_ctor_get_uint8(v___x_1995_, 9);
lean_dec_ref(v___x_1995_);
v___x_1997_ = 1;
v___x_1998_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Meta_isExprDefEq(v_d_1954_, v_a_1994_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
v___y_1976_ = v___x_1999_;
goto v___jp_1975_;
}
else
{
lean_object* v_keyedConfig_2000_; uint8_t v_trackZetaDelta_2001_; lean_object* v_zetaDeltaSet_2002_; lean_object* v_lctx_2003_; lean_object* v_localInstances_2004_; lean_object* v_defEqCtx_x3f_2005_; lean_object* v_synthPendingDepth_2006_; lean_object* v_customCanUnfoldPredicate_x3f_2007_; uint8_t v_univApprox_2008_; uint8_t v_inTypeClassResolution_2009_; uint8_t v_cacheInferType_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_keyedConfig_2000_ = lean_ctor_get(v_a_1942_, 0);
v_trackZetaDelta_2001_ = lean_ctor_get_uint8(v_a_1942_, sizeof(void*)*7);
v_zetaDeltaSet_2002_ = lean_ctor_get(v_a_1942_, 1);
v_lctx_2003_ = lean_ctor_get(v_a_1942_, 2);
v_localInstances_2004_ = lean_ctor_get(v_a_1942_, 3);
v_defEqCtx_x3f_2005_ = lean_ctor_get(v_a_1942_, 4);
v_synthPendingDepth_2006_ = lean_ctor_get(v_a_1942_, 5);
v_customCanUnfoldPredicate_x3f_2007_ = lean_ctor_get(v_a_1942_, 6);
v_univApprox_2008_ = lean_ctor_get_uint8(v_a_1942_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2009_ = lean_ctor_get_uint8(v_a_1942_, sizeof(void*)*7 + 2);
v_cacheInferType_2010_ = lean_ctor_get_uint8(v_a_1942_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2000_);
v___x_2011_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1997_, v_keyedConfig_2000_);
lean_inc(v_customCanUnfoldPredicate_x3f_2007_);
lean_inc(v_synthPendingDepth_2006_);
lean_inc(v_defEqCtx_x3f_2005_);
lean_inc_ref(v_localInstances_2004_);
lean_inc_ref(v_lctx_2003_);
lean_inc(v_zetaDeltaSet_2002_);
v___x_2012_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set(v___x_2012_, 1, v_zetaDeltaSet_2002_);
lean_ctor_set(v___x_2012_, 2, v_lctx_2003_);
lean_ctor_set(v___x_2012_, 3, v_localInstances_2004_);
lean_ctor_set(v___x_2012_, 4, v_defEqCtx_x3f_2005_);
lean_ctor_set(v___x_2012_, 5, v_synthPendingDepth_2006_);
lean_ctor_set(v___x_2012_, 6, v_customCanUnfoldPredicate_x3f_2007_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*7, v_trackZetaDelta_2001_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*7 + 1, v_univApprox_2008_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2009_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*7 + 3, v_cacheInferType_2010_);
v___x_2013_ = l_Lean_Meta_isExprDefEq(v_d_1954_, v_a_1994_, v___x_2012_, v_a_1943_, v_a_1944_, v_a_1945_);
lean_dec_ref_known(v___x_2012_, 7);
v___y_1976_ = v___x_2013_;
goto v___jp_1975_;
}
}
else
{
lean_dec_ref(v_d_1954_);
lean_dec_ref(v_body_1951_);
lean_dec_ref(v_instMVars_1941_);
lean_dec_ref(v_args_1940_);
lean_dec(v_j_1939_);
lean_dec(v_i_1938_);
lean_dec_ref(v_f_1935_);
return v___x_1993_;
}
v___jp_1975_:
{
if (lean_obj_tag(v___y_1976_) == 0)
{
lean_object* v_a_1977_; uint8_t v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___y_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___y_1976_, 1);
v___x_1978_ = lean_unbox(v_a_1977_);
lean_dec(v_a_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v_body_1951_);
lean_dec_ref(v_instMVars_1941_);
lean_dec(v_j_1939_);
lean_dec(v_i_1938_);
v___x_1979_ = l_Lean_mkAppN(v_f_1935_, v_args_1940_);
lean_dec_ref(v_args_1940_);
lean_inc(v_x_1974_);
v___x_1980_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1979_, v_x_1974_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_unsigned_to_nat(1u);
v___x_1982_ = lean_nat_add(v_i_1938_, v___x_1981_);
lean_dec(v_i_1938_);
lean_inc(v_x_1974_);
v___x_1983_ = lean_array_push(v_args_1940_, v_x_1974_);
v_type_1937_ = v_body_1951_;
v_i_1938_ = v___x_1982_;
v_args_1940_ = v___x_1983_;
goto _start;
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v_body_1951_);
lean_dec_ref(v_instMVars_1941_);
lean_dec_ref(v_args_1940_);
lean_dec(v_j_1939_);
lean_dec(v_i_1938_);
lean_dec_ref(v_f_1935_);
v_a_1985_ = lean_ctor_get(v___y_1976_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___y_1976_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___y_1976_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___y_1976_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
v___jp_1955_:
{
lean_object* v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1960_, 0, v_d_1954_);
v___x_1961_ = 0;
v___x_1962_ = l_Lean_Meta_mkFreshExprMVar(v___x_1960_, v___x_1961_, v_binderName_1949_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = lean_array_push(v_args_1940_, v_a_1963_);
v_type_1937_ = v_body_1951_;
v_args_1940_ = v___x_1964_;
v_a_1942_ = v___y_1956_;
v_a_1943_ = v___y_1957_;
v_a_1944_ = v___y_1958_;
v_a_1945_ = v___y_1959_;
goto _start;
}
else
{
lean_dec_ref(v_body_1951_);
lean_dec_ref(v_instMVars_1941_);
lean_dec_ref(v_args_1940_);
lean_dec(v_j_1939_);
lean_dec(v_i_1938_);
lean_dec_ref(v_f_1935_);
return v___x_1962_;
}
}
}
else
{
lean_object* v___x_2014_; lean_object* v_type_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_array_get_size(v_args_1940_);
v_type_2015_ = lean_expr_instantiate_rev_range(v_type_1937_, v_j_1939_, v___x_2014_, v_args_1940_);
lean_dec(v_j_1939_);
lean_dec_ref(v_type_1937_);
v___x_2016_ = l_Lean_Meta_whnfD(v_type_2015_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; uint8_t v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l_Lean_Expr_isForall(v_a_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v_a_2017_);
lean_dec_ref(v_instMVars_1941_);
lean_dec_ref(v_args_1940_);
lean_dec(v_i_1938_);
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2020_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2021_ = l_Lean_indentExpr(v_f_1935_);
v___x_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2020_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2022_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2027_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1936_, v___x_2025_, v___x_2026_);
v___x_2028_ = l_Lean_indentD(v___x_2027_);
v___x_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2024_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_2019_, v___x_2029_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_2030_;
}
else
{
v_type_1937_ = v_a_2017_;
v_j_1939_ = v___x_2014_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1941_);
lean_dec_ref(v_args_1940_);
lean_dec(v_i_1938_);
lean_dec_ref(v_f_1935_);
return v___x_2016_;
}
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec(v_j_1939_);
lean_dec(v_i_1938_);
lean_dec_ref(v_type_1937_);
v___x_2032_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2033_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2032_, v_f_1935_, v_args_1940_, v_instMVars_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
lean_dec_ref(v_instMVars_1941_);
lean_dec_ref(v_args_1940_);
return v___x_2033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* v_f_2034_, lean_object* v_xs_2035_, lean_object* v_type_2036_, lean_object* v_i_2037_, lean_object* v_j_2038_, lean_object* v_args_2039_, lean_object* v_instMVars_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2034_, v_xs_2035_, v_type_2036_, v_i_2037_, v_j_2038_, v_args_2039_, v_instMVars_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec_ref(v_xs_2035_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* v_f_2049_, lean_object* v_fType_2050_, lean_object* v_xs_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_2059_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2049_, v_xs_2051_, v_fType_2050_, v___x_2057_, v___x_2057_, v___x_2058_, v___x_2058_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* v_f_2060_, lean_object* v_fType_2061_, lean_object* v_xs_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_f_2060_, v_fType_2061_, v_xs_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec_ref(v_xs_2062_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object* v_x_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
if (lean_obj_tag(v_x_2069_) == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = l_List_reverse___redArg(v_x_2070_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
else
{
lean_object* v_tail_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2096_; 
v_tail_2078_ = lean_ctor_get(v_x_2069_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_x_2069_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v_x_2069_, 0);
lean_dec(v_unused_2097_);
v___x_2080_ = v_x_2069_;
v_isShared_2081_ = v_isSharedCheck_2096_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_tail_2078_);
lean_dec(v_x_2069_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2096_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_Meta_mkFreshLevelMVar(v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v_x_2070_);
lean_ctor_set(v___x_2080_, 0, v_a_2083_);
v___x_2085_ = v___x_2080_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2083_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_x_2070_);
v___x_2085_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
v_x_2069_ = v_tail_2078_;
v_x_2070_ = v___x_2085_;
goto _start;
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_del_object(v___x_2080_);
lean_dec(v_tail_2078_);
lean_dec(v_x_2070_);
v_a_2088_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2082_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2082_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object* v_x_2098_, lean_object* v_x_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_x_2098_, v_x_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2109_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2110_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
lean_ctor_set(v___x_2112_, 2, v___x_2111_);
lean_ctor_set(v___x_2112_, 3, v___x_2111_);
lean_ctor_set(v___x_2112_, 4, v___x_2110_);
lean_ctor_set(v___x_2112_, 5, v___x_2110_);
lean_ctor_set(v___x_2112_, 6, v___x_2110_);
lean_ctor_set(v___x_2112_, 7, v___x_2110_);
lean_ctor_set(v___x_2112_, 8, v___x_2110_);
lean_ctor_set(v___x_2112_, 9, v___x_2110_);
lean_ctor_set(v___x_2112_, 10, v___x_2110_);
lean_ctor_set(v___x_2112_, 11, v___x_2109_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_unsigned_to_nat(32u);
v___x_2114_ = lean_mk_empty_array_with_capacity(v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2116_ = ((size_t)5ULL);
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = lean_unsigned_to_nat(32u);
v___x_2119_ = lean_mk_empty_array_with_capacity(v___x_2118_);
v___x_2120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2121_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v___x_2119_);
lean_ctor_set(v___x_2121_, 2, v___x_2117_);
lean_ctor_set(v___x_2121_, 3, v___x_2117_);
lean_ctor_set_usize(v___x_2121_, 4, v___x_2116_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2122_ = lean_box(1);
v___x_2123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2123_);
lean_ctor_set(v___x_2125_, 2, v___x_2122_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2128_ = l_Lean_stringToMessageData(v___x_2127_);
return v___x_2128_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2137_ = l_Lean_stringToMessageData(v___x_2136_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2140_ = l_Lean_stringToMessageData(v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2143_ = l_Lean_stringToMessageData(v___x_2142_);
return v___x_2143_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2147_, lean_object* v_declHint_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v_env_2153_; uint8_t v___x_2154_; 
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_st_ref_get(v___y_2149_);
v_env_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc_ref(v_env_2153_);
lean_dec(v___x_2152_);
v___x_2154_ = l_Lean_Name_isAnonymous(v_declHint_2148_);
if (v___x_2154_ == 0)
{
uint8_t v_isExporting_2155_; 
v_isExporting_2155_ = lean_ctor_get_uint8(v_env_2153_, sizeof(void*)*13);
if (v_isExporting_2155_ == 0)
{
lean_object* v___x_2156_; 
lean_dec_ref(v_env_2153_);
lean_dec(v_declHint_2148_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_msg_2147_);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
lean_inc_ref(v_env_2153_);
v___x_2157_ = l_Lean_Environment_setExporting(v_env_2153_, v___x_2154_);
lean_inc(v_declHint_2148_);
lean_inc_ref(v___x_2157_);
v___x_2158_ = l_Lean_Environment_contains(v___x_2157_, v_declHint_2148_, v_isExporting_2155_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
lean_dec_ref(v___x_2157_);
lean_dec_ref(v_env_2153_);
lean_dec(v_declHint_2148_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_msg_2147_);
return v___x_2159_;
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v_c_2165_; lean_object* v___x_2166_; 
v___x_2160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2162_ = l_Lean_Options_empty;
v___x_2163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2157_);
lean_ctor_set(v___x_2163_, 1, v___x_2160_);
lean_ctor_set(v___x_2163_, 2, v___x_2161_);
lean_ctor_set(v___x_2163_, 3, v___x_2162_);
lean_inc(v_declHint_2148_);
v___x_2164_ = l_Lean_MessageData_ofConstName(v_declHint_2148_, v___x_2154_);
v_c_2165_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2165_, 0, v___x_2163_);
lean_ctor_set(v_c_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2153_, v_declHint_2148_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref(v_env_2153_);
lean_dec(v_declHint_2148_);
v___x_2167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v_c_2165_);
v___x_2169_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = l_Lean_MessageData_note(v___x_2170_);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_msg_2147_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
else
{
lean_object* v_val_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2208_; 
v_val_2174_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2176_ = v___x_2166_;
v_isShared_2177_ = v_isSharedCheck_2208_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_val_2174_);
lean_dec(v___x_2166_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2208_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v_moduleNames_2179_; lean_object* v_mod_2180_; uint8_t v___x_2181_; 
v___x_2178_ = l_Lean_Environment_header(v_env_2153_);
lean_dec_ref(v_env_2153_);
v_moduleNames_2179_ = lean_ctor_get(v___x_2178_, 4);
lean_inc_ref(v_moduleNames_2179_);
lean_dec_ref(v___x_2178_);
v_mod_2180_ = lean_array_get(v___x_2151_, v_moduleNames_2179_, v_val_2174_);
lean_dec(v_val_2174_);
lean_dec_ref(v_moduleNames_2179_);
v___x_2181_ = l_Lean_isPrivateName(v_declHint_2148_);
lean_dec(v_declHint_2148_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2182_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v_c_2165_);
v___x_2184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = l_Lean_MessageData_ofName(v_mod_2180_);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_MessageData_note(v___x_2189_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v_msg_2147_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2191_);
v___x_2193_ = v___x_2176_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v_c_2165_);
v___x_2197_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = l_Lean_MessageData_ofName(v_mod_2180_);
v___x_2200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = l_Lean_MessageData_note(v___x_2202_);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v_msg_2147_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2204_);
v___x_2206_ = v___x_2176_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2209_; 
lean_dec_ref(v_env_2153_);
lean_dec(v_declHint_2148_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_msg_2147_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2210_, lean_object* v_declHint_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2210_, v_declHint_2211_, v___y_2212_);
lean_dec(v___y_2212_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_2215_, lean_object* v_declHint_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2232_; 
v___x_2222_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2215_, v_declHint_2216_, v___y_2220_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2232_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2232_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2227_ = l_Lean_unknownIdentifierMessageTag;
v___x_2228_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v_a_2223_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2228_);
v___x_2230_ = v___x_2225_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_2233_, lean_object* v_declHint_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2233_, v_declHint_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_2241_, lean_object* v_msg_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_toCold_2248_; lean_object* v_currRecDepth_2249_; lean_object* v_ref_2250_; uint16_t v_optionFlags_2251_; uint8_t v_suppressElabErrors_2252_; uint8_t v_isRecordingDeps_2253_; lean_object* v_ref_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v_toCold_2248_ = lean_ctor_get(v___y_2245_, 0);
v_currRecDepth_2249_ = lean_ctor_get(v___y_2245_, 1);
v_ref_2250_ = lean_ctor_get(v___y_2245_, 2);
v_optionFlags_2251_ = lean_ctor_get_uint16(v___y_2245_, sizeof(void*)*3);
v_suppressElabErrors_2252_ = lean_ctor_get_uint8(v___y_2245_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2253_ = lean_ctor_get_uint8(v___y_2245_, sizeof(void*)*3 + 3);
v_ref_2254_ = l_Lean_replaceRef(v_ref_2241_, v_ref_2250_);
lean_inc(v_currRecDepth_2249_);
lean_inc_ref(v_toCold_2248_);
v___x_2255_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2255_, 0, v_toCold_2248_);
lean_ctor_set(v___x_2255_, 1, v_currRecDepth_2249_);
lean_ctor_set(v___x_2255_, 2, v_ref_2254_);
lean_ctor_set_uint16(v___x_2255_, sizeof(void*)*3, v_optionFlags_2251_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*3 + 2, v_suppressElabErrors_2252_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*3 + 3, v_isRecordingDeps_2253_);
v___x_2256_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2242_, v___y_2243_, v___y_2244_, v___x_2255_, v___y_2246_);
lean_dec_ref_known(v___x_2255_, 3);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2257_, lean_object* v_msg_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2257_, v_msg_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v_ref_2257_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2265_, lean_object* v_msg_2266_, lean_object* v_declHint_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v_a_2274_; lean_object* v___x_2275_; 
v___x_2273_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2266_, v_declHint_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2265_, v_a_2274_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2276_, lean_object* v_msg_2277_, lean_object* v_declHint_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2276_, v_msg_2277_, v_declHint_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v_ref_2276_);
return v_res_2284_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2287_ = l_Lean_stringToMessageData(v___x_2286_);
return v___x_2287_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2290_ = l_Lean_stringToMessageData(v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2291_, lean_object* v_constName_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2298_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2299_ = 0;
lean_inc(v_constName_2292_);
v___x_2300_ = l_Lean_MessageData_ofConstName(v_constName_2292_, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2298_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2291_, v___x_2303_, v_constName_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2305_, lean_object* v_constName_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2305_, v_constName_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v_ref_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_ref_2319_; lean_object* v___x_2320_; 
v_ref_2319_ = lean_ctor_get(v___y_2316_, 2);
v___x_2320_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2319_, v_constName_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; lean_object* v_env_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; 
v___x_2334_ = lean_st_ref_get(v___y_2332_);
v_env_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc_ref(v_env_2335_);
lean_dec(v___x_2334_);
v___x_2336_ = 0;
lean_inc(v_constName_2328_);
v___x_2337_ = l_Lean_Environment_findConstVal_x3f(v_env_2335_, v_constName_2328_, v___x_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v___x_2338_;
}
else
{
lean_object* v_val_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_constName_2328_);
v_val_2339_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2337_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_val_2339_);
lean_dec(v___x_2337_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 0);
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_val_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; 
lean_inc(v_constName_2354_);
v___x_2360_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v_levelParams_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v_levelParams_2362_ = lean_ctor_get(v_a_2361_, 1);
v___x_2363_ = lean_box(0);
lean_inc(v_levelParams_2362_);
v___x_2364_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2362_, v___x_2363_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc_n(v_a_2365_, 2);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = l_Lean_mkConst(v_constName_2354_, v_a_2365_);
v___x_2367_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2361_, v_a_2365_, v_a_2358_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2376_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2376_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2376_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2366_);
lean_ctor_set(v___x_2372_, 1, v_a_2368_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2372_);
v___x_2374_ = v___x_2370_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec_ref(v___x_2366_);
v_a_2377_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2367_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2367_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_a_2361_);
lean_dec(v_constName_2354_);
v_a_2385_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2364_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2364_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_constName_2354_);
v_a_2393_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2360_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2360_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2408_, lean_object* v_constName_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2416_, lean_object* v_constName_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2416_, v_constName_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2424_, lean_object* v_ref_2425_, lean_object* v_constName_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2425_, v_constName_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2433_, lean_object* v_ref_2434_, lean_object* v_constName_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2433_, v_ref_2434_, v_constName_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v_ref_2434_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2442_, lean_object* v_ref_2443_, lean_object* v_msg_2444_, lean_object* v_declHint_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2443_, v_msg_2444_, v_declHint_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_ref_2453_, lean_object* v_msg_2454_, lean_object* v_declHint_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2452_, v_ref_2453_, v_msg_2454_, v_declHint_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v_ref_2453_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2462_, lean_object* v_declHint_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2462_, v_declHint_2463_, v___y_2467_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2470_, lean_object* v_declHint_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2470_, v_declHint_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2478_, lean_object* v_ref_2479_, lean_object* v_msg_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2479_, v_msg_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2487_, lean_object* v_ref_2488_, lean_object* v_msg_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2487_, v_ref_2488_, v_msg_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v_ref_2488_);
return v_res_2495_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2498_ = l_Lean_stringToMessageData(v___x_2497_);
return v___x_2498_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2501_ = l_Lean_stringToMessageData(v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2502_, lean_object* v_f_2503_, lean_object* v_inst_2504_, lean_object* v_xs_2505_, lean_object* v_x_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2512_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2513_ = lean_apply_1(v_inst_2502_, v_f_2503_);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_apply_1(v_inst_2504_, v_xs_2505_);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2520_, lean_object* v_f_2521_, lean_object* v_inst_2522_, lean_object* v_xs_2523_, lean_object* v_x_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2520_, v_f_2521_, v_inst_2522_, v_xs_2523_, v_x_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v_x_2524_);
return v_res_2530_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_instMonadEIO___redArg();
return v___x_2531_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2533_ = l_StateRefT_x27_instMonad___redArg(v___x_2532_);
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2541_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2542_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2541_, v___x_2540_);
return v___x_2542_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___f_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2544_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2545_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2544_, v___x_2543_);
return v___x_2545_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2549_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2551_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2550_, v___x_2549_, v___x_2548_);
return v___x_2551_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___f_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; 
v___x_2552_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2553_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2554_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2555_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2554_, v___f_2553_, v___x_2552_);
return v___x_2555_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_instMonadExceptOfEIO___redArg();
return v___x_2556_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2558_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2557_);
return v___x_2558_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2560_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2559_);
return v___x_2560_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2562_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2561_);
return v___x_2562_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2564_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2563_);
return v___x_2564_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2576_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2577_ = l_Lean_Name_append(v___x_2576_, v___x_2575_);
return v___x_2577_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2584_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2585_ = l_Lean_Name_append(v___x_2584_, v___x_2583_);
return v___x_2585_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2586_; double v___x_2587_; 
v___x_2586_ = lean_unsigned_to_nat(1000000000u);
v___x_2587_ = lean_float_of_nat(v___x_2586_);
return v___x_2587_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2594_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2595_ = l_Lean_Name_append(v___x_2594_, v___x_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_f_2598_, lean_object* v_xs_2599_, lean_object* v_k_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2606_; lean_object* v_toApplicative_2607_; lean_object* v_toFunctor_2608_; lean_object* v_toSeq_2609_; lean_object* v_toSeqLeft_2610_; lean_object* v_toSeqRight_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___x_2616_; lean_object* v___f_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v_toApplicative_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2846_; 
v___x_2606_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2607_ = lean_ctor_get(v___x_2606_, 0);
v_toFunctor_2608_ = lean_ctor_get(v_toApplicative_2607_, 0);
v_toSeq_2609_ = lean_ctor_get(v_toApplicative_2607_, 2);
v_toSeqLeft_2610_ = lean_ctor_get(v_toApplicative_2607_, 3);
v_toSeqRight_2611_ = lean_ctor_get(v_toApplicative_2607_, 4);
v___f_2612_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2613_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2608_, 2);
v___f_2614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2614_, 0, v_toFunctor_2608_);
v___f_2615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2615_, 0, v_toFunctor_2608_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___f_2614_);
lean_ctor_set(v___x_2616_, 1, v___f_2615_);
lean_inc(v_toSeqRight_2611_);
v___f_2617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2617_, 0, v_toSeqRight_2611_);
lean_inc(v_toSeqLeft_2610_);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toSeqLeft_2610_);
lean_inc(v_toSeq_2609_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toSeq_2609_);
v___x_2620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2616_);
lean_ctor_set(v___x_2620_, 1, v___f_2612_);
lean_ctor_set(v___x_2620_, 2, v___f_2619_);
lean_ctor_set(v___x_2620_, 3, v___f_2618_);
lean_ctor_set(v___x_2620_, 4, v___f_2617_);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___f_2613_);
v___x_2622_ = l_StateRefT_x27_instMonad___redArg(v___x_2621_);
v_toApplicative_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2622_, 1);
lean_dec(v_unused_2847_);
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2846_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_toApplicative_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2846_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_toFunctor_2627_; lean_object* v_toSeq_2628_; lean_object* v_toSeqLeft_2629_; lean_object* v_toSeqRight_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2844_; 
v_toFunctor_2627_ = lean_ctor_get(v_toApplicative_2623_, 0);
v_toSeq_2628_ = lean_ctor_get(v_toApplicative_2623_, 2);
v_toSeqLeft_2629_ = lean_ctor_get(v_toApplicative_2623_, 3);
v_toSeqRight_2630_ = lean_ctor_get(v_toApplicative_2623_, 4);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_toApplicative_2623_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v_toApplicative_2623_, 1);
lean_dec(v_unused_2845_);
v___x_2632_ = v_toApplicative_2623_;
v_isShared_2633_ = v_isSharedCheck_2844_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_toSeqRight_2630_);
lean_inc(v_toSeqLeft_2629_);
lean_inc(v_toSeq_2628_);
lean_inc(v_toFunctor_2627_);
lean_dec(v_toApplicative_2623_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2844_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___f_2634_; lean_object* v___f_2635_; lean_object* v___f_2636_; lean_object* v___f_2637_; lean_object* v___x_2638_; lean_object* v___f_2639_; lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___x_2643_; 
v___f_2634_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2635_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2627_);
v___f_2636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2636_, 0, v_toFunctor_2627_);
v___f_2637_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2637_, 0, v_toFunctor_2627_);
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___f_2636_);
lean_ctor_set(v___x_2638_, 1, v___f_2637_);
v___f_2639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2639_, 0, v_toSeqRight_2630_);
v___f_2640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2640_, 0, v_toSeqLeft_2629_);
v___f_2641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2641_, 0, v_toSeq_2628_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 4, v___f_2639_);
lean_ctor_set(v___x_2632_, 3, v___f_2640_);
lean_ctor_set(v___x_2632_, 2, v___f_2641_);
lean_ctor_set(v___x_2632_, 1, v___f_2634_);
lean_ctor_set(v___x_2632_, 0, v___x_2638_);
v___x_2643_ = v___x_2632_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___f_2634_);
lean_ctor_set(v_reuseFailAlloc_2843_, 2, v___f_2641_);
lean_ctor_set(v_reuseFailAlloc_2843_, 3, v___f_2640_);
lean_ctor_set(v_reuseFailAlloc_2843_, 4, v___f_2639_);
v___x_2643_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2645_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v___f_2635_);
lean_ctor_set(v___x_2625_, 0, v___x_2643_);
v___x_2645_ = v___x_2625_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___f_2635_);
v___x_2645_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_toMonadRef_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v_toCold_2651_; lean_object* v_options_2652_; uint8_t v_hasTrace_2653_; 
v___x_2646_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2647_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2648_ = lean_ctor_get(v___x_2647_, 0);
v___x_2649_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2650_ = l_Lean_KVMap_instValueBool;
v_toCold_2651_ = lean_ctor_get(v_a_2603_, 0);
v_options_2652_ = lean_ctor_get(v_toCold_2651_, 2);
v_hasTrace_2653_ = lean_ctor_get_uint8(v_options_2652_, sizeof(void*)*1);
if (v_hasTrace_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_dec_ref(v___x_2645_);
lean_dec(v_xs_2599_);
lean_dec(v_f_2598_);
lean_dec_ref(v_inst_2597_);
lean_dec_ref(v_inst_2596_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2654_ = lean_apply_5(v_k_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2654_) == 0)
{
return v___x_2654_;
}
else
{
lean_object* v_a_2655_; uint8_t v___x_2656_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
v___x_2656_ = l_Lean_Exception_isInterrupt(v_a_2655_);
if (v___x_2656_ == 0)
{
uint8_t v___x_2657_; 
lean_inc(v_a_2655_);
v___x_2657_ = l_Lean_Exception_isRuntime(v_a_2655_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2654_, 0);
lean_dec(v_unused_2665_);
v___x_2659_ = v___x_2654_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_dec(v___x_2654_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2655_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
lean_dec(v_a_2655_);
return v___x_2654_;
}
}
else
{
lean_dec(v_a_2655_);
return v___x_2654_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2666_; lean_object* v___x_2667_; lean_object* v___y_2669_; lean_object* v_a_2670_; lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v_a_2705_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v_a_2721_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v_a_2726_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v_a_2731_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v_a_2744_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v_a_2757_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v_a_2762_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v_a_2767_; 
v_inheritedTraceOptions_2666_ = lean_ctor_get(v_toCold_2651_, 11);
v___x_2667_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2696_, 0, v_inst_2596_);
lean_closure_set(v___f_2696_, 1, v_f_2598_);
lean_closure_set(v___f_2696_, 2, v_inst_2597_);
lean_closure_set(v___f_2696_, 3, v_xs_2599_);
v___f_2697_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2698_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2700_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2701_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2666_, v_options_2652_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2814_ = l_Lean_trace_profiler;
v___x_2815_ = l_Lean_Option_get___redArg(v___x_2650_, v_options_2652_, v___x_2814_);
v___x_2816_ = lean_unbox(v___x_2815_);
lean_dec(v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
lean_dec_ref(v___f_2696_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2817_ = lean_apply_5(v_k_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2820_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2666_, v_options_2652_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_dec(v_a_2818_);
lean_dec_ref(v___x_2645_);
return v___x_2817_;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_8887__overap_2823_; lean_object* v___x_2824_; 
lean_dec_ref_known(v___x_2817_, 1);
lean_inc(v_a_2818_);
v___x_2822_ = l_Lean_MessageData_ofExpr(v_a_2818_);
lean_inc_ref(v_toMonadRef_2648_);
lean_inc_ref(v___x_2645_);
v___x_8887__overap_2823_ = l_Lean_addTrace___redArg(v___x_2645_, v___x_2646_, v_toMonadRef_2648_, v___x_2667_, v___x_2819_, v___x_2822_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2824_ = lean_apply_5(v___x_8887__overap_2823_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec_ref(v___x_2645_);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; 
v_unused_2832_ = lean_ctor_get(v___x_2824_, 0);
lean_dec(v_unused_2832_);
v___x_2826_ = v___x_2824_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_dec(v___x_2824_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_a_2818_);
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2818_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2818_);
v_a_2833_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2824_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2824_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
lean_inc(v_a_2833_);
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
v___y_2669_ = v___x_2838_;
v_a_2670_ = v_a_2833_;
goto v___jp_2668_;
}
}
}
}
}
else
{
lean_object* v_a_2841_; 
v_a_2841_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2841_);
v___y_2669_ = v___x_2817_;
v_a_2670_ = v_a_2841_;
goto v___jp_2668_;
}
}
else
{
goto v___jp_2777_;
}
}
else
{
goto v___jp_2777_;
}
v___jp_2668_:
{
uint8_t v___x_2671_; 
v___x_2671_ = l_Lean_Exception_isInterrupt(v_a_2670_);
if (v___x_2671_ == 0)
{
uint8_t v___x_2672_; 
lean_inc_ref(v_a_2670_);
v___x_2672_ = l_Lean_Exception_isRuntime(v_a_2670_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
lean_dec_ref(v___y_2669_);
v___x_2673_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2674_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2666_, v_options_2652_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; 
lean_dec_ref(v___x_2645_);
v___x_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2676_, 0, v_a_2670_);
return v___x_2676_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_8704__overap_2678_; lean_object* v___x_2679_; 
lean_inc_ref(v_a_2670_);
v___x_2677_ = l_Lean_Exception_toMessageData(v_a_2670_);
lean_inc_ref(v_toMonadRef_2648_);
v___x_8704__overap_2678_ = l_Lean_addTrace___redArg(v___x_2645_, v___x_2646_, v_toMonadRef_2648_, v___x_2667_, v___x_2673_, v___x_2677_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2679_ = lean_apply_5(v___x_8704__overap_2678_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v___x_2679_, 0);
lean_dec(v_unused_2687_);
v___x_2681_ = v___x_2679_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v___x_2679_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 1);
lean_ctor_set(v___x_2681_, 0, v_a_2670_);
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2670_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v_a_2670_);
v_a_2688_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2679_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2679_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_2670_);
lean_dec_ref(v___x_2645_);
return v___y_2669_;
}
}
else
{
lean_dec_ref(v_a_2670_);
lean_dec_ref(v___x_2645_);
return v___y_2669_;
}
}
v___jp_2702_:
{
lean_object* v___x_2706_; double v___x_2707_; double v___x_2708_; double v___x_2709_; double v___x_2710_; double v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_8763__overap_2716_; lean_object* v___x_2717_; 
v___x_2706_ = lean_io_mono_nanos_now();
v___x_2707_ = lean_float_of_nat(v___y_2703_);
v___x_2708_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2709_ = lean_float_div(v___x_2707_, v___x_2708_);
v___x_2710_ = lean_float_of_nat(v___x_2706_);
v___x_2711_ = lean_float_div(v___x_2710_, v___x_2708_);
v___x_2712_ = lean_box_float(v___x_2709_);
v___x_2713_ = lean_box_float(v___x_2711_);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_a_2705_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
lean_inc_ref(v_toMonadRef_2648_);
v___x_8763__overap_2716_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2645_, v___x_2646_, v_toMonadRef_2648_, v___x_2667_, lean_box(0), v___x_2649_, v___f_2697_, v___x_2698_, v_hasTrace_2653_, v___x_2699_, v_options_2652_, v___x_2701_, v___y_2704_, v___f_2696_, v___x_2715_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2717_ = lean_apply_5(v___x_8763__overap_2716_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
return v___x_2717_;
}
v___jp_2718_:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2722_, 0, v_a_2721_);
v___y_2703_ = v___y_2719_;
v___y_2704_ = v___y_2720_;
v_a_2705_ = v___x_2722_;
goto v___jp_2702_;
}
v___jp_2723_:
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_a_2726_);
v___y_2703_ = v___y_2724_;
v___y_2704_ = v___y_2725_;
v_a_2705_ = v___x_2727_;
goto v___jp_2702_;
}
v___jp_2728_:
{
uint8_t v___x_2732_; 
v___x_2732_ = l_Lean_Exception_isInterrupt(v_a_2731_);
if (v___x_2732_ == 0)
{
uint8_t v___x_2733_; 
lean_inc_ref(v_a_2731_);
v___x_2733_ = l_Lean_Exception_isRuntime(v_a_2731_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2734_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2735_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2666_, v_options_2652_, v___x_2735_);
if (v___x_2736_ == 0)
{
v___y_2724_ = v___y_2729_;
v___y_2725_ = v___y_2730_;
v_a_2726_ = v_a_2731_;
goto v___jp_2723_;
}
else
{
lean_object* v___x_2737_; lean_object* v___x_8782__overap_2738_; lean_object* v___x_2739_; 
lean_inc_ref(v_a_2731_);
v___x_2737_ = l_Lean_Exception_toMessageData(v_a_2731_);
lean_inc_ref(v_toMonadRef_2648_);
lean_inc_ref(v___x_2645_);
v___x_8782__overap_2738_ = l_Lean_addTrace___redArg(v___x_2645_, v___x_2646_, v_toMonadRef_2648_, v___x_2667_, v___x_2734_, v___x_2737_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2739_ = lean_apply_5(v___x_8782__overap_2738_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_dec_ref_known(v___x_2739_, 1);
v___y_2724_ = v___y_2729_;
v___y_2725_ = v___y_2730_;
v_a_2726_ = v_a_2731_;
goto v___jp_2723_;
}
else
{
lean_object* v_a_2740_; 
lean_dec_ref(v_a_2731_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v___y_2724_ = v___y_2729_;
v___y_2725_ = v___y_2730_;
v_a_2726_ = v_a_2740_;
goto v___jp_2723_;
}
}
}
else
{
v___y_2724_ = v___y_2729_;
v___y_2725_ = v___y_2730_;
v_a_2726_ = v_a_2731_;
goto v___jp_2723_;
}
}
else
{
v___y_2724_ = v___y_2729_;
v___y_2725_ = v___y_2730_;
v_a_2726_ = v_a_2731_;
goto v___jp_2723_;
}
}
v___jp_2741_:
{
lean_object* v___x_2745_; double v___x_2746_; double v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_8823__overap_2752_; lean_object* v___x_2753_; 
v___x_2745_ = lean_io_get_num_heartbeats();
v___x_2746_ = lean_float_of_nat(v___y_2743_);
v___x_2747_ = lean_float_of_nat(v___x_2745_);
v___x_2748_ = lean_box_float(v___x_2746_);
v___x_2749_ = lean_box_float(v___x_2747_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_a_2744_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
lean_inc_ref(v_toMonadRef_2648_);
v___x_8823__overap_2752_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2645_, v___x_2646_, v_toMonadRef_2648_, v___x_2667_, lean_box(0), v___x_2649_, v___f_2697_, v___x_2698_, v_hasTrace_2653_, v___x_2699_, v_options_2652_, v___x_2701_, v___y_2742_, v___f_2696_, v___x_2751_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2753_ = lean_apply_5(v___x_8823__overap_2752_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
return v___x_2753_;
}
v___jp_2754_:
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_a_2757_);
v___y_2742_ = v___y_2755_;
v___y_2743_ = v___y_2756_;
v_a_2744_ = v___x_2758_;
goto v___jp_2741_;
}
v___jp_2759_:
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_a_2762_);
v___y_2742_ = v___y_2760_;
v___y_2743_ = v___y_2761_;
v_a_2744_ = v___x_2763_;
goto v___jp_2741_;
}
v___jp_2764_:
{
uint8_t v___x_2768_; 
v___x_2768_ = l_Lean_Exception_isInterrupt(v_a_2767_);
if (v___x_2768_ == 0)
{
uint8_t v___x_2769_; 
lean_inc_ref(v_a_2767_);
v___x_2769_ = l_Lean_Exception_isRuntime(v_a_2767_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2770_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2771_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2772_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2666_, v_options_2652_, v___x_2771_);
if (v___x_2772_ == 0)
{
v___y_2760_ = v___y_2765_;
v___y_2761_ = v___y_2766_;
v_a_2762_ = v_a_2767_;
goto v___jp_2759_;
}
else
{
lean_object* v___x_2773_; lean_object* v___x_8842__overap_2774_; lean_object* v___x_2775_; 
lean_inc_ref(v_a_2767_);
v___x_2773_ = l_Lean_Exception_toMessageData(v_a_2767_);
lean_inc_ref(v_toMonadRef_2648_);
lean_inc_ref(v___x_2645_);
v___x_8842__overap_2774_ = l_Lean_addTrace___redArg(v___x_2645_, v___x_2646_, v_toMonadRef_2648_, v___x_2667_, v___x_2770_, v___x_2773_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2775_ = lean_apply_5(v___x_8842__overap_2774_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_dec_ref_known(v___x_2775_, 1);
v___y_2760_ = v___y_2765_;
v___y_2761_ = v___y_2766_;
v_a_2762_ = v_a_2767_;
goto v___jp_2759_;
}
else
{
lean_object* v_a_2776_; 
lean_dec_ref(v_a_2767_);
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___y_2760_ = v___y_2765_;
v___y_2761_ = v___y_2766_;
v_a_2762_ = v_a_2776_;
goto v___jp_2759_;
}
}
}
else
{
v___y_2760_ = v___y_2765_;
v___y_2761_ = v___y_2766_;
v_a_2762_ = v_a_2767_;
goto v___jp_2759_;
}
}
else
{
v___y_2760_ = v___y_2765_;
v___y_2761_ = v___y_2766_;
v_a_2762_ = v_a_2767_;
goto v___jp_2759_;
}
}
v___jp_2777_:
{
lean_object* v___x_8741__overap_2778_; lean_object* v___x_2779_; 
lean_inc_ref(v___x_2645_);
v___x_8741__overap_2778_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2645_, v___x_2646_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2779_ = lean_apply_5(v___x_8741__overap_2778_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2781_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2782_ = l_Lean_Option_get___redArg(v___x_2650_, v_options_2652_, v___x_2781_);
v___x_2783_ = lean_unbox(v___x_2782_);
lean_dec(v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_io_mono_nanos_now();
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2785_ = lean_apply_5(v_k_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2666_, v_options_2652_, v___x_2788_);
if (v___x_2789_ == 0)
{
v___y_2719_ = v___x_2784_;
v___y_2720_ = v_a_2780_;
v_a_2721_ = v_a_2786_;
goto v___jp_2718_;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_8803__overap_2791_; lean_object* v___x_2792_; 
lean_inc(v_a_2786_);
v___x_2790_ = l_Lean_MessageData_ofExpr(v_a_2786_);
lean_inc_ref(v_toMonadRef_2648_);
lean_inc_ref(v___x_2645_);
v___x_8803__overap_2791_ = l_Lean_addTrace___redArg(v___x_2645_, v___x_2646_, v_toMonadRef_2648_, v___x_2667_, v___x_2787_, v___x_2790_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2792_ = lean_apply_5(v___x_8803__overap_2791_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_dec_ref_known(v___x_2792_, 1);
v___y_2719_ = v___x_2784_;
v___y_2720_ = v_a_2780_;
v_a_2721_ = v_a_2786_;
goto v___jp_2718_;
}
else
{
lean_object* v_a_2793_; 
lean_dec(v_a_2786_);
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v___y_2729_ = v___x_2784_;
v___y_2730_ = v_a_2780_;
v_a_2731_ = v_a_2793_;
goto v___jp_2728_;
}
}
}
else
{
lean_object* v_a_2794_; 
v_a_2794_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2785_, 1);
v___y_2729_ = v___x_2784_;
v___y_2730_ = v_a_2780_;
v_a_2731_ = v_a_2794_;
goto v___jp_2728_;
}
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2796_ = lean_apply_5(v_k_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2799_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2800_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2666_, v_options_2652_, v___x_2799_);
if (v___x_2800_ == 0)
{
v___y_2755_ = v_a_2780_;
v___y_2756_ = v___x_2795_;
v_a_2757_ = v_a_2797_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2801_; lean_object* v___x_8863__overap_2802_; lean_object* v___x_2803_; 
lean_inc(v_a_2797_);
v___x_2801_ = l_Lean_MessageData_ofExpr(v_a_2797_);
lean_inc_ref(v_toMonadRef_2648_);
lean_inc_ref(v___x_2645_);
v___x_8863__overap_2802_ = l_Lean_addTrace___redArg(v___x_2645_, v___x_2646_, v_toMonadRef_2648_, v___x_2667_, v___x_2798_, v___x_2801_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
v___x_2803_ = lean_apply_5(v___x_8863__overap_2802_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, lean_box(0));
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_dec_ref_known(v___x_2803_, 1);
v___y_2755_ = v_a_2780_;
v___y_2756_ = v___x_2795_;
v_a_2757_ = v_a_2797_;
goto v___jp_2754_;
}
else
{
lean_object* v_a_2804_; 
lean_dec(v_a_2797_);
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___y_2765_ = v_a_2780_;
v___y_2766_ = v___x_2795_;
v_a_2767_ = v_a_2804_;
goto v___jp_2764_;
}
}
}
else
{
lean_object* v_a_2805_; 
v_a_2805_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2796_, 1);
v___y_2765_ = v_a_2780_;
v___y_2766_ = v___x_2795_;
v_a_2767_ = v_a_2805_;
goto v___jp_2764_;
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref(v___f_2696_);
lean_dec_ref(v___x_2645_);
lean_dec_ref(v_k_2600_);
v_a_2806_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2779_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2779_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_f_2850_, lean_object* v_xs_2851_, lean_object* v_k_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2848_, v_inst_2849_, v_f_2850_, v_xs_2851_, v_k_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2859_, lean_object* v_00_u03b2_2860_, lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_f_2863_, lean_object* v_xs_2864_, lean_object* v_k_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2861_, v_inst_2862_, v_f_2863_, v_xs_2864_, v_k_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2872_, lean_object* v_00_u03b2_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_f_2876_, lean_object* v_xs_2877_, lean_object* v_k_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2872_, v_00_u03b2_2873_, v_inst_2874_, v_inst_2875_, v_f_2876_, v_xs_2877_, v_k_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2885_, uint8_t v_allowLevelAssignments_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2886_, v_k_2885_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
v_a_2901_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2892_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2892_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2909_, lean_object* v_allowLevelAssignments_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2916_; lean_object* v_res_2917_; 
v_allowLevelAssignments_boxed_2916_ = lean_unbox(v_allowLevelAssignments_2910_);
v_res_2917_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2909_, v_allowLevelAssignments_boxed_2916_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2918_, lean_object* v_k_2919_, uint8_t v_allowLevelAssignments_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2919_, v_allowLevelAssignments_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2927_, lean_object* v_k_2928_, lean_object* v_allowLevelAssignments_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2935_; lean_object* v_res_2936_; 
v_allowLevelAssignments_boxed_2935_ = lean_unbox(v_allowLevelAssignments_2929_);
v_res_2936_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2927_, v_k_2928_, v_allowLevelAssignments_boxed_2935_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2937_, lean_object* v_xs_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2937_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v_fst_2946_; lean_object* v_snd_2947_; lean_object* v___x_2948_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
v_fst_2946_ = lean_ctor_get(v_a_2945_, 0);
lean_inc(v_fst_2946_);
v_snd_2947_ = lean_ctor_get(v_a_2945_, 1);
lean_inc(v_snd_2947_);
lean_dec(v_a_2945_);
v___x_2948_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2946_, v_snd_2947_, v_xs_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
return v___x_2948_;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_a_2949_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2944_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2944_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2957_, lean_object* v_xs_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2957_, v_xs_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v_xs_2958_);
return v_res_2964_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = lean_unsigned_to_nat(32u);
v___x_2966_ = lean_mk_empty_array_with_capacity(v___x_2965_);
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
return v___x_2967_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2968_ = ((size_t)5ULL);
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = lean_unsigned_to_nat(32u);
v___x_2971_ = lean_mk_empty_array_with_capacity(v___x_2970_);
v___x_2972_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2973_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v___x_2971_);
lean_ctor_set(v___x_2973_, 2, v___x_2969_);
lean_ctor_set(v___x_2973_, 3, v___x_2969_);
lean_ctor_set_usize(v___x_2973_, 4, v___x_2968_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; lean_object* v_traceState_2977_; lean_object* v_traces_2978_; lean_object* v___x_2979_; lean_object* v_traceState_2980_; lean_object* v_env_2981_; lean_object* v_nextMacroScope_2982_; lean_object* v_ngen_2983_; lean_object* v_auxDeclNGen_2984_; lean_object* v_cache_2985_; lean_object* v_recordedDeps_2986_; lean_object* v_messages_2987_; lean_object* v_infoState_2988_; lean_object* v_snapshotTasks_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3008_; 
v___x_2976_ = lean_st_ref_get(v___y_2974_);
v_traceState_2977_ = lean_ctor_get(v___x_2976_, 4);
lean_inc_ref(v_traceState_2977_);
lean_dec(v___x_2976_);
v_traces_2978_ = lean_ctor_get(v_traceState_2977_, 0);
lean_inc_ref(v_traces_2978_);
lean_dec_ref(v_traceState_2977_);
v___x_2979_ = lean_st_ref_take(v___y_2974_);
v_traceState_2980_ = lean_ctor_get(v___x_2979_, 4);
v_env_2981_ = lean_ctor_get(v___x_2979_, 0);
v_nextMacroScope_2982_ = lean_ctor_get(v___x_2979_, 1);
v_ngen_2983_ = lean_ctor_get(v___x_2979_, 2);
v_auxDeclNGen_2984_ = lean_ctor_get(v___x_2979_, 3);
v_cache_2985_ = lean_ctor_get(v___x_2979_, 5);
v_recordedDeps_2986_ = lean_ctor_get(v___x_2979_, 6);
v_messages_2987_ = lean_ctor_get(v___x_2979_, 7);
v_infoState_2988_ = lean_ctor_get(v___x_2979_, 8);
v_snapshotTasks_2989_ = lean_ctor_get(v___x_2979_, 9);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2991_ = v___x_2979_;
v_isShared_2992_ = v_isSharedCheck_3008_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_snapshotTasks_2989_);
lean_inc(v_infoState_2988_);
lean_inc(v_messages_2987_);
lean_inc(v_recordedDeps_2986_);
lean_inc(v_cache_2985_);
lean_inc(v_traceState_2980_);
lean_inc(v_auxDeclNGen_2984_);
lean_inc(v_ngen_2983_);
lean_inc(v_nextMacroScope_2982_);
lean_inc(v_env_2981_);
lean_dec(v___x_2979_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3008_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
uint64_t v_tid_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3006_; 
v_tid_2993_ = lean_ctor_get_uint64(v_traceState_2980_, sizeof(void*)*1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_traceState_2980_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v_traceState_2980_, 0);
lean_dec(v_unused_3007_);
v___x_2995_ = v_traceState_2980_;
v_isShared_2996_ = v_isSharedCheck_3006_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v_traceState_2980_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3006_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v___x_2999_; 
v___x_2997_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_2997_);
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2997_);
lean_ctor_set_uint64(v_reuseFailAlloc_3005_, sizeof(void*)*1, v_tid_2993_);
v___x_2999_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3001_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 4, v___x_2999_);
v___x_3001_ = v___x_2991_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_env_2981_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_nextMacroScope_2982_);
lean_ctor_set(v_reuseFailAlloc_3004_, 2, v_ngen_2983_);
lean_ctor_set(v_reuseFailAlloc_3004_, 3, v_auxDeclNGen_2984_);
lean_ctor_set(v_reuseFailAlloc_3004_, 4, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3004_, 5, v_cache_2985_);
lean_ctor_set(v_reuseFailAlloc_3004_, 6, v_recordedDeps_2986_);
lean_ctor_set(v_reuseFailAlloc_3004_, 7, v_messages_2987_);
lean_ctor_set(v_reuseFailAlloc_3004_, 8, v_infoState_2988_);
lean_ctor_set(v_reuseFailAlloc_3004_, 9, v_snapshotTasks_2989_);
v___x_3001_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_st_ref_put(v___y_2974_, v___x_3001_);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_traces_2978_);
return v___x_3003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3009_);
lean_dec(v___y_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3012_, lean_object* v_opt_3013_){
_start:
{
lean_object* v_name_3014_; lean_object* v_defValue_3015_; lean_object* v_map_3016_; lean_object* v___x_3017_; 
v_name_3014_ = lean_ctor_get(v_opt_3013_, 0);
v_defValue_3015_ = lean_ctor_get(v_opt_3013_, 1);
v_map_3016_ = lean_ctor_get(v_opts_3012_, 0);
v___x_3017_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3016_, v_name_3014_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_inc(v_defValue_3015_);
return v_defValue_3015_;
}
else
{
lean_object* v_val_3018_; 
v_val_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_val_3018_);
lean_dec_ref_known(v___x_3017_, 1);
if (lean_obj_tag(v_val_3018_) == 3)
{
lean_object* v_v_3019_; 
v_v_3019_ = lean_ctor_get(v_val_3018_, 0);
lean_inc(v_v_3019_);
lean_dec_ref_known(v_val_3018_, 1);
return v_v_3019_;
}
else
{
lean_dec(v_val_3018_);
lean_inc(v_defValue_3015_);
return v_defValue_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3020_, lean_object* v_opt_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3020_, v_opt_3021_);
lean_dec_ref(v_opt_3021_);
lean_dec_ref(v_opts_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3023_, lean_object* v_opt_3024_){
_start:
{
lean_object* v_name_3025_; lean_object* v_defValue_3026_; lean_object* v_map_3027_; lean_object* v___x_3028_; 
v_name_3025_ = lean_ctor_get(v_opt_3024_, 0);
v_defValue_3026_ = lean_ctor_get(v_opt_3024_, 1);
v_map_3027_ = lean_ctor_get(v_opts_3023_, 0);
v___x_3028_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3027_, v_name_3025_);
if (lean_obj_tag(v___x_3028_) == 0)
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_unbox(v_defValue_3026_);
return v___x_3029_;
}
else
{
lean_object* v_val_3030_; 
v_val_3030_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_val_3030_);
lean_dec_ref_known(v___x_3028_, 1);
if (lean_obj_tag(v_val_3030_) == 1)
{
uint8_t v_v_3031_; 
v_v_3031_ = lean_ctor_get_uint8(v_val_3030_, 0);
lean_dec_ref_known(v_val_3030_, 0);
return v_v_3031_;
}
else
{
uint8_t v___x_3032_; 
lean_dec(v_val_3030_);
v___x_3032_ = lean_unbox(v_defValue_3026_);
return v___x_3032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3033_, lean_object* v_opt_3034_){
_start:
{
uint8_t v_res_3035_; lean_object* v_r_3036_; 
v_res_3035_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3033_, v_opt_3034_);
lean_dec_ref(v_opt_3034_);
lean_dec_ref(v_opts_3033_);
v_r_3036_ = lean_box(v_res_3035_);
return v_r_3036_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3037_){
_start:
{
if (lean_obj_tag(v_e_3037_) == 0)
{
uint8_t v___x_3038_; 
v___x_3038_ = 2;
return v___x_3038_;
}
else
{
lean_object* v_a_3039_; uint8_t v___x_3040_; 
v_a_3039_ = lean_ctor_get(v_e_3037_, 0);
v___x_3040_ = l_Lean_Expr_hasSyntheticSorry(v_a_3039_);
if (v___x_3040_ == 0)
{
uint8_t v___x_3041_; 
v___x_3041_ = 0;
return v___x_3041_;
}
else
{
uint8_t v___x_3042_; 
v___x_3042_ = 1;
return v___x_3042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3043_){
_start:
{
uint8_t v_res_3044_; lean_object* v_r_3045_; 
v_res_3044_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3043_);
lean_dec_ref(v_e_3043_);
v_r_3045_ = lean_box(v_res_3044_);
return v_r_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3046_, size_t v_i_3047_, lean_object* v_bs_3048_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_usize_dec_lt(v_i_3047_, v_sz_3046_);
if (v___x_3049_ == 0)
{
return v_bs_3048_;
}
else
{
lean_object* v_v_3050_; lean_object* v_msg_3051_; lean_object* v___x_3052_; lean_object* v_bs_x27_3053_; size_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v_v_3050_ = lean_array_uget_borrowed(v_bs_3048_, v_i_3047_);
v_msg_3051_ = lean_ctor_get(v_v_3050_, 1);
lean_inc_ref(v_msg_3051_);
v___x_3052_ = lean_unsigned_to_nat(0u);
v_bs_x27_3053_ = lean_array_uset(v_bs_3048_, v_i_3047_, v___x_3052_);
v___x_3054_ = ((size_t)1ULL);
v___x_3055_ = lean_usize_add(v_i_3047_, v___x_3054_);
v___x_3056_ = lean_array_uset(v_bs_x27_3053_, v_i_3047_, v_msg_3051_);
v_i_3047_ = v___x_3055_;
v_bs_3048_ = v___x_3056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3058_, lean_object* v_i_3059_, lean_object* v_bs_3060_){
_start:
{
size_t v_sz_boxed_3061_; size_t v_i_boxed_3062_; lean_object* v_res_3063_; 
v_sz_boxed_3061_ = lean_unbox_usize(v_sz_3058_);
lean_dec(v_sz_3058_);
v_i_boxed_3062_ = lean_unbox_usize(v_i_3059_);
lean_dec(v_i_3059_);
v_res_3063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3061_, v_i_boxed_3062_, v_bs_3060_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3064_, lean_object* v_data_3065_, lean_object* v_ref_3066_, lean_object* v_msg_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_toCold_3073_; lean_object* v_currRecDepth_3074_; lean_object* v_ref_3075_; uint16_t v_optionFlags_3076_; uint8_t v_suppressElabErrors_3077_; uint8_t v_isRecordingDeps_3078_; lean_object* v_ref_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v_traceState_3082_; lean_object* v_traces_3083_; lean_object* v___x_3084_; size_t v_sz_3085_; size_t v___x_3086_; lean_object* v___x_3087_; lean_object* v_msg_3088_; lean_object* v___x_3089_; lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3128_; 
v_toCold_3073_ = lean_ctor_get(v___y_3070_, 0);
v_currRecDepth_3074_ = lean_ctor_get(v___y_3070_, 1);
v_ref_3075_ = lean_ctor_get(v___y_3070_, 2);
v_optionFlags_3076_ = lean_ctor_get_uint16(v___y_3070_, sizeof(void*)*3);
v_suppressElabErrors_3077_ = lean_ctor_get_uint8(v___y_3070_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3078_ = lean_ctor_get_uint8(v___y_3070_, sizeof(void*)*3 + 3);
v_ref_3079_ = l_Lean_replaceRef(v_ref_3066_, v_ref_3075_);
lean_inc(v_currRecDepth_3074_);
lean_inc_ref(v_toCold_3073_);
v___x_3080_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3080_, 0, v_toCold_3073_);
lean_ctor_set(v___x_3080_, 1, v_currRecDepth_3074_);
lean_ctor_set(v___x_3080_, 2, v_ref_3079_);
lean_ctor_set_uint16(v___x_3080_, sizeof(void*)*3, v_optionFlags_3076_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*3 + 2, v_suppressElabErrors_3077_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*3 + 3, v_isRecordingDeps_3078_);
v___x_3081_ = lean_st_ref_get(v___y_3071_);
v_traceState_3082_ = lean_ctor_get(v___x_3081_, 4);
lean_inc_ref(v_traceState_3082_);
lean_dec(v___x_3081_);
v_traces_3083_ = lean_ctor_get(v_traceState_3082_, 0);
lean_inc_ref(v_traces_3083_);
lean_dec_ref(v_traceState_3082_);
v___x_3084_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3083_);
lean_dec_ref(v_traces_3083_);
v_sz_3085_ = lean_array_size(v___x_3084_);
v___x_3086_ = ((size_t)0ULL);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3085_, v___x_3086_, v___x_3084_);
v_msg_3088_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3088_, 0, v_data_3065_);
lean_ctor_set(v_msg_3088_, 1, v_msg_3067_);
lean_ctor_set(v_msg_3088_, 2, v___x_3087_);
v___x_3089_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3088_, v___y_3068_, v___y_3069_, v___x_3080_, v___y_3071_);
lean_dec_ref_known(v___x_3080_, 3);
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3128_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3128_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v_traceState_3095_; lean_object* v_env_3096_; lean_object* v_nextMacroScope_3097_; lean_object* v_ngen_3098_; lean_object* v_auxDeclNGen_3099_; lean_object* v_cache_3100_; lean_object* v_recordedDeps_3101_; lean_object* v_messages_3102_; lean_object* v_infoState_3103_; lean_object* v_snapshotTasks_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3127_; 
v___x_3094_ = lean_st_ref_take(v___y_3071_);
v_traceState_3095_ = lean_ctor_get(v___x_3094_, 4);
v_env_3096_ = lean_ctor_get(v___x_3094_, 0);
v_nextMacroScope_3097_ = lean_ctor_get(v___x_3094_, 1);
v_ngen_3098_ = lean_ctor_get(v___x_3094_, 2);
v_auxDeclNGen_3099_ = lean_ctor_get(v___x_3094_, 3);
v_cache_3100_ = lean_ctor_get(v___x_3094_, 5);
v_recordedDeps_3101_ = lean_ctor_get(v___x_3094_, 6);
v_messages_3102_ = lean_ctor_get(v___x_3094_, 7);
v_infoState_3103_ = lean_ctor_get(v___x_3094_, 8);
v_snapshotTasks_3104_ = lean_ctor_get(v___x_3094_, 9);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3106_ = v___x_3094_;
v_isShared_3107_ = v_isSharedCheck_3127_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_snapshotTasks_3104_);
lean_inc(v_infoState_3103_);
lean_inc(v_messages_3102_);
lean_inc(v_recordedDeps_3101_);
lean_inc(v_cache_3100_);
lean_inc(v_traceState_3095_);
lean_inc(v_auxDeclNGen_3099_);
lean_inc(v_ngen_3098_);
lean_inc(v_nextMacroScope_3097_);
lean_inc(v_env_3096_);
lean_dec(v___x_3094_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3127_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
uint64_t v_tid_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3125_; 
v_tid_3108_ = lean_ctor_get_uint64(v_traceState_3095_, sizeof(void*)*1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_traceState_3095_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_traceState_3095_, 0);
lean_dec(v_unused_3126_);
v___x_3110_ = v_traceState_3095_;
v_isShared_3111_ = v_isSharedCheck_3125_;
goto v_resetjp_3109_;
}
else
{
lean_dec(v_traceState_3095_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3125_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_ref_3066_);
lean_ctor_set(v___x_3113_, 1, v_a_3090_);
v___x_3114_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3064_, v___x_3113_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3114_);
v___x_3116_ = v___x_3110_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3114_);
lean_ctor_set_uint64(v_reuseFailAlloc_3124_, sizeof(void*)*1, v_tid_3108_);
v___x_3116_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3118_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 4, v___x_3116_);
v___x_3118_ = v___x_3106_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_env_3096_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_nextMacroScope_3097_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_ngen_3098_);
lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_auxDeclNGen_3099_);
lean_ctor_set(v_reuseFailAlloc_3123_, 4, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3123_, 5, v_cache_3100_);
lean_ctor_set(v_reuseFailAlloc_3123_, 6, v_recordedDeps_3101_);
lean_ctor_set(v_reuseFailAlloc_3123_, 7, v_messages_3102_);
lean_ctor_set(v_reuseFailAlloc_3123_, 8, v_infoState_3103_);
lean_ctor_set(v_reuseFailAlloc_3123_, 9, v_snapshotTasks_3104_);
v___x_3118_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3119_ = lean_st_ref_put(v___y_3071_, v___x_3118_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3112_);
v___x_3121_ = v___x_3092_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3112_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3129_, lean_object* v_data_3130_, lean_object* v_ref_3131_, lean_object* v_msg_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3129_, v_data_3130_, v_ref_3131_, v_msg_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3139_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3141_ = lean_ctor_get(v_x_3139_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_x_3139_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v_x_3139_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v_x_3139_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 1);
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_a_3149_ = lean_ctor_get(v_x_3139_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_x_3139_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v_x_3139_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v_x_3139_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set_tag(v___x_3151_, 0);
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3157_);
return v_res_3159_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3160_; double v___x_3161_; 
v___x_3160_ = lean_unsigned_to_nat(0u);
v___x_3161_ = lean_float_of_nat(v___x_3160_);
return v___x_3161_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3164_ = l_Lean_stringToMessageData(v___x_3163_);
return v___x_3164_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3165_; double v___x_3166_; 
v___x_3165_ = lean_unsigned_to_nat(1000u);
v___x_3166_ = lean_float_of_nat(v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3167_, uint8_t v_collapsed_3168_, lean_object* v_tag_3169_, lean_object* v_opts_3170_, uint8_t v_clsEnabled_3171_, lean_object* v_oldTraces_3172_, lean_object* v_msg_3173_, lean_object* v_resStartStop_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_fst_3180_; lean_object* v_snd_3181_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v_data_3185_; lean_object* v_fst_3196_; lean_object* v_snd_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; lean_object* v___y_3201_; lean_object* v_a_3202_; uint8_t v___y_3217_; double v___y_3249_; 
v_fst_3180_ = lean_ctor_get(v_resStartStop_3174_, 0);
lean_inc(v_fst_3180_);
v_snd_3181_ = lean_ctor_get(v_resStartStop_3174_, 1);
lean_inc(v_snd_3181_);
lean_dec_ref(v_resStartStop_3174_);
v_fst_3196_ = lean_ctor_get(v_snd_3181_, 0);
lean_inc(v_fst_3196_);
v_snd_3197_ = lean_ctor_get(v_snd_3181_, 1);
lean_inc(v_snd_3197_);
lean_dec(v_snd_3181_);
v___x_3198_ = l_Lean_trace_profiler;
v___x_3199_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3170_, v___x_3198_);
if (v___x_3199_ == 0)
{
v___y_3217_ = v___x_3199_;
goto v___jp_3216_;
}
else
{
lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3255_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3170_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; double v___x_3258_; double v___x_3259_; double v___x_3260_; 
v___x_3256_ = l_Lean_trace_profiler_threshold;
v___x_3257_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3170_, v___x_3256_);
v___x_3258_ = lean_float_of_nat(v___x_3257_);
v___x_3259_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3260_ = lean_float_div(v___x_3258_, v___x_3259_);
v___y_3249_ = v___x_3260_;
goto v___jp_3248_;
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; double v___x_3263_; 
v___x_3261_ = l_Lean_trace_profiler_threshold;
v___x_3262_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3170_, v___x_3261_);
v___x_3263_ = lean_float_of_nat(v___x_3262_);
v___y_3249_ = v___x_3263_;
goto v___jp_3248_;
}
}
v___jp_3182_:
{
lean_object* v___x_3186_; 
lean_inc(v___y_3184_);
v___x_3186_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3172_, v_data_3185_, v___y_3184_, v___y_3183_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v___x_3187_; 
lean_dec_ref_known(v___x_3186_, 1);
v___x_3187_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3180_);
return v___x_3187_;
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v_fst_3180_);
v_a_3188_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3186_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3186_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
v___jp_3200_:
{
uint8_t v_result_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; double v___x_3206_; lean_object* v_data_3207_; 
v_result_3203_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3180_);
v___x_3204_ = lean_box(v_result_3203_);
v___x_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
v___x_3206_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3169_);
lean_inc_ref(v___x_3205_);
lean_inc(v_cls_3167_);
v_data_3207_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3207_, 0, v_cls_3167_);
lean_ctor_set(v_data_3207_, 1, v___x_3205_);
lean_ctor_set(v_data_3207_, 2, v_tag_3169_);
lean_ctor_set_float(v_data_3207_, sizeof(void*)*3, v___x_3206_);
lean_ctor_set_float(v_data_3207_, sizeof(void*)*3 + 8, v___x_3206_);
lean_ctor_set_uint8(v_data_3207_, sizeof(void*)*3 + 16, v_collapsed_3168_);
if (v___x_3199_ == 0)
{
lean_dec_ref_known(v___x_3205_, 1);
lean_dec(v_snd_3197_);
lean_dec(v_fst_3196_);
lean_dec_ref(v_tag_3169_);
lean_dec(v_cls_3167_);
v___y_3183_ = v_a_3202_;
v___y_3184_ = v___y_3201_;
v_data_3185_ = v_data_3207_;
goto v___jp_3182_;
}
else
{
lean_object* v_data_3208_; double v___x_3209_; double v___x_3210_; 
lean_dec_ref_known(v_data_3207_, 3);
v_data_3208_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3208_, 0, v_cls_3167_);
lean_ctor_set(v_data_3208_, 1, v___x_3205_);
lean_ctor_set(v_data_3208_, 2, v_tag_3169_);
v___x_3209_ = lean_unbox_float(v_fst_3196_);
lean_dec(v_fst_3196_);
lean_ctor_set_float(v_data_3208_, sizeof(void*)*3, v___x_3209_);
v___x_3210_ = lean_unbox_float(v_snd_3197_);
lean_dec(v_snd_3197_);
lean_ctor_set_float(v_data_3208_, sizeof(void*)*3 + 8, v___x_3210_);
lean_ctor_set_uint8(v_data_3208_, sizeof(void*)*3 + 16, v_collapsed_3168_);
v___y_3183_ = v_a_3202_;
v___y_3184_ = v___y_3201_;
v_data_3185_ = v_data_3208_;
goto v___jp_3182_;
}
}
v___jp_3211_:
{
lean_object* v_ref_3212_; lean_object* v___x_3213_; 
v_ref_3212_ = lean_ctor_get(v___y_3177_, 2);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v_fst_3180_);
v___x_3213_ = lean_apply_6(v_msg_3173_, v_fst_3180_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, lean_box(0));
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___y_3201_ = v_ref_3212_;
v_a_3202_ = v_a_3214_;
goto v___jp_3200_;
}
else
{
lean_object* v___x_3215_; 
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3201_ = v_ref_3212_;
v_a_3202_ = v___x_3215_;
goto v___jp_3200_;
}
}
v___jp_3216_:
{
if (v_clsEnabled_3171_ == 0)
{
if (v___y_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v_traceState_3219_; lean_object* v_env_3220_; lean_object* v_nextMacroScope_3221_; lean_object* v_ngen_3222_; lean_object* v_auxDeclNGen_3223_; lean_object* v_cache_3224_; lean_object* v_recordedDeps_3225_; lean_object* v_messages_3226_; lean_object* v_infoState_3227_; lean_object* v_snapshotTasks_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_snd_3197_);
lean_dec(v_fst_3196_);
lean_dec_ref(v_msg_3173_);
lean_dec_ref(v_tag_3169_);
lean_dec(v_cls_3167_);
v___x_3218_ = lean_st_ref_take(v___y_3178_);
v_traceState_3219_ = lean_ctor_get(v___x_3218_, 4);
v_env_3220_ = lean_ctor_get(v___x_3218_, 0);
v_nextMacroScope_3221_ = lean_ctor_get(v___x_3218_, 1);
v_ngen_3222_ = lean_ctor_get(v___x_3218_, 2);
v_auxDeclNGen_3223_ = lean_ctor_get(v___x_3218_, 3);
v_cache_3224_ = lean_ctor_get(v___x_3218_, 5);
v_recordedDeps_3225_ = lean_ctor_get(v___x_3218_, 6);
v_messages_3226_ = lean_ctor_get(v___x_3218_, 7);
v_infoState_3227_ = lean_ctor_get(v___x_3218_, 8);
v_snapshotTasks_3228_ = lean_ctor_get(v___x_3218_, 9);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3230_ = v___x_3218_;
v_isShared_3231_ = v_isSharedCheck_3247_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_snapshotTasks_3228_);
lean_inc(v_infoState_3227_);
lean_inc(v_messages_3226_);
lean_inc(v_recordedDeps_3225_);
lean_inc(v_cache_3224_);
lean_inc(v_traceState_3219_);
lean_inc(v_auxDeclNGen_3223_);
lean_inc(v_ngen_3222_);
lean_inc(v_nextMacroScope_3221_);
lean_inc(v_env_3220_);
lean_dec(v___x_3218_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3247_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
uint64_t v_tid_3232_; lean_object* v_traces_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3246_; 
v_tid_3232_ = lean_ctor_get_uint64(v_traceState_3219_, sizeof(void*)*1);
v_traces_3233_ = lean_ctor_get(v_traceState_3219_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_traceState_3219_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3235_ = v_traceState_3219_;
v_isShared_3236_ = v_isSharedCheck_3246_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_traces_3233_);
lean_dec(v_traceState_3219_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3246_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3237_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3172_, v_traces_3233_);
lean_dec_ref(v_traces_3233_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3237_);
v___x_3239_ = v___x_3235_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3237_);
lean_ctor_set_uint64(v_reuseFailAlloc_3245_, sizeof(void*)*1, v_tid_3232_);
v___x_3239_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
lean_object* v___x_3241_; 
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 4, v___x_3239_);
v___x_3241_ = v___x_3230_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_env_3220_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_nextMacroScope_3221_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_ngen_3222_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_auxDeclNGen_3223_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3244_, 5, v_cache_3224_);
lean_ctor_set(v_reuseFailAlloc_3244_, 6, v_recordedDeps_3225_);
lean_ctor_set(v_reuseFailAlloc_3244_, 7, v_messages_3226_);
lean_ctor_set(v_reuseFailAlloc_3244_, 8, v_infoState_3227_);
lean_ctor_set(v_reuseFailAlloc_3244_, 9, v_snapshotTasks_3228_);
v___x_3241_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = lean_st_ref_put(v___y_3178_, v___x_3241_);
v___x_3243_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3180_);
return v___x_3243_;
}
}
}
}
}
else
{
goto v___jp_3211_;
}
}
else
{
goto v___jp_3211_;
}
}
v___jp_3248_:
{
double v___x_3250_; double v___x_3251_; double v___x_3252_; uint8_t v___x_3253_; 
v___x_3250_ = lean_unbox_float(v_snd_3197_);
v___x_3251_ = lean_unbox_float(v_fst_3196_);
v___x_3252_ = lean_float_sub(v___x_3250_, v___x_3251_);
v___x_3253_ = lean_float_decLt(v___y_3249_, v___x_3252_);
v___y_3217_ = v___x_3253_;
goto v___jp_3216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3264_, lean_object* v_collapsed_3265_, lean_object* v_tag_3266_, lean_object* v_opts_3267_, lean_object* v_clsEnabled_3268_, lean_object* v_oldTraces_3269_, lean_object* v_msg_3270_, lean_object* v_resStartStop_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
uint8_t v_collapsed_boxed_3277_; uint8_t v_clsEnabled_boxed_3278_; lean_object* v_res_3279_; 
v_collapsed_boxed_3277_ = lean_unbox(v_collapsed_3265_);
v_clsEnabled_boxed_3278_ = lean_unbox(v_clsEnabled_3268_);
v_res_3279_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3264_, v_collapsed_boxed_3277_, v_tag_3266_, v_opts_3267_, v_clsEnabled_boxed_3278_, v_oldTraces_3269_, v_msg_3270_, v_resStartStop_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec_ref(v_opts_3267_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
if (lean_obj_tag(v_a_3280_) == 0)
{
lean_object* v___x_3282_; 
v___x_3282_ = l_List_reverse___redArg(v_a_3281_);
return v___x_3282_;
}
else
{
lean_object* v_head_3283_; lean_object* v_tail_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3293_; 
v_head_3283_ = lean_ctor_get(v_a_3280_, 0);
v_tail_3284_ = lean_ctor_get(v_a_3280_, 1);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_a_3280_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3286_ = v_a_3280_;
v_isShared_3287_ = v_isSharedCheck_3293_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_tail_3284_);
lean_inc(v_head_3283_);
lean_dec(v_a_3280_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3293_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3288_ = l_Lean_MessageData_ofExpr(v_head_3283_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 1, v_a_3281_);
lean_ctor_set(v___x_3286_, 0, v___x_3288_);
v___x_3290_ = v___x_3286_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_a_3281_);
v___x_3290_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
v_a_3280_ = v_tail_3284_;
v_a_3281_ = v___x_3290_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3294_, lean_object* v_xs_3295_, lean_object* v_x_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3302_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3303_ = l_Lean_MessageData_ofName(v_f_3294_);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_array_to_list(v_xs_3295_);
v___x_3308_ = lean_box(0);
v___x_3309_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3307_, v___x_3308_);
v___x_3310_ = l_Lean_MessageData_ofList(v___x_3309_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3306_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3313_, lean_object* v_xs_3314_, lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3313_, v_xs_3314_, v_x_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v_x_3315_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3324_, lean_object* v_msg_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_ref_3331_; lean_object* v___x_3332_; lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3378_; 
v_ref_3331_ = lean_ctor_get(v___y_3328_, 2);
v___x_3332_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3378_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3378_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v_traceState_3338_; lean_object* v_env_3339_; lean_object* v_nextMacroScope_3340_; lean_object* v_ngen_3341_; lean_object* v_auxDeclNGen_3342_; lean_object* v_cache_3343_; lean_object* v_recordedDeps_3344_; lean_object* v_messages_3345_; lean_object* v_infoState_3346_; lean_object* v_snapshotTasks_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3377_; 
v___x_3337_ = lean_st_ref_take(v___y_3329_);
v_traceState_3338_ = lean_ctor_get(v___x_3337_, 4);
v_env_3339_ = lean_ctor_get(v___x_3337_, 0);
v_nextMacroScope_3340_ = lean_ctor_get(v___x_3337_, 1);
v_ngen_3341_ = lean_ctor_get(v___x_3337_, 2);
v_auxDeclNGen_3342_ = lean_ctor_get(v___x_3337_, 3);
v_cache_3343_ = lean_ctor_get(v___x_3337_, 5);
v_recordedDeps_3344_ = lean_ctor_get(v___x_3337_, 6);
v_messages_3345_ = lean_ctor_get(v___x_3337_, 7);
v_infoState_3346_ = lean_ctor_get(v___x_3337_, 8);
v_snapshotTasks_3347_ = lean_ctor_get(v___x_3337_, 9);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3349_ = v___x_3337_;
v_isShared_3350_ = v_isSharedCheck_3377_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_snapshotTasks_3347_);
lean_inc(v_infoState_3346_);
lean_inc(v_messages_3345_);
lean_inc(v_recordedDeps_3344_);
lean_inc(v_cache_3343_);
lean_inc(v_traceState_3338_);
lean_inc(v_auxDeclNGen_3342_);
lean_inc(v_ngen_3341_);
lean_inc(v_nextMacroScope_3340_);
lean_inc(v_env_3339_);
lean_dec(v___x_3337_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3377_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
uint64_t v_tid_3351_; lean_object* v_traces_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3376_; 
v_tid_3351_ = lean_ctor_get_uint64(v_traceState_3338_, sizeof(void*)*1);
v_traces_3352_ = lean_ctor_get(v_traceState_3338_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v_traceState_3338_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3354_ = v_traceState_3338_;
v_isShared_3355_ = v_isSharedCheck_3376_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_traces_3352_);
lean_dec(v_traceState_3338_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3376_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; double v___x_3358_; uint8_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3367_; 
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_box(0);
v___x_3358_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3359_ = 0;
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3361_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3361_, 0, v_cls_3324_);
lean_ctor_set(v___x_3361_, 1, v___x_3357_);
lean_ctor_set(v___x_3361_, 2, v___x_3360_);
lean_ctor_set_float(v___x_3361_, sizeof(void*)*3, v___x_3358_);
lean_ctor_set_float(v___x_3361_, sizeof(void*)*3 + 8, v___x_3358_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*3 + 16, v___x_3359_);
v___x_3362_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3363_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3361_);
lean_ctor_set(v___x_3363_, 1, v_a_3333_);
lean_ctor_set(v___x_3363_, 2, v___x_3362_);
lean_inc(v_ref_3331_);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v_ref_3331_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = l_Lean_PersistentArray_push___redArg(v_traces_3352_, v___x_3364_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3365_);
v___x_3367_ = v___x_3354_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3365_);
lean_ctor_set_uint64(v_reuseFailAlloc_3375_, sizeof(void*)*1, v_tid_3351_);
v___x_3367_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3369_; 
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 4, v___x_3367_);
v___x_3369_ = v___x_3349_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_env_3339_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_nextMacroScope_3340_);
lean_ctor_set(v_reuseFailAlloc_3374_, 2, v_ngen_3341_);
lean_ctor_set(v_reuseFailAlloc_3374_, 3, v_auxDeclNGen_3342_);
lean_ctor_set(v_reuseFailAlloc_3374_, 4, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3374_, 5, v_cache_3343_);
lean_ctor_set(v_reuseFailAlloc_3374_, 6, v_recordedDeps_3344_);
lean_ctor_set(v_reuseFailAlloc_3374_, 7, v_messages_3345_);
lean_ctor_set(v_reuseFailAlloc_3374_, 8, v_infoState_3346_);
lean_ctor_set(v_reuseFailAlloc_3374_, 9, v_snapshotTasks_3347_);
v___x_3369_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_st_ref_put(v___y_3329_, v___x_3369_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3356_);
v___x_3372_ = v___x_3335_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3356_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3379_, lean_object* v_msg_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3379_, v_msg_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3387_, lean_object* v_xs_3388_, lean_object* v_k_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_toCold_3395_; lean_object* v_options_3396_; uint8_t v_hasTrace_3397_; 
v_toCold_3395_ = lean_ctor_get(v_a_3392_, 0);
v_options_3396_ = lean_ctor_get(v_toCold_3395_, 2);
v_hasTrace_3397_ = lean_ctor_get_uint8(v_options_3396_, sizeof(void*)*1);
if (v_hasTrace_3397_ == 0)
{
lean_object* v___x_3398_; 
lean_dec_ref(v_xs_3388_);
lean_dec(v_f_3387_);
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
lean_inc(v_a_3391_);
lean_inc_ref(v_a_3390_);
v___x_3398_ = lean_apply_5(v_k_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, lean_box(0));
return v___x_3398_;
}
else
{
lean_object* v_inheritedTraceOptions_3399_; lean_object* v___f_3400_; lean_object* v___y_3402_; lean_object* v_a_3403_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v_a_3435_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v_a_3450_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v_a_3455_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v_a_3460_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v_a_3472_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v_a_3484_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v_a_3489_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v_a_3494_; 
v_inheritedTraceOptions_3399_ = lean_ctor_get(v_toCold_3395_, 11);
v___f_3400_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3400_, 0, v_f_3387_);
lean_closure_set(v___f_3400_, 1, v_xs_3388_);
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3430_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3431_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3399_, v_options_3396_, v___x_3430_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3528_ = l_Lean_trace_profiler;
v___x_3529_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3396_, v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
lean_dec_ref(v___f_3400_);
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
lean_inc(v_a_3391_);
lean_inc_ref(v_a_3390_);
v___x_3530_ = lean_apply_5(v_k_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, lean_box(0));
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
v___x_3532_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3533_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3534_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3399_, v_options_3396_, v___x_3533_);
if (v___x_3534_ == 0)
{
lean_dec(v_a_3531_);
return v___x_3530_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
lean_dec_ref_known(v___x_3530_, 1);
lean_inc(v_a_3531_);
v___x_3535_ = l_Lean_MessageData_ofExpr(v_a_3531_);
v___x_3536_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3532_, v___x_3535_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3543_ == 0)
{
lean_object* v_unused_3544_; 
v_unused_3544_ = lean_ctor_get(v___x_3536_, 0);
lean_dec(v_unused_3544_);
v___x_3538_ = v___x_3536_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_dec(v___x_3536_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v_a_3531_);
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3531_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_a_3531_);
v_a_3545_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3536_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3536_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
lean_inc(v_a_3545_);
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
v___y_3402_ = v___x_3550_;
v_a_3403_ = v_a_3545_;
goto v___jp_3401_;
}
}
}
}
}
else
{
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3553_);
v___y_3402_ = v___x_3530_;
v_a_3403_ = v_a_3553_;
goto v___jp_3401_;
}
}
else
{
goto v___jp_3503_;
}
}
else
{
goto v___jp_3503_;
}
v___jp_3401_:
{
uint8_t v___x_3404_; 
v___x_3404_ = l_Lean_Exception_isInterrupt(v_a_3403_);
if (v___x_3404_ == 0)
{
uint8_t v___x_3405_; 
lean_inc_ref(v_a_3403_);
v___x_3405_ = l_Lean_Exception_isRuntime(v_a_3403_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
lean_dec_ref(v___y_3402_);
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3407_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3408_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3399_, v_options_3396_, v___x_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_a_3403_);
return v___x_3409_;
}
else
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_inc_ref(v_a_3403_);
v___x_3410_ = l_Lean_Exception_toMessageData(v_a_3403_);
v___x_3411_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3406_, v___x_3410_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v___x_3411_, 0);
lean_dec(v_unused_3419_);
v___x_3413_ = v___x_3411_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_dec(v___x_3411_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 1);
lean_ctor_set(v___x_3413_, 0, v_a_3403_);
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3403_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v_a_3403_);
v_a_3420_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3411_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3411_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3403_);
return v___y_3402_;
}
}
else
{
lean_dec_ref(v_a_3403_);
return v___y_3402_;
}
}
v___jp_3432_:
{
lean_object* v___x_3436_; double v___x_3437_; double v___x_3438_; double v___x_3439_; double v___x_3440_; double v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3436_ = lean_io_mono_nanos_now();
v___x_3437_ = lean_float_of_nat(v___y_3433_);
v___x_3438_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3439_ = lean_float_div(v___x_3437_, v___x_3438_);
v___x_3440_ = lean_float_of_nat(v___x_3436_);
v___x_3441_ = lean_float_div(v___x_3440_, v___x_3438_);
v___x_3442_ = lean_box_float(v___x_3439_);
v___x_3443_ = lean_box_float(v___x_3441_);
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3445_, 0, v_a_3435_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3428_, v_hasTrace_3397_, v___x_3429_, v_options_3396_, v___x_3431_, v___y_3434_, v___f_3400_, v___x_3445_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
return v___x_3446_;
}
v___jp_3447_:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_a_3450_);
v___y_3433_ = v___y_3448_;
v___y_3434_ = v___y_3449_;
v_a_3435_ = v___x_3451_;
goto v___jp_3432_;
}
v___jp_3452_:
{
lean_object* v___x_3456_; 
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v_a_3455_);
v___y_3433_ = v___y_3453_;
v___y_3434_ = v___y_3454_;
v_a_3435_ = v___x_3456_;
goto v___jp_3432_;
}
v___jp_3457_:
{
uint8_t v___x_3461_; 
v___x_3461_ = l_Lean_Exception_isInterrupt(v_a_3460_);
if (v___x_3461_ == 0)
{
uint8_t v___x_3462_; 
lean_inc_ref(v_a_3460_);
v___x_3462_ = l_Lean_Exception_isRuntime(v_a_3460_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; 
v___x_3463_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3464_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3465_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3399_, v_options_3396_, v___x_3464_);
if (v___x_3465_ == 0)
{
v___y_3453_ = v___y_3458_;
v___y_3454_ = v___y_3459_;
v_a_3455_ = v_a_3460_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_inc_ref(v_a_3460_);
v___x_3466_ = l_Lean_Exception_toMessageData(v_a_3460_);
v___x_3467_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3463_, v___x_3466_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_dec_ref_known(v___x_3467_, 1);
v___y_3453_ = v___y_3458_;
v___y_3454_ = v___y_3459_;
v_a_3455_ = v_a_3460_;
goto v___jp_3452_;
}
else
{
lean_object* v_a_3468_; 
lean_dec_ref(v_a_3460_);
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___y_3453_ = v___y_3458_;
v___y_3454_ = v___y_3459_;
v_a_3455_ = v_a_3468_;
goto v___jp_3452_;
}
}
}
else
{
v___y_3453_ = v___y_3458_;
v___y_3454_ = v___y_3459_;
v_a_3455_ = v_a_3460_;
goto v___jp_3452_;
}
}
else
{
v___y_3453_ = v___y_3458_;
v___y_3454_ = v___y_3459_;
v_a_3455_ = v_a_3460_;
goto v___jp_3452_;
}
}
v___jp_3469_:
{
lean_object* v___x_3473_; double v___x_3474_; double v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3473_ = lean_io_get_num_heartbeats();
v___x_3474_ = lean_float_of_nat(v___y_3471_);
v___x_3475_ = lean_float_of_nat(v___x_3473_);
v___x_3476_ = lean_box_float(v___x_3474_);
v___x_3477_ = lean_box_float(v___x_3475_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3476_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v_a_3472_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3428_, v_hasTrace_3397_, v___x_3429_, v_options_3396_, v___x_3431_, v___y_3470_, v___f_3400_, v___x_3479_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
return v___x_3480_;
}
v___jp_3481_:
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_a_3484_);
v___y_3470_ = v___y_3482_;
v___y_3471_ = v___y_3483_;
v_a_3472_ = v___x_3485_;
goto v___jp_3469_;
}
v___jp_3486_:
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_a_3489_);
v___y_3470_ = v___y_3487_;
v___y_3471_ = v___y_3488_;
v_a_3472_ = v___x_3490_;
goto v___jp_3469_;
}
v___jp_3491_:
{
uint8_t v___x_3495_; 
v___x_3495_ = l_Lean_Exception_isInterrupt(v_a_3494_);
if (v___x_3495_ == 0)
{
uint8_t v___x_3496_; 
lean_inc_ref(v_a_3494_);
v___x_3496_ = l_Lean_Exception_isRuntime(v_a_3494_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3497_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3498_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3499_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3399_, v_options_3396_, v___x_3498_);
if (v___x_3499_ == 0)
{
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3493_;
v_a_3489_ = v_a_3494_;
goto v___jp_3486_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_inc_ref(v_a_3494_);
v___x_3500_ = l_Lean_Exception_toMessageData(v_a_3494_);
v___x_3501_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3497_, v___x_3500_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_dec_ref_known(v___x_3501_, 1);
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3493_;
v_a_3489_ = v_a_3494_;
goto v___jp_3486_;
}
else
{
lean_object* v_a_3502_; 
lean_dec_ref(v_a_3494_);
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3493_;
v_a_3489_ = v_a_3502_;
goto v___jp_3486_;
}
}
}
else
{
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3493_;
v_a_3489_ = v_a_3494_;
goto v___jp_3486_;
}
}
else
{
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3493_;
v_a_3489_ = v_a_3494_;
goto v___jp_3486_;
}
}
v___jp_3503_:
{
lean_object* v___x_3504_; lean_object* v_a_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v___x_3504_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3393_);
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref(v___x_3504_);
v___x_3506_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3507_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3396_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = lean_io_mono_nanos_now();
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
lean_inc(v_a_3391_);
lean_inc_ref(v_a_3390_);
v___x_3509_ = lean_apply_5(v_k_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, lean_box(0));
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3512_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3513_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3399_, v_options_3396_, v___x_3512_);
if (v___x_3513_ == 0)
{
v___y_3448_ = v___x_3508_;
v___y_3449_ = v_a_3505_;
v_a_3450_ = v_a_3510_;
goto v___jp_3447_;
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
lean_inc(v_a_3510_);
v___x_3514_ = l_Lean_MessageData_ofExpr(v_a_3510_);
v___x_3515_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3511_, v___x_3514_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_dec_ref_known(v___x_3515_, 1);
v___y_3448_ = v___x_3508_;
v___y_3449_ = v_a_3505_;
v_a_3450_ = v_a_3510_;
goto v___jp_3447_;
}
else
{
lean_object* v_a_3516_; 
lean_dec(v_a_3510_);
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___y_3458_ = v___x_3508_;
v___y_3459_ = v_a_3505_;
v_a_3460_ = v_a_3516_;
goto v___jp_3457_;
}
}
}
else
{
lean_object* v_a_3517_; 
v_a_3517_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3509_, 1);
v___y_3458_ = v___x_3508_;
v___y_3459_ = v_a_3505_;
v_a_3460_ = v_a_3517_;
goto v___jp_3457_;
}
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
lean_inc(v_a_3391_);
lean_inc_ref(v_a_3390_);
v___x_3519_ = lean_apply_5(v_k_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, lean_box(0));
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v___x_3521_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3522_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3523_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3399_, v_options_3396_, v___x_3522_);
if (v___x_3523_ == 0)
{
v___y_3482_ = v_a_3505_;
v___y_3483_ = v___x_3518_;
v_a_3484_ = v_a_3520_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_inc(v_a_3520_);
v___x_3524_ = l_Lean_MessageData_ofExpr(v_a_3520_);
v___x_3525_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3521_, v___x_3524_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_dec_ref_known(v___x_3525_, 1);
v___y_3482_ = v_a_3505_;
v___y_3483_ = v___x_3518_;
v_a_3484_ = v_a_3520_;
goto v___jp_3481_;
}
else
{
lean_object* v_a_3526_; 
lean_dec(v_a_3520_);
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v___x_3525_, 1);
v___y_3492_ = v_a_3505_;
v___y_3493_ = v___x_3518_;
v_a_3494_ = v_a_3526_;
goto v___jp_3491_;
}
}
}
else
{
lean_object* v_a_3527_; 
v_a_3527_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3519_, 1);
v___y_3492_ = v_a_3505_;
v___y_3493_ = v___x_3518_;
v_a_3494_ = v_a_3527_;
goto v___jp_3491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3554_, lean_object* v_xs_3555_, lean_object* v_k_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3554_, v_xs_3555_, v_k_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3563_, lean_object* v_xs_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v___f_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_inc_ref(v_xs_3564_);
lean_inc(v_constName_3563_);
v___f_3570_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3570_, 0, v_constName_3563_);
lean_closure_set(v___f_3570_, 1, v_xs_3564_);
v___x_3571_ = 0;
v___x_3572_ = lean_box(v___x_3571_);
v___x_3573_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3573_, 0, lean_box(0));
lean_closure_set(v___x_3573_, 1, v___f_3570_);
lean_closure_set(v___x_3573_, 2, v___x_3572_);
v___x_3574_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3563_, v_xs_3564_, v___x_3573_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3575_, lean_object* v_xs_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_Meta_mkAppM(v_constName_3575_, v_xs_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3586_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3596_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3603_, lean_object* v_x_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3603_, v_x_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3611_, lean_object* v_xs_3612_, lean_object* v_x_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3619_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3620_ = l_Lean_MessageData_ofExpr(v_f_3611_);
v___x_3621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3619_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3621_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = lean_array_to_list(v_xs_3612_);
v___x_3625_ = lean_box(0);
v___x_3626_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3624_, v___x_3625_);
v___x_3627_ = l_Lean_MessageData_ofList(v___x_3626_);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3623_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3630_, lean_object* v_xs_3631_, lean_object* v_x_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3630_, v_xs_3631_, v_x_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v_x_3632_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3639_, lean_object* v_xs_3640_, lean_object* v_k_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v_toCold_3647_; lean_object* v_options_3648_; uint8_t v_hasTrace_3649_; 
v_toCold_3647_ = lean_ctor_get(v_a_3644_, 0);
v_options_3648_ = lean_ctor_get(v_toCold_3647_, 2);
v_hasTrace_3649_ = lean_ctor_get_uint8(v_options_3648_, sizeof(void*)*1);
if (v_hasTrace_3649_ == 0)
{
lean_object* v___x_3650_; 
lean_dec_ref(v_xs_3640_);
lean_dec_ref(v_f_3639_);
lean_inc(v_a_3645_);
lean_inc_ref(v_a_3644_);
lean_inc(v_a_3643_);
lean_inc_ref(v_a_3642_);
v___x_3650_ = lean_apply_5(v_k_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, lean_box(0));
return v___x_3650_;
}
else
{
lean_object* v_inheritedTraceOptions_3651_; lean_object* v___f_3652_; lean_object* v___y_3654_; lean_object* v_a_3655_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v_a_3687_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v_a_3702_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v_a_3707_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v_a_3712_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v_a_3724_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v_a_3736_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v_a_3741_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v_a_3746_; 
v_inheritedTraceOptions_3651_ = lean_ctor_get(v_toCold_3647_, 11);
v___f_3652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3652_, 0, v_f_3639_);
lean_closure_set(v___f_3652_, 1, v_xs_3640_);
v___x_3680_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3681_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3682_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3683_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3651_, v_options_3648_, v___x_3682_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3780_; uint8_t v___x_3781_; 
v___x_3780_ = l_Lean_trace_profiler;
v___x_3781_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3648_, v___x_3780_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; 
lean_dec_ref(v___f_3652_);
lean_inc(v_a_3645_);
lean_inc_ref(v_a_3644_);
lean_inc(v_a_3643_);
lean_inc_ref(v_a_3642_);
v___x_3782_ = lean_apply_5(v_k_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, lean_box(0));
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
v___x_3784_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3785_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3651_, v_options_3648_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_dec(v_a_3783_);
return v___x_3782_;
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_dec_ref_known(v___x_3782_, 1);
lean_inc(v_a_3783_);
v___x_3787_ = l_Lean_MessageData_ofExpr(v_a_3783_);
v___x_3788_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3784_, v___x_3787_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; 
v_unused_3796_ = lean_ctor_get(v___x_3788_, 0);
lean_dec(v_unused_3796_);
v___x_3790_ = v___x_3788_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_dec(v___x_3788_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v_a_3783_);
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3783_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_a_3783_);
v_a_3797_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3788_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3788_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
lean_inc(v_a_3797_);
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
v___y_3654_ = v___x_3802_;
v_a_3655_ = v_a_3797_;
goto v___jp_3653_;
}
}
}
}
}
else
{
lean_object* v_a_3805_; 
v_a_3805_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3805_);
v___y_3654_ = v___x_3782_;
v_a_3655_ = v_a_3805_;
goto v___jp_3653_;
}
}
else
{
goto v___jp_3755_;
}
}
else
{
goto v___jp_3755_;
}
v___jp_3653_:
{
uint8_t v___x_3656_; 
v___x_3656_ = l_Lean_Exception_isInterrupt(v_a_3655_);
if (v___x_3656_ == 0)
{
uint8_t v___x_3657_; 
lean_inc_ref(v_a_3655_);
v___x_3657_ = l_Lean_Exception_isRuntime(v_a_3655_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
lean_dec_ref(v___y_3654_);
v___x_3658_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3659_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3651_, v_options_3648_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_a_3655_);
return v___x_3661_;
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_inc_ref(v_a_3655_);
v___x_3662_ = l_Lean_Exception_toMessageData(v_a_3655_);
v___x_3663_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3658_, v___x_3662_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; 
v_unused_3671_ = lean_ctor_get(v___x_3663_, 0);
lean_dec(v_unused_3671_);
v___x_3665_ = v___x_3663_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_dec(v___x_3663_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
lean_ctor_set_tag(v___x_3665_, 1);
lean_ctor_set(v___x_3665_, 0, v_a_3655_);
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3655_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec_ref(v_a_3655_);
v_a_3672_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3663_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3663_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3655_);
return v___y_3654_;
}
}
else
{
lean_dec_ref(v_a_3655_);
return v___y_3654_;
}
}
v___jp_3684_:
{
lean_object* v___x_3688_; double v___x_3689_; double v___x_3690_; double v___x_3691_; double v___x_3692_; double v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3688_ = lean_io_mono_nanos_now();
v___x_3689_ = lean_float_of_nat(v___y_3686_);
v___x_3690_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3691_ = lean_float_div(v___x_3689_, v___x_3690_);
v___x_3692_ = lean_float_of_nat(v___x_3688_);
v___x_3693_ = lean_float_div(v___x_3692_, v___x_3690_);
v___x_3694_ = lean_box_float(v___x_3691_);
v___x_3695_ = lean_box_float(v___x_3693_);
v___x_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v_a_3687_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3680_, v_hasTrace_3649_, v___x_3681_, v_options_3648_, v___x_3683_, v___y_3685_, v___f_3652_, v___x_3697_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
return v___x_3698_;
}
v___jp_3699_:
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_a_3702_);
v___y_3685_ = v___y_3700_;
v___y_3686_ = v___y_3701_;
v_a_3687_ = v___x_3703_;
goto v___jp_3684_;
}
v___jp_3704_:
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3708_, 0, v_a_3707_);
v___y_3685_ = v___y_3705_;
v___y_3686_ = v___y_3706_;
v_a_3687_ = v___x_3708_;
goto v___jp_3684_;
}
v___jp_3709_:
{
uint8_t v___x_3713_; 
v___x_3713_ = l_Lean_Exception_isInterrupt(v_a_3712_);
if (v___x_3713_ == 0)
{
uint8_t v___x_3714_; 
lean_inc_ref(v_a_3712_);
v___x_3714_ = l_Lean_Exception_isRuntime(v_a_3712_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3715_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3716_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3651_, v_options_3648_, v___x_3716_);
if (v___x_3717_ == 0)
{
v___y_3705_ = v___y_3710_;
v___y_3706_ = v___y_3711_;
v_a_3707_ = v_a_3712_;
goto v___jp_3704_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_inc_ref(v_a_3712_);
v___x_3718_ = l_Lean_Exception_toMessageData(v_a_3712_);
v___x_3719_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3715_, v___x_3718_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_dec_ref_known(v___x_3719_, 1);
v___y_3705_ = v___y_3710_;
v___y_3706_ = v___y_3711_;
v_a_3707_ = v_a_3712_;
goto v___jp_3704_;
}
else
{
lean_object* v_a_3720_; 
lean_dec_ref(v_a_3712_);
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3719_, 1);
v___y_3705_ = v___y_3710_;
v___y_3706_ = v___y_3711_;
v_a_3707_ = v_a_3720_;
goto v___jp_3704_;
}
}
}
else
{
v___y_3705_ = v___y_3710_;
v___y_3706_ = v___y_3711_;
v_a_3707_ = v_a_3712_;
goto v___jp_3704_;
}
}
else
{
v___y_3705_ = v___y_3710_;
v___y_3706_ = v___y_3711_;
v_a_3707_ = v_a_3712_;
goto v___jp_3704_;
}
}
v___jp_3721_:
{
lean_object* v___x_3725_; double v___x_3726_; double v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3725_ = lean_io_get_num_heartbeats();
v___x_3726_ = lean_float_of_nat(v___y_3723_);
v___x_3727_ = lean_float_of_nat(v___x_3725_);
v___x_3728_ = lean_box_float(v___x_3726_);
v___x_3729_ = lean_box_float(v___x_3727_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v_a_3724_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3680_, v_hasTrace_3649_, v___x_3681_, v_options_3648_, v___x_3683_, v___y_3722_, v___f_3652_, v___x_3731_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
return v___x_3732_;
}
v___jp_3733_:
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3737_, 0, v_a_3736_);
v___y_3722_ = v___y_3734_;
v___y_3723_ = v___y_3735_;
v_a_3724_ = v___x_3737_;
goto v___jp_3721_;
}
v___jp_3738_:
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v_a_3741_);
v___y_3722_ = v___y_3739_;
v___y_3723_ = v___y_3740_;
v_a_3724_ = v___x_3742_;
goto v___jp_3721_;
}
v___jp_3743_:
{
uint8_t v___x_3747_; 
v___x_3747_ = l_Lean_Exception_isInterrupt(v_a_3746_);
if (v___x_3747_ == 0)
{
uint8_t v___x_3748_; 
lean_inc_ref(v_a_3746_);
v___x_3748_ = l_Lean_Exception_isRuntime(v_a_3746_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3749_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3750_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3751_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3651_, v_options_3648_, v___x_3750_);
if (v___x_3751_ == 0)
{
v___y_3739_ = v___y_3744_;
v___y_3740_ = v___y_3745_;
v_a_3741_ = v_a_3746_;
goto v___jp_3738_;
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_inc_ref(v_a_3746_);
v___x_3752_ = l_Lean_Exception_toMessageData(v_a_3746_);
v___x_3753_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3749_, v___x_3752_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_dec_ref_known(v___x_3753_, 1);
v___y_3739_ = v___y_3744_;
v___y_3740_ = v___y_3745_;
v_a_3741_ = v_a_3746_;
goto v___jp_3738_;
}
else
{
lean_object* v_a_3754_; 
lean_dec_ref(v_a_3746_);
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3753_, 1);
v___y_3739_ = v___y_3744_;
v___y_3740_ = v___y_3745_;
v_a_3741_ = v_a_3754_;
goto v___jp_3738_;
}
}
}
else
{
v___y_3739_ = v___y_3744_;
v___y_3740_ = v___y_3745_;
v_a_3741_ = v_a_3746_;
goto v___jp_3738_;
}
}
else
{
v___y_3739_ = v___y_3744_;
v___y_3740_ = v___y_3745_;
v_a_3741_ = v_a_3746_;
goto v___jp_3738_;
}
}
v___jp_3755_:
{
lean_object* v___x_3756_; lean_object* v_a_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3756_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3645_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref(v___x_3756_);
v___x_3758_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3759_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3648_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_io_mono_nanos_now();
lean_inc(v_a_3645_);
lean_inc_ref(v_a_3644_);
lean_inc(v_a_3643_);
lean_inc_ref(v_a_3642_);
v___x_3761_ = lean_apply_5(v_k_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, lean_box(0));
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v___x_3763_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3764_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3765_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3651_, v_options_3648_, v___x_3764_);
if (v___x_3765_ == 0)
{
v___y_3700_ = v_a_3757_;
v___y_3701_ = v___x_3760_;
v_a_3702_ = v_a_3762_;
goto v___jp_3699_;
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
lean_inc(v_a_3762_);
v___x_3766_ = l_Lean_MessageData_ofExpr(v_a_3762_);
v___x_3767_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3763_, v___x_3766_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_dec_ref_known(v___x_3767_, 1);
v___y_3700_ = v_a_3757_;
v___y_3701_ = v___x_3760_;
v_a_3702_ = v_a_3762_;
goto v___jp_3699_;
}
else
{
lean_object* v_a_3768_; 
lean_dec(v_a_3762_);
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v___y_3710_ = v_a_3757_;
v___y_3711_ = v___x_3760_;
v_a_3712_ = v_a_3768_;
goto v___jp_3709_;
}
}
}
else
{
lean_object* v_a_3769_; 
v_a_3769_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v___x_3761_, 1);
v___y_3710_ = v_a_3757_;
v___y_3711_ = v___x_3760_;
v_a_3712_ = v_a_3769_;
goto v___jp_3709_;
}
}
else
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3645_);
lean_inc_ref(v_a_3644_);
lean_inc(v_a_3643_);
lean_inc_ref(v_a_3642_);
v___x_3771_ = lean_apply_5(v_k_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, lean_box(0));
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3774_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3775_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3651_, v_options_3648_, v___x_3774_);
if (v___x_3775_ == 0)
{
v___y_3734_ = v_a_3757_;
v___y_3735_ = v___x_3770_;
v_a_3736_ = v_a_3772_;
goto v___jp_3733_;
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_inc(v_a_3772_);
v___x_3776_ = l_Lean_MessageData_ofExpr(v_a_3772_);
v___x_3777_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3773_, v___x_3776_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_dec_ref_known(v___x_3777_, 1);
v___y_3734_ = v_a_3757_;
v___y_3735_ = v___x_3770_;
v_a_3736_ = v_a_3772_;
goto v___jp_3733_;
}
else
{
lean_object* v_a_3778_; 
lean_dec(v_a_3772_);
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3777_, 1);
v___y_3744_ = v_a_3757_;
v___y_3745_ = v___x_3770_;
v_a_3746_ = v_a_3778_;
goto v___jp_3743_;
}
}
}
else
{
lean_object* v_a_3779_; 
v_a_3779_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3771_, 1);
v___y_3744_ = v_a_3757_;
v___y_3745_ = v___x_3770_;
v_a_3746_ = v_a_3779_;
goto v___jp_3743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3806_, lean_object* v_xs_3807_, lean_object* v_k_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3806_, v_xs_3807_, v_k_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3815_, lean_object* v_xs_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v___x_3822_; 
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc_ref(v_f_3815_);
v___x_3822_ = lean_infer_type(v_f_3815_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___x_3822_, 1);
lean_inc_ref(v_xs_3816_);
lean_inc_ref(v_f_3815_);
v___x_3824_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3824_, 0, v_f_3815_);
lean_closure_set(v___x_3824_, 1, v_a_3823_);
lean_closure_set(v___x_3824_, 2, v_xs_3816_);
v___x_3825_ = 0;
v___x_3826_ = lean_box(v___x_3825_);
v___x_3827_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3827_, 0, lean_box(0));
lean_closure_set(v___x_3827_, 1, v___x_3824_);
lean_closure_set(v___x_3827_, 2, v___x_3826_);
v___x_3828_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3815_, v_xs_3816_, v___x_3827_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
return v___x_3828_;
}
else
{
lean_dec_ref(v_xs_3816_);
lean_dec_ref(v_f_3815_);
return v___x_3822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3829_, lean_object* v_xs_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_Meta_mkAppM_x27(v_f_3829_, v_xs_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3837_, size_t v_i_3838_, size_t v_stop_3839_, lean_object* v_b_3840_){
_start:
{
lean_object* v___y_3842_; uint8_t v___x_3846_; 
v___x_3846_ = lean_usize_dec_eq(v_i_3838_, v_stop_3839_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
v___x_3847_ = lean_array_uget_borrowed(v_as_3837_, v_i_3838_);
if (lean_obj_tag(v___x_3847_) == 0)
{
v___y_3842_ = v_b_3840_;
goto v___jp_3841_;
}
else
{
lean_object* v_val_3848_; lean_object* v___x_3849_; 
v_val_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_val_3848_);
v___x_3849_ = lean_array_push(v_b_3840_, v_val_3848_);
v___y_3842_ = v___x_3849_;
goto v___jp_3841_;
}
}
else
{
return v_b_3840_;
}
v___jp_3841_:
{
size_t v___x_3843_; size_t v___x_3844_; 
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3838_, v___x_3843_);
v_i_3838_ = v___x_3844_;
v_b_3840_ = v___y_3842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3850_, lean_object* v_i_3851_, lean_object* v_stop_3852_, lean_object* v_b_3853_){
_start:
{
size_t v_i_boxed_3854_; size_t v_stop_boxed_3855_; lean_object* v_res_3856_; 
v_i_boxed_3854_ = lean_unbox_usize(v_i_3851_);
lean_dec(v_i_3851_);
v_stop_boxed_3855_ = lean_unbox_usize(v_stop_3852_);
lean_dec(v_stop_3852_);
v_res_3856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3850_, v_i_boxed_3854_, v_stop_boxed_3855_, v_b_3853_);
lean_dec_ref(v_as_3850_);
return v_res_3856_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3864_ = l_Lean_MessageData_ofFormat(v___x_3863_);
return v___x_3864_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_box(1);
v___x_3866_ = l_Lean_MessageData_ofFormat(v___x_3865_);
return v___x_3866_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3871_ = l_Lean_MessageData_ofFormat(v___x_3870_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3872_, lean_object* v_xs_3873_, lean_object* v_x_3874_, lean_object* v_x_3875_, lean_object* v_x_3876_, lean_object* v_x_3877_, lean_object* v_x_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
if (lean_obj_tag(v_x_3878_) == 7)
{
lean_object* v_binderName_3884_; lean_object* v_binderType_3885_; lean_object* v_body_3886_; uint8_t v_binderInfo_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v_binderName_3884_ = lean_ctor_get(v_x_3878_, 0);
lean_inc(v_binderName_3884_);
v_binderType_3885_ = lean_ctor_get(v_x_3878_, 1);
lean_inc_ref(v_binderType_3885_);
v_body_3886_ = lean_ctor_get(v_x_3878_, 2);
lean_inc_ref(v_body_3886_);
v_binderInfo_3887_ = lean_ctor_get_uint8(v_x_3878_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3878_, 3);
v___x_3888_ = lean_array_get_size(v_xs_3873_);
v___x_3889_ = lean_nat_dec_lt(v_x_3874_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_dec_ref(v_body_3886_);
lean_dec_ref(v_binderType_3885_);
lean_dec(v_binderName_3884_);
lean_dec(v_x_3876_);
lean_dec(v_x_3874_);
v___x_3890_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3891_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3890_, v_f_3872_, v_x_3875_, v_x_3877_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec_ref(v_x_3877_);
lean_dec_ref(v_x_3875_);
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; lean_object* v_d_3893_; lean_object* v___x_3894_; 
v___x_3892_ = lean_array_get_size(v_x_3875_);
v_d_3893_ = lean_expr_instantiate_rev_range(v_binderType_3885_, v_x_3876_, v___x_3892_, v_x_3875_);
lean_dec_ref(v_binderType_3885_);
v___x_3894_ = lean_array_fget_borrowed(v_xs_3873_, v_x_3874_);
if (lean_obj_tag(v___x_3894_) == 0)
{
if (v_binderInfo_3887_ == 3)
{
lean_object* v___x_3895_; uint8_t v___x_3896_; lean_object* v___x_3897_; 
v___x_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3895_, 0, v_d_3893_);
v___x_3896_ = 1;
v___x_3897_ = l_Lean_Meta_mkFreshExprMVar(v___x_3895_, v___x_3896_, v_binderName_3884_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc_n(v_a_3898_, 2);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = lean_unsigned_to_nat(1u);
v___x_3900_ = lean_nat_add(v_x_3874_, v___x_3899_);
lean_dec(v_x_3874_);
v___x_3901_ = lean_array_push(v_x_3875_, v_a_3898_);
v___x_3902_ = l_Lean_Expr_mvarId_x21(v_a_3898_);
lean_dec(v_a_3898_);
v___x_3903_ = lean_array_push(v_x_3877_, v___x_3902_);
v_x_3874_ = v___x_3900_;
v_x_3875_ = v___x_3901_;
v_x_3877_ = v___x_3903_;
v_x_3878_ = v_body_3886_;
goto _start;
}
else
{
lean_dec_ref(v_body_3886_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_x_3875_);
lean_dec(v_x_3874_);
lean_dec_ref(v_f_3872_);
return v___x_3897_;
}
}
else
{
lean_object* v___x_3905_; uint8_t v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v_d_3893_);
v___x_3906_ = 0;
v___x_3907_ = l_Lean_Meta_mkFreshExprMVar(v___x_3905_, v___x_3906_, v_binderName_3884_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3909_ = lean_unsigned_to_nat(1u);
v___x_3910_ = lean_nat_add(v_x_3874_, v___x_3909_);
lean_dec(v_x_3874_);
v___x_3911_ = lean_array_push(v_x_3875_, v_a_3908_);
v_x_3874_ = v___x_3910_;
v_x_3875_ = v___x_3911_;
v_x_3878_ = v_body_3886_;
goto _start;
}
else
{
lean_dec_ref(v_body_3886_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_x_3875_);
lean_dec(v_x_3874_);
lean_dec_ref(v_f_3872_);
return v___x_3907_;
}
}
}
else
{
lean_object* v_val_3913_; lean_object* v___x_3914_; 
lean_dec(v_binderName_3884_);
v_val_3913_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3882_);
lean_inc_ref(v_a_3881_);
lean_inc(v_a_3880_);
lean_inc_ref(v_a_3879_);
lean_inc(v_val_3913_);
v___x_3914_ = lean_infer_type(v_val_3913_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v___x_3916_ = l_Lean_Meta_isExprDefEq(v_d_3893_, v_a_3915_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; uint8_t v___x_3918_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = lean_unbox(v_a_3917_);
lean_dec(v_a_3917_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec_ref(v_body_3886_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec(v_x_3874_);
v___x_3919_ = l_Lean_mkAppN(v_f_3872_, v_x_3875_);
lean_dec_ref(v_x_3875_);
lean_inc(v_val_3913_);
v___x_3920_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3919_, v_val_3913_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
return v___x_3920_;
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = lean_unsigned_to_nat(1u);
v___x_3922_ = lean_nat_add(v_x_3874_, v___x_3921_);
lean_dec(v_x_3874_);
lean_inc(v_val_3913_);
v___x_3923_ = lean_array_push(v_x_3875_, v_val_3913_);
v_x_3874_ = v___x_3922_;
v_x_3875_ = v___x_3923_;
v_x_3878_ = v_body_3886_;
goto _start;
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v_body_3886_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_x_3875_);
lean_dec(v_x_3874_);
lean_dec_ref(v_f_3872_);
v_a_3925_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3916_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3916_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_dec_ref(v_d_3893_);
lean_dec_ref(v_body_3886_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_x_3875_);
lean_dec(v_x_3874_);
lean_dec_ref(v_f_3872_);
return v___x_3914_;
}
}
}
}
else
{
lean_object* v___x_3933_; lean_object* v_type_3934_; lean_object* v___x_3935_; 
v___x_3933_ = lean_array_get_size(v_x_3875_);
v_type_3934_ = lean_expr_instantiate_rev_range(v_x_3878_, v_x_3876_, v___x_3933_, v_x_3875_);
lean_dec(v_x_3876_);
lean_dec_ref(v_x_3878_);
v___x_3935_ = l_Lean_Meta_whnfD(v_type_3934_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; uint8_t v___x_3937_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v___x_3937_ = l_Lean_Expr_isForall(v_a_3936_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; uint8_t v___x_3939_; 
lean_dec(v_a_3936_);
v___x_3938_ = lean_array_get_size(v_xs_3873_);
v___x_3939_ = lean_nat_dec_eq(v_x_3874_, v___x_3938_);
lean_dec(v_x_3874_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; lean_object* v___y_3942_; lean_object* v___x_3955_; uint8_t v___x_3956_; 
lean_dec_ref(v_x_3877_);
lean_dec_ref(v_x_3875_);
v___x_3940_ = lean_unsigned_to_nat(0u);
v___x_3955_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3956_ = lean_nat_dec_lt(v___x_3940_, v___x_3938_);
if (v___x_3956_ == 0)
{
v___y_3942_ = v___x_3955_;
goto v___jp_3941_;
}
else
{
size_t v___x_3957_; size_t v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = ((size_t)0ULL);
v___x_3958_ = lean_usize_of_nat(v___x_3938_);
v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3873_, v___x_3957_, v___x_3958_, v___x_3955_);
v___y_3942_ = v___x_3959_;
goto v___jp_3941_;
}
v___jp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3943_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3944_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3945_ = l_Lean_indentExpr(v_f_3872_);
v___x_3946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
v___x_3949_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3952_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3942_, v___x_3940_, v___x_3951_);
lean_dec_ref(v___y_3942_);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3950_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3943_, v___x_3953_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
return v___x_3954_;
}
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3961_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3960_, v_f_3872_, v_x_3875_, v_x_3877_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec_ref(v_x_3877_);
lean_dec_ref(v_x_3875_);
return v___x_3961_;
}
}
else
{
v_x_3876_ = v___x_3933_;
v_x_3878_ = v_a_3936_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3877_);
lean_dec_ref(v_x_3875_);
lean_dec(v_x_3874_);
lean_dec_ref(v_f_3872_);
return v___x_3935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_3963_, lean_object* v_xs_3964_, lean_object* v_x_3965_, lean_object* v_x_3966_, lean_object* v_x_3967_, lean_object* v_x_3968_, lean_object* v_x_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_3963_, v_xs_3964_, v_x_3965_, v_x_3966_, v_x_3967_, v_x_3968_, v_x_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec_ref(v_xs_3964_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_3976_, lean_object* v_xs_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_3976_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v_fst_3985_; lean_object* v_snd_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v___x_3983_, 1);
v_fst_3985_ = lean_ctor_get(v_a_3984_, 0);
lean_inc(v_fst_3985_);
v_snd_3986_ = lean_ctor_get(v_a_3984_, 1);
lean_inc(v_snd_3986_);
lean_dec(v_a_3984_);
v___x_3987_ = lean_unsigned_to_nat(0u);
v___x_3988_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3989_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_3985_, v_xs_3977_, v___x_3987_, v___x_3988_, v___x_3987_, v___x_3988_, v_snd_3986_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
return v___x_3989_;
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
v_a_3990_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3983_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3983_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_3998_, lean_object* v_xs_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_3998_, v_xs_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec_ref(v_xs_3999_);
return v_res_4005_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4010_ = l_Lean_MessageData_ofFormat(v___x_4009_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
if (lean_obj_tag(v_a_4011_) == 0)
{
lean_object* v___x_4013_; 
v___x_4013_ = l_List_reverse___redArg(v_a_4012_);
return v___x_4013_;
}
else
{
lean_object* v_head_4014_; lean_object* v_tail_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4028_; 
v_head_4014_ = lean_ctor_get(v_a_4011_, 0);
v_tail_4015_ = lean_ctor_get(v_a_4011_, 1);
v_isSharedCheck_4028_ = !lean_is_exclusive(v_a_4011_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4017_ = v_a_4011_;
v_isShared_4018_ = v_isSharedCheck_4028_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_tail_4015_);
lean_inc(v_head_4014_);
lean_dec(v_a_4011_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4028_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___y_4020_; 
if (lean_obj_tag(v_head_4014_) == 0)
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4020_ = v___x_4025_;
goto v___jp_4019_;
}
else
{
lean_object* v_val_4026_; lean_object* v___x_4027_; 
v_val_4026_ = lean_ctor_get(v_head_4014_, 0);
lean_inc(v_val_4026_);
lean_dec_ref_known(v_head_4014_, 1);
v___x_4027_ = l_Lean_MessageData_ofExpr(v_val_4026_);
v___y_4020_ = v___x_4027_;
goto v___jp_4019_;
}
v___jp_4019_:
{
lean_object* v___x_4022_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v_a_4012_);
lean_ctor_set(v___x_4017_, 0, v___y_4020_);
v___x_4022_ = v___x_4017_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___y_4020_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_a_4012_);
v___x_4022_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
v_a_4011_ = v_tail_4015_;
v_a_4012_ = v___x_4022_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4029_, lean_object* v_xs_4030_, lean_object* v_x_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4037_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4038_ = l_Lean_MessageData_ofName(v_f_4029_);
v___x_4039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4039_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = lean_array_to_list(v_xs_4030_);
v___x_4043_ = lean_box(0);
v___x_4044_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4042_, v___x_4043_);
v___x_4045_ = l_Lean_MessageData_ofList(v___x_4044_);
v___x_4046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4041_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4048_, lean_object* v_xs_4049_, lean_object* v_x_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4048_, v_xs_4049_, v_x_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec_ref(v_x_4050_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4057_, lean_object* v_xs_4058_, lean_object* v_k_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v_toCold_4065_; lean_object* v_options_4066_; uint8_t v_hasTrace_4067_; 
v_toCold_4065_ = lean_ctor_get(v_a_4062_, 0);
v_options_4066_ = lean_ctor_get(v_toCold_4065_, 2);
v_hasTrace_4067_ = lean_ctor_get_uint8(v_options_4066_, sizeof(void*)*1);
if (v_hasTrace_4067_ == 0)
{
lean_object* v___x_4068_; 
lean_dec_ref(v_xs_4058_);
lean_dec(v_f_4057_);
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
v___x_4068_ = lean_apply_5(v_k_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, lean_box(0));
return v___x_4068_;
}
else
{
lean_object* v_inheritedTraceOptions_4069_; lean_object* v___f_4070_; lean_object* v___y_4072_; lean_object* v_a_4073_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v_a_4105_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v_a_4120_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v_a_4125_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v_a_4130_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v_a_4142_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v_a_4154_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v_a_4159_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v_a_4164_; 
v_inheritedTraceOptions_4069_ = lean_ctor_get(v_toCold_4065_, 11);
v___f_4070_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4070_, 0, v_f_4057_);
lean_closure_set(v___f_4070_, 1, v_xs_4058_);
v___x_4098_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4099_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4100_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4101_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4069_, v_options_4066_, v___x_4100_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4198_; uint8_t v___x_4199_; 
v___x_4198_ = l_Lean_trace_profiler;
v___x_4199_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4066_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; 
lean_dec_ref(v___f_4070_);
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
v___x_4200_ = lean_apply_5(v_k_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, lean_box(0));
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
v___x_4202_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4203_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4204_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4069_, v_options_4066_, v___x_4203_);
if (v___x_4204_ == 0)
{
lean_dec(v_a_4201_);
return v___x_4200_;
}
else
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec_ref_known(v___x_4200_, 1);
lean_inc(v_a_4201_);
v___x_4205_ = l_Lean_MessageData_ofExpr(v_a_4201_);
v___x_4206_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4202_, v___x_4205_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4213_ == 0)
{
lean_object* v_unused_4214_; 
v_unused_4214_ = lean_ctor_get(v___x_4206_, 0);
lean_dec(v_unused_4214_);
v___x_4208_ = v___x_4206_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_dec(v___x_4206_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 0, v_a_4201_);
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4201_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec(v_a_4201_);
v_a_4215_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4206_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4206_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
lean_inc(v_a_4215_);
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
v___y_4072_ = v___x_4220_;
v_a_4073_ = v_a_4215_;
goto v___jp_4071_;
}
}
}
}
}
else
{
lean_object* v_a_4223_; 
v_a_4223_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4223_);
v___y_4072_ = v___x_4200_;
v_a_4073_ = v_a_4223_;
goto v___jp_4071_;
}
}
else
{
goto v___jp_4173_;
}
}
else
{
goto v___jp_4173_;
}
v___jp_4071_:
{
uint8_t v___x_4074_; 
v___x_4074_ = l_Lean_Exception_isInterrupt(v_a_4073_);
if (v___x_4074_ == 0)
{
uint8_t v___x_4075_; 
lean_inc_ref(v_a_4073_);
v___x_4075_ = l_Lean_Exception_isRuntime(v_a_4073_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
lean_dec_ref(v___y_4072_);
v___x_4076_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4077_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4078_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4069_, v_options_4066_, v___x_4077_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4079_, 0, v_a_4073_);
return v___x_4079_;
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
lean_inc_ref(v_a_4073_);
v___x_4080_ = l_Lean_Exception_toMessageData(v_a_4073_);
v___x_4081_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4076_, v___x_4080_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; 
v_unused_4089_ = lean_ctor_get(v___x_4081_, 0);
lean_dec(v_unused_4089_);
v___x_4083_ = v___x_4081_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_dec(v___x_4081_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
lean_ctor_set_tag(v___x_4083_, 1);
lean_ctor_set(v___x_4083_, 0, v_a_4073_);
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4073_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec_ref(v_a_4073_);
v_a_4090_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4081_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4081_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_4073_);
return v___y_4072_;
}
}
else
{
lean_dec_ref(v_a_4073_);
return v___y_4072_;
}
}
v___jp_4102_:
{
lean_object* v___x_4106_; double v___x_4107_; double v___x_4108_; double v___x_4109_; double v___x_4110_; double v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4106_ = lean_io_mono_nanos_now();
v___x_4107_ = lean_float_of_nat(v___y_4104_);
v___x_4108_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4109_ = lean_float_div(v___x_4107_, v___x_4108_);
v___x_4110_ = lean_float_of_nat(v___x_4106_);
v___x_4111_ = lean_float_div(v___x_4110_, v___x_4108_);
v___x_4112_ = lean_box_float(v___x_4109_);
v___x_4113_ = lean_box_float(v___x_4111_);
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4112_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v_a_4105_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4098_, v_hasTrace_4067_, v___x_4099_, v_options_4066_, v___x_4101_, v___y_4103_, v___f_4070_, v___x_4115_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
return v___x_4116_;
}
v___jp_4117_:
{
lean_object* v___x_4121_; 
v___x_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4121_, 0, v_a_4120_);
v___y_4103_ = v___y_4118_;
v___y_4104_ = v___y_4119_;
v_a_4105_ = v___x_4121_;
goto v___jp_4102_;
}
v___jp_4122_:
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v_a_4125_);
v___y_4103_ = v___y_4123_;
v___y_4104_ = v___y_4124_;
v_a_4105_ = v___x_4126_;
goto v___jp_4102_;
}
v___jp_4127_:
{
uint8_t v___x_4131_; 
v___x_4131_ = l_Lean_Exception_isInterrupt(v_a_4130_);
if (v___x_4131_ == 0)
{
uint8_t v___x_4132_; 
lean_inc_ref(v_a_4130_);
v___x_4132_ = l_Lean_Exception_isRuntime(v_a_4130_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4133_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4134_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4135_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4069_, v_options_4066_, v___x_4134_);
if (v___x_4135_ == 0)
{
v___y_4123_ = v___y_4128_;
v___y_4124_ = v___y_4129_;
v_a_4125_ = v_a_4130_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
lean_inc_ref(v_a_4130_);
v___x_4136_ = l_Lean_Exception_toMessageData(v_a_4130_);
v___x_4137_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4133_, v___x_4136_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_dec_ref_known(v___x_4137_, 1);
v___y_4123_ = v___y_4128_;
v___y_4124_ = v___y_4129_;
v_a_4125_ = v_a_4130_;
goto v___jp_4122_;
}
else
{
lean_object* v_a_4138_; 
lean_dec_ref(v_a_4130_);
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4137_, 1);
v___y_4123_ = v___y_4128_;
v___y_4124_ = v___y_4129_;
v_a_4125_ = v_a_4138_;
goto v___jp_4122_;
}
}
}
else
{
v___y_4123_ = v___y_4128_;
v___y_4124_ = v___y_4129_;
v_a_4125_ = v_a_4130_;
goto v___jp_4122_;
}
}
else
{
v___y_4123_ = v___y_4128_;
v___y_4124_ = v___y_4129_;
v_a_4125_ = v_a_4130_;
goto v___jp_4122_;
}
}
v___jp_4139_:
{
lean_object* v___x_4143_; double v___x_4144_; double v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4143_ = lean_io_get_num_heartbeats();
v___x_4144_ = lean_float_of_nat(v___y_4141_);
v___x_4145_ = lean_float_of_nat(v___x_4143_);
v___x_4146_ = lean_box_float(v___x_4144_);
v___x_4147_ = lean_box_float(v___x_4145_);
v___x_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4149_, 0, v_a_4142_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
v___x_4150_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4098_, v_hasTrace_4067_, v___x_4099_, v_options_4066_, v___x_4101_, v___y_4140_, v___f_4070_, v___x_4149_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
return v___x_4150_;
}
v___jp_4151_:
{
lean_object* v___x_4155_; 
v___x_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_a_4154_);
v___y_4140_ = v___y_4152_;
v___y_4141_ = v___y_4153_;
v_a_4142_ = v___x_4155_;
goto v___jp_4139_;
}
v___jp_4156_:
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v_a_4159_);
v___y_4140_ = v___y_4157_;
v___y_4141_ = v___y_4158_;
v_a_4142_ = v___x_4160_;
goto v___jp_4139_;
}
v___jp_4161_:
{
uint8_t v___x_4165_; 
v___x_4165_ = l_Lean_Exception_isInterrupt(v_a_4164_);
if (v___x_4165_ == 0)
{
uint8_t v___x_4166_; 
lean_inc_ref(v_a_4164_);
v___x_4166_ = l_Lean_Exception_isRuntime(v_a_4164_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v___x_4167_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4168_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4169_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4069_, v_options_4066_, v___x_4168_);
if (v___x_4169_ == 0)
{
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v_a_4164_;
goto v___jp_4156_;
}
else
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
lean_inc_ref(v_a_4164_);
v___x_4170_ = l_Lean_Exception_toMessageData(v_a_4164_);
v___x_4171_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4167_, v___x_4170_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_dec_ref_known(v___x_4171_, 1);
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v_a_4164_;
goto v___jp_4156_;
}
else
{
lean_object* v_a_4172_; 
lean_dec_ref(v_a_4164_);
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v_a_4172_;
goto v___jp_4156_;
}
}
}
else
{
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v_a_4164_;
goto v___jp_4156_;
}
}
else
{
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v_a_4164_;
goto v___jp_4156_;
}
}
v___jp_4173_:
{
lean_object* v___x_4174_; lean_object* v_a_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; 
v___x_4174_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4063_);
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref(v___x_4174_);
v___x_4176_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4177_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4066_, v___x_4176_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_io_mono_nanos_now();
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
v___x_4179_ = lean_apply_5(v_k_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, lean_box(0));
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v___x_4181_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4182_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4183_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4069_, v_options_4066_, v___x_4182_);
if (v___x_4183_ == 0)
{
v___y_4118_ = v_a_4175_;
v___y_4119_ = v___x_4178_;
v_a_4120_ = v_a_4180_;
goto v___jp_4117_;
}
else
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_inc(v_a_4180_);
v___x_4184_ = l_Lean_MessageData_ofExpr(v_a_4180_);
v___x_4185_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4181_, v___x_4184_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_dec_ref_known(v___x_4185_, 1);
v___y_4118_ = v_a_4175_;
v___y_4119_ = v___x_4178_;
v_a_4120_ = v_a_4180_;
goto v___jp_4117_;
}
else
{
lean_object* v_a_4186_; 
lean_dec(v_a_4180_);
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4185_, 1);
v___y_4128_ = v_a_4175_;
v___y_4129_ = v___x_4178_;
v_a_4130_ = v_a_4186_;
goto v___jp_4127_;
}
}
}
else
{
lean_object* v_a_4187_; 
v_a_4187_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4179_, 1);
v___y_4128_ = v_a_4175_;
v___y_4129_ = v___x_4178_;
v_a_4130_ = v_a_4187_;
goto v___jp_4127_;
}
}
else
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
v___x_4189_ = lean_apply_5(v_k_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, lean_box(0));
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4192_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4193_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4069_, v_options_4066_, v___x_4192_);
if (v___x_4193_ == 0)
{
v___y_4152_ = v_a_4175_;
v___y_4153_ = v___x_4188_;
v_a_4154_ = v_a_4190_;
goto v___jp_4151_;
}
else
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_inc(v_a_4190_);
v___x_4194_ = l_Lean_MessageData_ofExpr(v_a_4190_);
v___x_4195_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4191_, v___x_4194_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_dec_ref_known(v___x_4195_, 1);
v___y_4152_ = v_a_4175_;
v___y_4153_ = v___x_4188_;
v_a_4154_ = v_a_4190_;
goto v___jp_4151_;
}
else
{
lean_object* v_a_4196_; 
lean_dec(v_a_4190_);
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4195_, 1);
v___y_4162_ = v_a_4175_;
v___y_4163_ = v___x_4188_;
v_a_4164_ = v_a_4196_;
goto v___jp_4161_;
}
}
}
else
{
lean_object* v_a_4197_; 
v_a_4197_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4189_, 1);
v___y_4162_ = v_a_4175_;
v___y_4163_ = v___x_4188_;
v_a_4164_ = v_a_4197_;
goto v___jp_4161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4224_, lean_object* v_xs_4225_, lean_object* v_k_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4224_, v_xs_4225_, v_k_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_);
lean_dec(v_a_4230_);
lean_dec_ref(v_a_4229_);
lean_dec(v_a_4228_);
lean_dec_ref(v_a_4227_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4233_, lean_object* v_xs_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v___f_4240_; uint8_t v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
lean_inc_ref(v_xs_4234_);
lean_inc(v_constName_4233_);
v___f_4240_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4240_, 0, v_constName_4233_);
lean_closure_set(v___f_4240_, 1, v_xs_4234_);
v___x_4241_ = 0;
v___x_4242_ = lean_box(v___x_4241_);
v___x_4243_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4243_, 0, lean_box(0));
lean_closure_set(v___x_4243_, 1, v___f_4240_);
lean_closure_set(v___x_4243_, 2, v___x_4242_);
v___x_4244_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4233_, v_xs_4234_, v___x_4243_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4245_, lean_object* v_xs_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_Meta_mkAppOptM(v_constName_4245_, v_xs_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
lean_dec(v_a_4248_);
lean_dec_ref(v_a_4247_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4253_, lean_object* v_xs_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4261_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4262_ = l_Lean_MessageData_ofExpr(v_f_4253_);
v___x_4263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4261_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = lean_array_to_list(v_xs_4254_);
v___x_4267_ = lean_box(0);
v___x_4268_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4266_, v___x_4267_);
v___x_4269_ = l_Lean_MessageData_ofList(v___x_4268_);
v___x_4270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4265_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4272_, lean_object* v_xs_4273_, lean_object* v_x_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4272_, v_xs_4273_, v_x_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec_ref(v_x_4274_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4281_, lean_object* v_xs_4282_, lean_object* v_k_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v_toCold_4289_; lean_object* v_options_4290_; uint8_t v_hasTrace_4291_; 
v_toCold_4289_ = lean_ctor_get(v_a_4286_, 0);
v_options_4290_ = lean_ctor_get(v_toCold_4289_, 2);
v_hasTrace_4291_ = lean_ctor_get_uint8(v_options_4290_, sizeof(void*)*1);
if (v_hasTrace_4291_ == 0)
{
lean_object* v___x_4292_; 
lean_dec_ref(v_xs_4282_);
lean_dec_ref(v_f_4281_);
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
lean_inc(v_a_4285_);
lean_inc_ref(v_a_4284_);
v___x_4292_ = lean_apply_5(v_k_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, lean_box(0));
return v___x_4292_;
}
else
{
lean_object* v_inheritedTraceOptions_4293_; lean_object* v___f_4294_; lean_object* v___y_4296_; lean_object* v_a_4297_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v_a_4329_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v_a_4344_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v_a_4349_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v_a_4354_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v_a_4366_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v_a_4378_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v_a_4383_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v_a_4388_; 
v_inheritedTraceOptions_4293_ = lean_ctor_get(v_toCold_4289_, 11);
v___f_4294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4294_, 0, v_f_4281_);
lean_closure_set(v___f_4294_, 1, v_xs_4282_);
v___x_4322_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4323_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4324_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4325_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4293_, v_options_4290_, v___x_4324_);
if (v___x_4325_ == 0)
{
lean_object* v___x_4422_; uint8_t v___x_4423_; 
v___x_4422_ = l_Lean_trace_profiler;
v___x_4423_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4290_, v___x_4422_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; 
lean_dec_ref(v___f_4294_);
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
lean_inc(v_a_4285_);
lean_inc_ref(v_a_4284_);
v___x_4424_ = lean_apply_5(v_k_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, lean_box(0));
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
v___x_4426_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4427_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4428_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4293_, v_options_4290_, v___x_4427_);
if (v___x_4428_ == 0)
{
lean_dec(v_a_4425_);
return v___x_4424_;
}
else
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
lean_dec_ref_known(v___x_4424_, 1);
lean_inc(v_a_4425_);
v___x_4429_ = l_Lean_MessageData_ofExpr(v_a_4425_);
v___x_4430_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4426_, v___x_4429_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4437_ == 0)
{
lean_object* v_unused_4438_; 
v_unused_4438_ = lean_ctor_get(v___x_4430_, 0);
lean_dec(v_unused_4438_);
v___x_4432_ = v___x_4430_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_dec(v___x_4430_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v_a_4425_);
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4425_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_dec(v_a_4425_);
v_a_4439_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4430_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4430_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
lean_inc(v_a_4439_);
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
v___y_4296_ = v___x_4444_;
v_a_4297_ = v_a_4439_;
goto v___jp_4295_;
}
}
}
}
}
else
{
lean_object* v_a_4447_; 
v_a_4447_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4447_);
v___y_4296_ = v___x_4424_;
v_a_4297_ = v_a_4447_;
goto v___jp_4295_;
}
}
else
{
goto v___jp_4397_;
}
}
else
{
goto v___jp_4397_;
}
v___jp_4295_:
{
uint8_t v___x_4298_; 
v___x_4298_ = l_Lean_Exception_isInterrupt(v_a_4297_);
if (v___x_4298_ == 0)
{
uint8_t v___x_4299_; 
lean_inc_ref(v_a_4297_);
v___x_4299_ = l_Lean_Exception_isRuntime(v_a_4297_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; 
lean_dec_ref(v___y_4296_);
v___x_4300_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4301_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4302_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4293_, v_options_4290_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_a_4297_);
return v___x_4303_;
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
lean_inc_ref(v_a_4297_);
v___x_4304_ = l_Lean_Exception_toMessageData(v_a_4297_);
v___x_4305_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4300_, v___x_4304_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4312_ == 0)
{
lean_object* v_unused_4313_; 
v_unused_4313_ = lean_ctor_get(v___x_4305_, 0);
lean_dec(v_unused_4313_);
v___x_4307_ = v___x_4305_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_dec(v___x_4305_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set_tag(v___x_4307_, 1);
lean_ctor_set(v___x_4307_, 0, v_a_4297_);
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4297_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec_ref(v_a_4297_);
v_a_4314_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4305_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4305_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_4297_);
return v___y_4296_;
}
}
else
{
lean_dec_ref(v_a_4297_);
return v___y_4296_;
}
}
v___jp_4326_:
{
lean_object* v___x_4330_; double v___x_4331_; double v___x_4332_; double v___x_4333_; double v___x_4334_; double v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4330_ = lean_io_mono_nanos_now();
v___x_4331_ = lean_float_of_nat(v___y_4327_);
v___x_4332_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4333_ = lean_float_div(v___x_4331_, v___x_4332_);
v___x_4334_ = lean_float_of_nat(v___x_4330_);
v___x_4335_ = lean_float_div(v___x_4334_, v___x_4332_);
v___x_4336_ = lean_box_float(v___x_4333_);
v___x_4337_ = lean_box_float(v___x_4335_);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4339_, 0, v_a_4329_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
v___x_4340_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4322_, v_hasTrace_4291_, v___x_4323_, v_options_4290_, v___x_4325_, v___y_4328_, v___f_4294_, v___x_4339_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
return v___x_4340_;
}
v___jp_4341_:
{
lean_object* v___x_4345_; 
v___x_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4345_, 0, v_a_4344_);
v___y_4327_ = v___y_4342_;
v___y_4328_ = v___y_4343_;
v_a_4329_ = v___x_4345_;
goto v___jp_4326_;
}
v___jp_4346_:
{
lean_object* v___x_4350_; 
v___x_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4350_, 0, v_a_4349_);
v___y_4327_ = v___y_4347_;
v___y_4328_ = v___y_4348_;
v_a_4329_ = v___x_4350_;
goto v___jp_4326_;
}
v___jp_4351_:
{
uint8_t v___x_4355_; 
v___x_4355_ = l_Lean_Exception_isInterrupt(v_a_4354_);
if (v___x_4355_ == 0)
{
uint8_t v___x_4356_; 
lean_inc_ref(v_a_4354_);
v___x_4356_ = l_Lean_Exception_isRuntime(v_a_4354_);
if (v___x_4356_ == 0)
{
lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4357_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4358_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4359_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4293_, v_options_4290_, v___x_4358_);
if (v___x_4359_ == 0)
{
v___y_4347_ = v___y_4352_;
v___y_4348_ = v___y_4353_;
v_a_4349_ = v_a_4354_;
goto v___jp_4346_;
}
else
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
lean_inc_ref(v_a_4354_);
v___x_4360_ = l_Lean_Exception_toMessageData(v_a_4354_);
v___x_4361_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4357_, v___x_4360_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_dec_ref_known(v___x_4361_, 1);
v___y_4347_ = v___y_4352_;
v___y_4348_ = v___y_4353_;
v_a_4349_ = v_a_4354_;
goto v___jp_4346_;
}
else
{
lean_object* v_a_4362_; 
lean_dec_ref(v_a_4354_);
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
v___y_4347_ = v___y_4352_;
v___y_4348_ = v___y_4353_;
v_a_4349_ = v_a_4362_;
goto v___jp_4346_;
}
}
}
else
{
v___y_4347_ = v___y_4352_;
v___y_4348_ = v___y_4353_;
v_a_4349_ = v_a_4354_;
goto v___jp_4346_;
}
}
else
{
v___y_4347_ = v___y_4352_;
v___y_4348_ = v___y_4353_;
v_a_4349_ = v_a_4354_;
goto v___jp_4346_;
}
}
v___jp_4363_:
{
lean_object* v___x_4367_; double v___x_4368_; double v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4367_ = lean_io_get_num_heartbeats();
v___x_4368_ = lean_float_of_nat(v___y_4364_);
v___x_4369_ = lean_float_of_nat(v___x_4367_);
v___x_4370_ = lean_box_float(v___x_4368_);
v___x_4371_ = lean_box_float(v___x_4369_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4373_, 0, v_a_4366_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4322_, v_hasTrace_4291_, v___x_4323_, v_options_4290_, v___x_4325_, v___y_4365_, v___f_4294_, v___x_4373_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
return v___x_4374_;
}
v___jp_4375_:
{
lean_object* v___x_4379_; 
v___x_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4379_, 0, v_a_4378_);
v___y_4364_ = v___y_4376_;
v___y_4365_ = v___y_4377_;
v_a_4366_ = v___x_4379_;
goto v___jp_4363_;
}
v___jp_4380_:
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v_a_4383_);
v___y_4364_ = v___y_4381_;
v___y_4365_ = v___y_4382_;
v_a_4366_ = v___x_4384_;
goto v___jp_4363_;
}
v___jp_4385_:
{
uint8_t v___x_4389_; 
v___x_4389_ = l_Lean_Exception_isInterrupt(v_a_4388_);
if (v___x_4389_ == 0)
{
uint8_t v___x_4390_; 
lean_inc_ref(v_a_4388_);
v___x_4390_ = l_Lean_Exception_isRuntime(v_a_4388_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v___x_4391_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4392_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4293_, v_options_4290_, v___x_4392_);
if (v___x_4393_ == 0)
{
v___y_4381_ = v___y_4386_;
v___y_4382_ = v___y_4387_;
v_a_4383_ = v_a_4388_;
goto v___jp_4380_;
}
else
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_inc_ref(v_a_4388_);
v___x_4394_ = l_Lean_Exception_toMessageData(v_a_4388_);
v___x_4395_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4391_, v___x_4394_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_dec_ref_known(v___x_4395_, 1);
v___y_4381_ = v___y_4386_;
v___y_4382_ = v___y_4387_;
v_a_4383_ = v_a_4388_;
goto v___jp_4380_;
}
else
{
lean_object* v_a_4396_; 
lean_dec_ref(v_a_4388_);
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v___y_4381_ = v___y_4386_;
v___y_4382_ = v___y_4387_;
v_a_4383_ = v_a_4396_;
goto v___jp_4380_;
}
}
}
else
{
v___y_4381_ = v___y_4386_;
v___y_4382_ = v___y_4387_;
v_a_4383_ = v_a_4388_;
goto v___jp_4380_;
}
}
else
{
v___y_4381_ = v___y_4386_;
v___y_4382_ = v___y_4387_;
v_a_4383_ = v_a_4388_;
goto v___jp_4380_;
}
}
v___jp_4397_:
{
lean_object* v___x_4398_; lean_object* v_a_4399_; lean_object* v___x_4400_; uint8_t v___x_4401_; 
v___x_4398_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4287_);
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref(v___x_4398_);
v___x_4400_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4401_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4290_, v___x_4400_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = lean_io_mono_nanos_now();
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
lean_inc(v_a_4285_);
lean_inc_ref(v_a_4284_);
v___x_4403_ = lean_apply_5(v_k_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, lean_box(0));
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; uint8_t v___x_4407_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4406_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4407_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4293_, v_options_4290_, v___x_4406_);
if (v___x_4407_ == 0)
{
v___y_4342_ = v___x_4402_;
v___y_4343_ = v_a_4399_;
v_a_4344_ = v_a_4404_;
goto v___jp_4341_;
}
else
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
lean_inc(v_a_4404_);
v___x_4408_ = l_Lean_MessageData_ofExpr(v_a_4404_);
v___x_4409_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4405_, v___x_4408_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_dec_ref_known(v___x_4409_, 1);
v___y_4342_ = v___x_4402_;
v___y_4343_ = v_a_4399_;
v_a_4344_ = v_a_4404_;
goto v___jp_4341_;
}
else
{
lean_object* v_a_4410_; 
lean_dec(v_a_4404_);
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___y_4352_ = v___x_4402_;
v___y_4353_ = v_a_4399_;
v_a_4354_ = v_a_4410_;
goto v___jp_4351_;
}
}
}
else
{
lean_object* v_a_4411_; 
v_a_4411_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4403_, 1);
v___y_4352_ = v___x_4402_;
v___y_4353_ = v_a_4399_;
v_a_4354_ = v_a_4411_;
goto v___jp_4351_;
}
}
else
{
lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4412_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
lean_inc(v_a_4285_);
lean_inc_ref(v_a_4284_);
v___x_4413_ = lean_apply_5(v_k_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, lean_box(0));
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4416_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4417_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4293_, v_options_4290_, v___x_4416_);
if (v___x_4417_ == 0)
{
v___y_4376_ = v___x_4412_;
v___y_4377_ = v_a_4399_;
v_a_4378_ = v_a_4414_;
goto v___jp_4375_;
}
else
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
lean_inc(v_a_4414_);
v___x_4418_ = l_Lean_MessageData_ofExpr(v_a_4414_);
v___x_4419_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4415_, v___x_4418_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_dec_ref_known(v___x_4419_, 1);
v___y_4376_ = v___x_4412_;
v___y_4377_ = v_a_4399_;
v_a_4378_ = v_a_4414_;
goto v___jp_4375_;
}
else
{
lean_object* v_a_4420_; 
lean_dec(v_a_4414_);
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v___y_4386_ = v___x_4412_;
v___y_4387_ = v_a_4399_;
v_a_4388_ = v_a_4420_;
goto v___jp_4385_;
}
}
}
else
{
lean_object* v_a_4421_; 
v_a_4421_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4413_, 1);
v___y_4386_ = v___x_4412_;
v___y_4387_ = v_a_4399_;
v_a_4388_ = v_a_4421_;
goto v___jp_4385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4448_, lean_object* v_xs_4449_, lean_object* v_k_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4448_, v_xs_4449_, v_k_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4457_, lean_object* v_xs_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v___x_4464_; 
lean_inc(v_a_4462_);
lean_inc_ref(v_a_4461_);
lean_inc(v_a_4460_);
lean_inc_ref(v_a_4459_);
lean_inc_ref(v_f_4457_);
v___x_4464_ = lean_infer_type(v_f_4457_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v_a_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; uint8_t v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4465_);
lean_dec_ref_known(v___x_4464_, 1);
v___x_4466_ = lean_unsigned_to_nat(0u);
v___x_4467_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4458_);
lean_inc_ref(v_f_4457_);
v___x_4468_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4468_, 0, v_f_4457_);
lean_closure_set(v___x_4468_, 1, v_xs_4458_);
lean_closure_set(v___x_4468_, 2, v___x_4466_);
lean_closure_set(v___x_4468_, 3, v___x_4467_);
lean_closure_set(v___x_4468_, 4, v___x_4466_);
lean_closure_set(v___x_4468_, 5, v___x_4467_);
lean_closure_set(v___x_4468_, 6, v_a_4465_);
v___x_4469_ = 0;
v___x_4470_ = lean_box(v___x_4469_);
v___x_4471_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4471_, 0, lean_box(0));
lean_closure_set(v___x_4471_, 1, v___x_4468_);
lean_closure_set(v___x_4471_, 2, v___x_4470_);
v___x_4472_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4457_, v_xs_4458_, v___x_4471_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
return v___x_4472_;
}
else
{
lean_dec_ref(v_xs_4458_);
lean_dec_ref(v_f_4457_);
return v___x_4464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4473_, lean_object* v_xs_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Lean_Meta_mkAppOptM_x27(v_f_4473_, v_xs_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
return v_res_4480_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4489_ = l_Lean_MessageData_ofFormat(v___x_4488_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4490_, lean_object* v_h1_4491_, lean_object* v_h2_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_){
_start:
{
lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___x_4508_; uint8_t v___x_4509_; 
v___x_4508_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4509_ = l_Lean_Expr_isAppOf(v_h2_4492_, v___x_4508_);
if (v___x_4509_ == 0)
{
lean_object* v___x_4510_; 
lean_inc_ref(v_h2_4492_);
v___x_4510_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref_known(v___x_4510_, 1);
v___x_4512_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4513_ = lean_unsigned_to_nat(3u);
v___x_4514_ = l_Lean_Expr_isAppOfArity(v_a_4511_, v___x_4512_, v___x_4513_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_dec_ref(v_h1_4491_);
lean_dec_ref(v_motive_4490_);
v___x_4515_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4516_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4517_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4492_, v_a_4511_);
v___x_4518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4516_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
v___x_4519_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4515_, v___x_4518_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
return v___x_4519_;
}
else
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4520_ = l_Lean_Expr_appFn_x21(v_a_4511_);
v___x_4521_ = l_Lean_Expr_appFn_x21(v___x_4520_);
v___x_4522_ = l_Lean_Expr_appArg_x21(v___x_4521_);
lean_dec_ref(v___x_4521_);
v___x_4523_ = l_Lean_Expr_appArg_x21(v___x_4520_);
lean_dec_ref(v___x_4520_);
v___x_4524_ = l_Lean_Expr_appArg_x21(v_a_4511_);
lean_dec(v_a_4511_);
lean_inc_ref(v___x_4522_);
v___x_4525_ = l_Lean_Meta_getLevel(v___x_4522_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; lean_object* v___x_4527_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4525_, 1);
lean_inc_ref(v_motive_4490_);
v___x_4527_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4490_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4551_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4551_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4551_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
if (lean_obj_tag(v_a_4528_) == 7)
{
lean_object* v_body_4532_; 
v_body_4532_ = lean_ctor_get(v_a_4528_, 2);
lean_inc_ref(v_body_4532_);
lean_dec_ref_known(v_a_4528_, 3);
if (lean_obj_tag(v_body_4532_) == 3)
{
lean_object* v_u_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4549_; 
v_u_4533_ = lean_ctor_get(v_body_4532_, 0);
lean_inc(v_u_4533_);
lean_dec_ref_known(v_body_4532_, 1);
v___x_4534_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4535_ = lean_box(0);
v___x_4536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4536_, 0, v_a_4526_);
lean_ctor_set(v___x_4536_, 1, v___x_4535_);
v___x_4537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4537_, 0, v_u_4533_);
lean_ctor_set(v___x_4537_, 1, v___x_4536_);
v___x_4538_ = l_Lean_mkConst(v___x_4534_, v___x_4537_);
v___x_4539_ = lean_unsigned_to_nat(6u);
v___x_4540_ = lean_mk_empty_array_with_capacity(v___x_4539_);
v___x_4541_ = lean_array_push(v___x_4540_, v___x_4522_);
v___x_4542_ = lean_array_push(v___x_4541_, v___x_4523_);
v___x_4543_ = lean_array_push(v___x_4542_, v_motive_4490_);
v___x_4544_ = lean_array_push(v___x_4543_, v_h1_4491_);
v___x_4545_ = lean_array_push(v___x_4544_, v___x_4524_);
v___x_4546_ = lean_array_push(v___x_4545_, v_h2_4492_);
v___x_4547_ = l_Lean_mkAppN(v___x_4538_, v___x_4546_);
lean_dec_ref(v___x_4546_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4547_);
v___x_4549_ = v___x_4530_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
else
{
lean_dec_ref(v_body_4532_);
lean_del_object(v___x_4530_);
lean_dec(v_a_4526_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v_h2_4492_);
lean_dec_ref(v_h1_4491_);
v___y_4499_ = v_a_4493_;
v___y_4500_ = v_a_4494_;
v___y_4501_ = v_a_4495_;
v___y_4502_ = v_a_4496_;
goto v___jp_4498_;
}
}
else
{
lean_del_object(v___x_4530_);
lean_dec(v_a_4528_);
lean_dec(v_a_4526_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v_h2_4492_);
lean_dec_ref(v_h1_4491_);
v___y_4499_ = v_a_4493_;
v___y_4500_ = v_a_4494_;
v___y_4501_ = v_a_4495_;
v___y_4502_ = v_a_4496_;
goto v___jp_4498_;
}
}
}
else
{
lean_dec(v_a_4526_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v_h2_4492_);
lean_dec_ref(v_h1_4491_);
lean_dec_ref(v_motive_4490_);
return v___x_4527_;
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v_h2_4492_);
lean_dec_ref(v_h1_4491_);
lean_dec_ref(v_motive_4490_);
v_a_4552_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4525_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4525_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4492_);
lean_dec_ref(v_h1_4491_);
lean_dec_ref(v_motive_4490_);
return v___x_4510_;
}
}
else
{
lean_object* v___x_4560_; 
lean_dec_ref(v_h2_4492_);
lean_dec_ref(v_motive_4490_);
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v_h1_4491_);
return v___x_4560_;
}
v___jp_4498_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4503_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4504_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4505_ = l_Lean_indentExpr(v_motive_4490_);
v___x_4506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4504_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
v___x_4507_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4503_, v___x_4506_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
return v___x_4507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4561_, lean_object* v_h1_4562_, lean_object* v_h2_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_Meta_mkEqNDRec(v_motive_4561_, v_h1_4562_, v_h2_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4574_, lean_object* v_h1_4575_, lean_object* v_h2_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4592_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4593_ = l_Lean_Expr_isAppOf(v_h2_4576_, v___x_4592_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
lean_inc_ref(v_h2_4576_);
v___x_4594_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; uint8_t v___x_4598_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref_known(v___x_4594_, 1);
v___x_4596_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4597_ = lean_unsigned_to_nat(3u);
v___x_4598_ = l_Lean_Expr_isAppOfArity(v_a_4595_, v___x_4596_, v___x_4597_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
lean_dec(v_a_4595_);
lean_dec_ref(v_h1_4575_);
lean_dec_ref(v_motive_4574_);
v___x_4599_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4600_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4601_ = l_Lean_indentExpr(v_h2_4576_);
v___x_4602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4600_);
lean_ctor_set(v___x_4602_, 1, v___x_4601_);
v___x_4603_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4599_, v___x_4602_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
return v___x_4603_;
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4604_ = l_Lean_Expr_appFn_x21(v_a_4595_);
v___x_4605_ = l_Lean_Expr_appFn_x21(v___x_4604_);
v___x_4606_ = l_Lean_Expr_appArg_x21(v___x_4605_);
lean_dec_ref(v___x_4605_);
v___x_4607_ = l_Lean_Expr_appArg_x21(v___x_4604_);
lean_dec_ref(v___x_4604_);
v___x_4608_ = l_Lean_Expr_appArg_x21(v_a_4595_);
lean_dec(v_a_4595_);
lean_inc_ref(v___x_4606_);
v___x_4609_ = l_Lean_Meta_getLevel(v___x_4606_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4611_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref_known(v___x_4609_, 1);
lean_inc_ref(v_motive_4574_);
v___x_4611_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4574_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4636_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4636_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4636_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
if (lean_obj_tag(v_a_4612_) == 7)
{
lean_object* v_body_4616_; 
v_body_4616_ = lean_ctor_get(v_a_4612_, 2);
lean_inc_ref(v_body_4616_);
lean_dec_ref_known(v_a_4612_, 3);
if (lean_obj_tag(v_body_4616_) == 7)
{
lean_object* v_body_4617_; 
v_body_4617_ = lean_ctor_get(v_body_4616_, 2);
lean_inc_ref(v_body_4617_);
lean_dec_ref_known(v_body_4616_, 3);
if (lean_obj_tag(v_body_4617_) == 3)
{
lean_object* v_u_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
v_u_4618_ = lean_ctor_get(v_body_4617_, 0);
lean_inc(v_u_4618_);
lean_dec_ref_known(v_body_4617_, 1);
v___x_4619_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4620_ = lean_box(0);
v___x_4621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4621_, 0, v_a_4610_);
lean_ctor_set(v___x_4621_, 1, v___x_4620_);
v___x_4622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4622_, 0, v_u_4618_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
v___x_4623_ = l_Lean_mkConst(v___x_4619_, v___x_4622_);
v___x_4624_ = lean_unsigned_to_nat(6u);
v___x_4625_ = lean_mk_empty_array_with_capacity(v___x_4624_);
v___x_4626_ = lean_array_push(v___x_4625_, v___x_4606_);
v___x_4627_ = lean_array_push(v___x_4626_, v___x_4607_);
v___x_4628_ = lean_array_push(v___x_4627_, v_motive_4574_);
v___x_4629_ = lean_array_push(v___x_4628_, v_h1_4575_);
v___x_4630_ = lean_array_push(v___x_4629_, v___x_4608_);
v___x_4631_ = lean_array_push(v___x_4630_, v_h2_4576_);
v___x_4632_ = l_Lean_mkAppN(v___x_4623_, v___x_4631_);
lean_dec_ref(v___x_4631_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4632_);
v___x_4634_ = v___x_4614_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4632_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
else
{
lean_dec_ref(v_body_4617_);
lean_del_object(v___x_4614_);
lean_dec(v_a_4610_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v_h2_4576_);
lean_dec_ref(v_h1_4575_);
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
v___y_4585_ = v_a_4579_;
v___y_4586_ = v_a_4580_;
goto v___jp_4582_;
}
}
else
{
lean_dec_ref(v_body_4616_);
lean_del_object(v___x_4614_);
lean_dec(v_a_4610_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v_h2_4576_);
lean_dec_ref(v_h1_4575_);
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
v___y_4585_ = v_a_4579_;
v___y_4586_ = v_a_4580_;
goto v___jp_4582_;
}
}
else
{
lean_del_object(v___x_4614_);
lean_dec(v_a_4612_);
lean_dec(v_a_4610_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v_h2_4576_);
lean_dec_ref(v_h1_4575_);
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
v___y_4585_ = v_a_4579_;
v___y_4586_ = v_a_4580_;
goto v___jp_4582_;
}
}
}
else
{
lean_dec(v_a_4610_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v_h2_4576_);
lean_dec_ref(v_h1_4575_);
lean_dec_ref(v_motive_4574_);
return v___x_4611_;
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v_h2_4576_);
lean_dec_ref(v_h1_4575_);
lean_dec_ref(v_motive_4574_);
v_a_4637_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4609_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4609_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4576_);
lean_dec_ref(v_h1_4575_);
lean_dec_ref(v_motive_4574_);
return v___x_4594_;
}
}
else
{
lean_object* v___x_4645_; 
lean_dec_ref(v_h2_4576_);
lean_dec_ref(v_motive_4574_);
v___x_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4645_, 0, v_h1_4575_);
return v___x_4645_;
}
v___jp_4582_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4587_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4588_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4589_ = l_Lean_indentExpr(v_motive_4574_);
v___x_4590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4588_);
lean_ctor_set(v___x_4590_, 1, v___x_4589_);
v___x_4591_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4587_, v___x_4590_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
return v___x_4591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4646_, lean_object* v_h1_4647_, lean_object* v_h2_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Lean_Meta_mkEqRec(v_motive_4646_, v_h1_4647_, v_h2_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore(lean_object* v_00_u03b1_4659_, lean_object* v_00_u03b2_4660_, lean_object* v_h_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v___x_4668_; 
lean_inc_ref(v_00_u03b1_4659_);
v___x_4668_ = l_Lean_Meta_getLevel(v_00_u03b1_4659_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4681_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4671_ = v___x_4668_;
v_isShared_4672_ = v_isSharedCheck_4681_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4668_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4681_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
v___x_4673_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4674_ = lean_box(0);
v___x_4675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4675_, 0, v_a_4669_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
v___x_4676_ = l_Lean_mkConst(v___x_4673_, v___x_4675_);
v___x_4677_ = l_Lean_mkApp4(v___x_4676_, v_00_u03b1_4659_, v_00_u03b2_4660_, v_h_4661_, v_a_4662_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 0, v___x_4677_);
v___x_4679_ = v___x_4671_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_dec_ref(v_a_4662_);
lean_dec_ref(v_h_4661_);
lean_dec_ref(v_00_u03b2_4660_);
lean_dec_ref(v_00_u03b1_4659_);
v_a_4682_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4668_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4668_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore___boxed(lean_object* v_00_u03b1_4690_, lean_object* v_00_u03b2_4691_, lean_object* v_h_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l_Lean_Meta_mkEqMPCore(v_00_u03b1_4690_, v_00_u03b2_4691_, v_h_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4700_, lean_object* v_pr_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v___x_4707_; 
lean_inc_ref(v_eqProof_4700_);
v___x_4707_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_eqProof_4700_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; uint8_t v___x_4711_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref_known(v___x_4707_, 1);
v___x_4709_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4710_ = lean_unsigned_to_nat(3u);
v___x_4711_ = l_Lean_Expr_isAppOfArity(v_a_4708_, v___x_4709_, v___x_4710_);
if (v___x_4711_ == 0)
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
lean_dec_ref(v_pr_4701_);
v___x_4712_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4713_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4714_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_eqProof_4700_, v_a_4708_);
v___x_4715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4713_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4712_, v___x_4715_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
return v___x_4716_;
}
else
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4717_ = l_Lean_Expr_appFn_x21(v_a_4708_);
v___x_4718_ = l_Lean_Expr_appArg_x21(v___x_4717_);
lean_dec_ref(v___x_4717_);
v___x_4719_ = l_Lean_Expr_appArg_x21(v_a_4708_);
lean_dec(v_a_4708_);
v___x_4720_ = l_Lean_Meta_mkEqMPCore(v___x_4718_, v___x_4719_, v_eqProof_4700_, v_pr_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
return v___x_4720_;
}
}
else
{
lean_dec_ref(v_pr_4701_);
lean_dec_ref(v_eqProof_4700_);
return v___x_4707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4721_, lean_object* v_pr_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Lean_Meta_mkEqMP(v_eqProof_4721_, v_pr_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4733_, lean_object* v_pr_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4740_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4741_ = lean_unsigned_to_nat(2u);
v___x_4742_ = lean_mk_empty_array_with_capacity(v___x_4741_);
v___x_4743_ = lean_array_push(v___x_4742_, v_eqProof_4733_);
v___x_4744_ = lean_array_push(v___x_4743_, v_pr_4734_);
v___x_4745_ = l_Lean_Meta_mkAppM(v___x_4740_, v___x_4744_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4746_, lean_object* v_pr_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l_Lean_Meta_mkEqMPR(v_eqProof_4746_, v_pr_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
lean_dec(v_a_4749_);
lean_dec_ref(v_a_4748_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_){
_start:
{
lean_object* v___f_4760_; lean_object* v___x_12329__overap_4761_; lean_object* v___x_4762_; 
v___f_4760_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12329__overap_4761_ = lean_panic_fn_borrowed(v___f_4760_, v_msg_4754_);
lean_inc(v___y_4758_);
lean_inc_ref(v___y_4757_);
lean_inc(v___y_4756_);
lean_inc_ref(v___y_4755_);
v___x_4762_ = lean_apply_5(v___x_12329__overap_4761_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, lean_box(0));
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4770_, uint8_t v_skipRealize_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v___x_4774_; lean_object* v_env_4775_; uint8_t v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4774_ = lean_st_ref_get(v___y_4772_);
v_env_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc_ref(v_env_4775_);
lean_dec(v___x_4774_);
v___x_4776_ = l_Lean_Environment_contains(v_env_4775_, v_constName_4770_, v_skipRealize_4771_);
v___x_4777_ = lean_box(v___x_4776_);
v___x_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4777_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4779_, lean_object* v_skipRealize_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
uint8_t v_skipRealize_boxed_4783_; lean_object* v_res_4784_; 
v_skipRealize_boxed_4783_ = lean_unbox(v_skipRealize_4780_);
v_res_4784_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4779_, v_skipRealize_boxed_4783_, v___y_4781_);
lean_dec(v___y_4781_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4785_, uint8_t v_skipRealize_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_){
_start:
{
lean_object* v___x_4792_; 
v___x_4792_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4785_, v_skipRealize_4786_, v___y_4790_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4793_, lean_object* v_skipRealize_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
uint8_t v_skipRealize_boxed_4800_; lean_object* v_res_4801_; 
v_skipRealize_boxed_4800_ = lean_unbox(v_skipRealize_4794_);
v_res_4801_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4793_, v_skipRealize_boxed_4800_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___y_4796_);
lean_dec_ref(v___y_4795_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___x_4802_, uint8_t v___x_4803_, lean_object* v_P_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; uint8_t v___x_4813_; lean_object* v___x_4814_; 
v___x_4810_ = lean_unsigned_to_nat(1u);
v___x_4811_ = lean_mk_empty_array_with_capacity(v___x_4810_);
lean_inc_ref(v_P_4804_);
v___x_4812_ = lean_array_push(v___x_4811_, v_P_4804_);
v___x_4813_ = 1;
v___x_4814_ = l_Lean_Meta_mkLambdaFVars(v___x_4812_, v_P_4804_, v___x_4802_, v___x_4803_, v___x_4802_, v___x_4803_, v___x_4813_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
lean_dec_ref(v___x_4812_);
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___x_4815_, lean_object* v___x_4816_, lean_object* v_P_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
uint8_t v___x_13769__boxed_4823_; uint8_t v___x_13770__boxed_4824_; lean_object* v_res_4825_; 
v___x_13769__boxed_4823_ = lean_unbox(v___x_4815_);
v___x_13770__boxed_4824_ = lean_unbox(v___x_4816_);
v_res_4825_ = l_Lean_Meta_mkNoConfusion___lam__0(v___x_13769__boxed_4823_, v___x_13770__boxed_4824_, v_P_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
lean_dec(v___y_4819_);
lean_dec_ref(v___y_4818_);
return v_res_4825_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4828_ = l_Lean_stringToMessageData(v___x_4827_);
return v___x_4828_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4830_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4831_ = l_Lean_stringToMessageData(v___x_4830_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4832_, lean_object* v_b_4833_, lean_object* v_i_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v_stop_4840_; lean_object* v_step_4841_; lean_object* v_a_4843_; uint8_t v___x_4846_; 
v_stop_4840_ = lean_ctor_get(v_range_4832_, 1);
v_step_4841_ = lean_ctor_get(v_range_4832_, 2);
v___x_4846_ = lean_nat_dec_lt(v_i_4834_, v_stop_4840_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4847_; 
lean_dec(v_i_4834_);
v___x_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4847_, 0, v_b_4833_);
return v___x_4847_;
}
else
{
lean_object* v___x_4848_; 
lean_inc(v___y_4838_);
lean_inc_ref(v___y_4837_);
lean_inc(v___y_4836_);
lean_inc_ref(v___y_4835_);
lean_inc_ref(v_b_4833_);
v___x_4848_ = lean_infer_type(v_b_4833_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4850_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref_known(v___x_4848_, 1);
v___x_4850_ = l_Lean_Meta_whnfForall(v_a_4849_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref_known(v___x_4850_, 1);
v___x_4852_ = l_Lean_Expr_bindingDomain_x21(v_a_4851_);
lean_dec(v_a_4851_);
lean_inc(v___y_4838_);
lean_inc_ref(v___y_4837_);
lean_inc(v___y_4836_);
lean_inc_ref(v___y_4835_);
v___x_4853_ = lean_whnf(v___x_4852_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v_a_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; uint8_t v___x_4857_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_a_4854_);
lean_dec_ref_known(v___x_4853_, 1);
v___x_4855_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4856_ = lean_unsigned_to_nat(4u);
v___x_4857_ = l_Lean_Expr_isAppOfArity(v_a_4854_, v___x_4855_, v___x_4856_);
if (v___x_4857_ == 0)
{
lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4858_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4859_ = lean_unsigned_to_nat(3u);
v___x_4860_ = l_Lean_Expr_isAppOfArity(v_a_4854_, v___x_4858_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; 
lean_dec(v_i_4834_);
lean_inc(v___y_4838_);
lean_inc_ref(v___y_4837_);
lean_inc(v___y_4836_);
lean_inc_ref(v___y_4835_);
v___x_4861_ = lean_infer_type(v_b_4833_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref_known(v___x_4861_, 1);
v___x_4863_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4864_ = l_Lean_MessageData_ofExpr(v_a_4854_);
v___x_4865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4863_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
v___x_4866_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4865_);
lean_ctor_set(v___x_4867_, 1, v___x_4866_);
v___x_4868_ = lean_unsigned_to_nat(30u);
v___x_4869_ = l_Lean_inlineExpr(v_a_4862_, v___x_4868_);
v___x_4870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4867_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4870_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4871_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4871_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
else
{
lean_dec(v_a_4854_);
return v___x_4861_;
}
}
else
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4880_ = l_Lean_Expr_appFn_x21(v_a_4854_);
lean_dec(v_a_4854_);
v___x_4881_ = l_Lean_Expr_appArg_x21(v___x_4880_);
lean_dec_ref(v___x_4880_);
v___x_4882_ = l_Lean_Meta_mkEqRefl(v___x_4881_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4884_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4883_);
lean_dec_ref_known(v___x_4882_, 1);
v___x_4884_ = l_Lean_Expr_app___override(v_b_4833_, v_a_4883_);
v_a_4843_ = v___x_4884_;
goto v___jp_4842_;
}
else
{
lean_dec(v_i_4834_);
lean_dec_ref(v_b_4833_);
return v___x_4882_;
}
}
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4885_ = l_Lean_Expr_appFn_x21(v_a_4854_);
lean_dec(v_a_4854_);
v___x_4886_ = l_Lean_Expr_appFn_x21(v___x_4885_);
lean_dec_ref(v___x_4885_);
v___x_4887_ = l_Lean_Expr_appArg_x21(v___x_4886_);
lean_dec_ref(v___x_4886_);
v___x_4888_ = l_Lean_Meta_mkHEqRefl(v___x_4887_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4890_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_a_4889_);
lean_dec_ref_known(v___x_4888_, 1);
v___x_4890_ = l_Lean_Expr_app___override(v_b_4833_, v_a_4889_);
v_a_4843_ = v___x_4890_;
goto v___jp_4842_;
}
else
{
lean_dec(v_i_4834_);
lean_dec_ref(v_b_4833_);
return v___x_4888_;
}
}
}
else
{
lean_dec(v_i_4834_);
lean_dec_ref(v_b_4833_);
return v___x_4853_;
}
}
else
{
lean_dec(v_i_4834_);
lean_dec_ref(v_b_4833_);
return v___x_4850_;
}
}
else
{
lean_dec(v_i_4834_);
lean_dec_ref(v_b_4833_);
return v___x_4848_;
}
}
v___jp_4842_:
{
lean_object* v___x_4844_; 
v___x_4844_ = lean_nat_add(v_i_4834_, v_step_4841_);
lean_dec(v_i_4834_);
v_b_4833_ = v_a_4843_;
v_i_4834_ = v___x_4844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4891_, lean_object* v_b_4892_, lean_object* v_i_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4891_, v_b_4892_, v_i_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec_ref(v_range_4891_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4900_, lean_object* v_b_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v___x_4907_; 
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
v___x_4907_ = lean_apply_6(v_k_4900_, v_b_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, lean_box(0));
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4908_, lean_object* v_b_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4908_, v_b_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4916_, uint8_t v_bi_4917_, lean_object* v_type_4918_, lean_object* v_k_4919_, uint8_t v_kind_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_){
_start:
{
lean_object* v___f_4926_; lean_object* v___x_4927_; 
v___f_4926_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4926_, 0, v_k_4919_);
v___x_4927_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4916_, v_bi_4917_, v_type_4918_, v___f_4926_, v_kind_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4927_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
v_a_4936_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4927_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4927_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_4944_, lean_object* v_bi_4945_, lean_object* v_type_4946_, lean_object* v_k_4947_, lean_object* v_kind_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
uint8_t v_bi_boxed_4954_; uint8_t v_kind_boxed_4955_; lean_object* v_res_4956_; 
v_bi_boxed_4954_ = lean_unbox(v_bi_4945_);
v_kind_boxed_4955_ = lean_unbox(v_kind_4948_);
v_res_4956_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4944_, v_bi_boxed_4954_, v_type_4946_, v_k_4947_, v_kind_boxed_4955_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_4957_, lean_object* v_type_4958_, lean_object* v_k_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
uint8_t v___x_4965_; uint8_t v___x_4966_; lean_object* v___x_4967_; 
v___x_4965_ = 0;
v___x_4966_ = 0;
v___x_4967_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4957_, v___x_4965_, v_type_4958_, v_k_4959_, v___x_4966_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_4968_, lean_object* v_type_4969_, lean_object* v_k_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_4968_, v_type_4969_, v_k_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
return v_res_4976_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4983_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_4984_ = l_Lean_MessageData_ofFormat(v___x_4983_);
return v___x_4984_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6(void){
_start:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4986_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__5));
v___x_4987_ = l_Lean_stringToMessageData(v___x_4986_);
return v___x_4987_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8(void){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__7));
v___x_4990_ = l_Lean_stringToMessageData(v___x_4989_);
return v___x_4990_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4994_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_4995_ = l_Lean_MessageData_ofFormat(v___x_4994_);
return v___x_4995_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5001_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5002_ = l_Lean_stringToMessageData(v___x_5001_);
return v___x_5002_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__18(void){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__17));
v___x_5005_ = l_Lean_stringToMessageData(v___x_5004_);
return v___x_5005_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__19(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5006_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__14));
v___x_5007_ = l_Lean_MessageData_ofName(v___x_5006_);
return v___x_5007_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__22(void){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5010_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5011_ = lean_unsigned_to_nat(10u);
v___x_5012_ = lean_unsigned_to_nat(511u);
v___x_5013_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__20));
v___x_5014_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5015_ = l_mkPanicMessageWithDecl(v___x_5014_, v___x_5013_, v___x_5012_, v___x_5011_, v___x_5010_);
return v___x_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5019_, lean_object* v_h_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_){
_start:
{
lean_object* v___x_5026_; 
lean_inc(v_a_5024_);
lean_inc_ref(v_a_5023_);
lean_inc(v_a_5022_);
lean_inc_ref(v_a_5021_);
lean_inc_ref(v_h_5020_);
v___x_5026_ = lean_infer_type(v_h_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v___x_5028_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_a_5027_);
lean_dec_ref_known(v___x_5026_, 1);
lean_inc(v_a_5024_);
lean_inc_ref(v_a_5023_);
lean_inc(v_a_5022_);
lean_inc_ref(v_a_5021_);
v___x_5028_ = lean_whnf(v_a_5027_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; uint8_t v___x_5032_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref_known(v___x_5028_, 1);
v___x_5030_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5031_ = lean_unsigned_to_nat(3u);
v___x_5032_ = l_Lean_Expr_isAppOfArity(v_a_5029_, v___x_5030_, v___x_5031_);
if (v___x_5032_ == 0)
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
lean_dec_ref(v_target_5019_);
v___x_5033_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5034_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5035_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5020_, v_a_5029_);
v___x_5036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5034_);
lean_ctor_set(v___x_5036_, 1, v___x_5035_);
v___x_5037_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5033_, v___x_5036_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
return v___x_5037_;
}
else
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___x_5056_; 
v___x_5038_ = l_Lean_Expr_appFn_x21(v_a_5029_);
v___x_5039_ = l_Lean_Expr_appFn_x21(v___x_5038_);
v___x_5040_ = l_Lean_Expr_appArg_x21(v___x_5039_);
lean_dec_ref(v___x_5039_);
v___x_5041_ = l_Lean_Expr_appArg_x21(v___x_5038_);
lean_dec_ref(v___x_5038_);
v___x_5042_ = l_Lean_Expr_appArg_x21(v_a_5029_);
lean_dec(v_a_5029_);
v___x_5056_ = l_Lean_Meta_whnfD(v___x_5040_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v_a_5057_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v___y_5062_; lean_object* v___x_5068_; 
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v___x_5056_, 1);
v___x_5068_ = l_Lean_Expr_getAppFn(v_a_5057_);
if (lean_obj_tag(v___x_5068_) == 4)
{
lean_object* v_declName_5069_; lean_object* v_us_5070_; lean_object* v___x_5071_; lean_object* v_env_5072_; uint8_t v___x_5073_; lean_object* v___x_5074_; 
v_declName_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_declName_5069_);
v_us_5070_ = lean_ctor_get(v___x_5068_, 1);
lean_inc(v_us_5070_);
lean_dec_ref_known(v___x_5068_, 2);
v___x_5071_ = lean_st_ref_get(v_a_5024_);
v_env_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc_ref(v_env_5072_);
lean_dec(v___x_5071_);
v___x_5073_ = 0;
v___x_5074_ = l_Lean_Environment_find_x3f(v_env_5072_, v_declName_5069_, v___x_5073_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_dec(v_us_5070_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v___y_5059_ = v_a_5021_;
v___y_5060_ = v_a_5022_;
v___y_5061_ = v_a_5023_;
v___y_5062_ = v_a_5024_;
goto v___jp_5058_;
}
else
{
lean_object* v_val_5075_; 
v_val_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_val_5075_);
lean_dec_ref_known(v___x_5074_, 1);
if (lean_obj_tag(v_val_5075_) == 5)
{
lean_object* v_val_5076_; lean_object* v___x_5077_; 
v_val_5076_ = lean_ctor_get(v_val_5075_, 0);
lean_inc_ref(v_val_5076_);
lean_dec_ref_known(v_val_5075_, 1);
lean_inc_ref(v_target_5019_);
v___x_5077_ = l_Lean_Meta_getLevel(v_target_5019_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5079_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref_known(v___x_5077_, 1);
lean_inc_ref(v___x_5041_);
v___x_5079_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5041_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref_known(v___x_5079_, 1);
if (lean_obj_tag(v_a_5080_) == 1)
{
lean_object* v_val_5081_; lean_object* v_fst_5082_; lean_object* v_snd_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5297_; 
v_val_5081_ = lean_ctor_get(v_a_5080_, 0);
lean_inc(v_val_5081_);
lean_dec_ref_known(v_a_5080_, 1);
v_fst_5082_ = lean_ctor_get(v_val_5081_, 0);
v_snd_5083_ = lean_ctor_get(v_val_5081_, 1);
v_isSharedCheck_5297_ = !lean_is_exclusive(v_val_5081_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5085_ = v_val_5081_;
v_isShared_5086_ = v_isSharedCheck_5297_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_snd_5083_);
lean_inc(v_fst_5082_);
lean_dec(v_val_5081_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5297_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5087_; 
lean_inc_ref(v___x_5042_);
v___x_5087_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5042_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5088_);
lean_dec_ref_known(v___x_5087_, 1);
if (lean_obj_tag(v_a_5088_) == 1)
{
lean_object* v_val_5089_; lean_object* v_fst_5090_; lean_object* v_snd_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5288_; 
v_val_5089_ = lean_ctor_get(v_a_5088_, 0);
lean_inc(v_val_5089_);
lean_dec_ref_known(v_a_5088_, 1);
v_fst_5090_ = lean_ctor_get(v_val_5089_, 0);
v_snd_5091_ = lean_ctor_get(v_val_5089_, 1);
v_isSharedCheck_5288_ = !lean_is_exclusive(v_val_5089_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5093_ = v_val_5089_;
v_isShared_5094_ = v_isSharedCheck_5288_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_snd_5091_);
lean_inc(v_fst_5090_);
lean_dec(v_val_5089_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5288_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v_toConstantVal_5095_; lean_object* v_cidx_5096_; lean_object* v_numParams_5097_; lean_object* v_numFields_5098_; lean_object* v_cidx_5099_; uint8_t v___x_5100_; 
v_toConstantVal_5095_ = lean_ctor_get(v_fst_5082_, 0);
lean_inc_ref(v_toConstantVal_5095_);
v_cidx_5096_ = lean_ctor_get(v_fst_5082_, 2);
lean_inc(v_cidx_5096_);
v_numParams_5097_ = lean_ctor_get(v_fst_5082_, 3);
lean_inc(v_numParams_5097_);
v_numFields_5098_ = lean_ctor_get(v_fst_5082_, 4);
lean_inc(v_numFields_5098_);
lean_dec(v_fst_5082_);
v_cidx_5099_ = lean_ctor_get(v_fst_5090_, 2);
lean_inc(v_cidx_5099_);
lean_dec(v_fst_5090_);
v___x_5100_ = lean_nat_dec_eq(v_cidx_5096_, v_cidx_5099_);
lean_dec(v_cidx_5099_);
lean_dec(v_cidx_5096_);
if (v___x_5100_ == 0)
{
lean_object* v_toConstantVal_5101_; lean_object* v_name_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v_a_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v_a_5109_; uint8_t v___x_5131_; 
lean_dec(v_numFields_5098_);
lean_dec(v_numParams_5097_);
lean_dec_ref(v_toConstantVal_5095_);
lean_dec(v_snd_5091_);
lean_dec(v_snd_5083_);
v_toConstantVal_5101_ = lean_ctor_get(v_val_5076_, 0);
lean_inc_ref(v_toConstantVal_5101_);
lean_dec_ref(v_val_5076_);
v_name_5102_ = lean_ctor_get(v_toConstantVal_5101_, 0);
lean_inc(v_name_5102_);
lean_dec_ref(v_toConstantVal_5101_);
v___x_5103_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5104_ = l_Lean_Name_str___override(v_name_5102_, v___x_5103_);
lean_inc(v___x_5104_);
v___x_5105_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5104_, v___x_5032_, v_a_5024_);
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5106_);
lean_dec_ref(v___x_5105_);
v___x_5107_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__14));
v___x_5108_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5107_, v___x_5032_, v_a_5024_);
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref(v___x_5108_);
v___x_5131_ = lean_unbox(v_a_5106_);
lean_dec(v_a_5106_);
if (v___x_5131_ == 0)
{
lean_dec(v_a_5109_);
lean_dec(v_a_5078_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
goto v___jp_5110_;
}
else
{
uint8_t v___x_5132_; 
v___x_5132_ = lean_unbox(v_a_5109_);
lean_dec(v_a_5109_);
if (v___x_5132_ == 0)
{
lean_dec(v_a_5078_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
goto v___jp_5110_;
}
else
{
lean_object* v___x_5133_; lean_object* v_dummy_5134_; lean_object* v_nargs_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
lean_del_object(v___x_5093_);
lean_del_object(v___x_5085_);
v___x_5133_ = l_Lean_mkConst(v___x_5104_, v_us_5070_);
v_dummy_5134_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5135_ = l_Lean_Expr_getAppNumArgs(v_a_5057_);
lean_inc(v_nargs_5135_);
v___x_5136_ = lean_mk_array(v_nargs_5135_, v_dummy_5134_);
v___x_5137_ = lean_unsigned_to_nat(1u);
v___x_5138_ = lean_nat_sub(v_nargs_5135_, v___x_5137_);
lean_dec(v_nargs_5135_);
lean_inc_n(v_a_5057_, 2);
v___x_5139_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5057_, v___x_5136_, v___x_5138_);
v___x_5140_ = l_Lean_mkAppN(v___x_5133_, v___x_5139_);
lean_dec_ref(v___x_5139_);
v___x_5141_ = l_Lean_Meta_getLevel(v_a_5057_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5164_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5144_ = v___x_5141_;
v_isShared_5145_ = v_isSharedCheck_5164_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5141_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5164_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5162_; 
v___x_5146_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5147_ = lean_box(0);
v___x_5148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5148_, 0, v_a_5078_);
lean_ctor_set(v___x_5148_, 1, v___x_5147_);
v___x_5149_ = l_Lean_mkConst(v___x_5146_, v___x_5148_);
v___x_5150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5150_, 0, v_a_5142_);
lean_ctor_set(v___x_5150_, 1, v___x_5147_);
v___x_5151_ = l_Lean_mkConst(v___x_5107_, v___x_5150_);
v___x_5152_ = lean_unsigned_to_nat(5u);
v___x_5153_ = lean_mk_empty_array_with_capacity(v___x_5152_);
v___x_5154_ = lean_array_push(v___x_5153_, v_a_5057_);
v___x_5155_ = lean_array_push(v___x_5154_, v___x_5140_);
v___x_5156_ = lean_array_push(v___x_5155_, v___x_5041_);
v___x_5157_ = lean_array_push(v___x_5156_, v___x_5042_);
v___x_5158_ = lean_array_push(v___x_5157_, v_h_5020_);
v___x_5159_ = l_Lean_mkAppN(v___x_5151_, v___x_5158_);
lean_dec_ref(v___x_5158_);
v___x_5160_ = l_Lean_mkAppB(v___x_5149_, v_target_5019_, v___x_5159_);
if (v_isShared_5145_ == 0)
{
lean_ctor_set(v___x_5144_, 0, v___x_5160_);
v___x_5162_ = v___x_5144_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v___x_5160_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec_ref(v___x_5140_);
lean_dec(v_a_5078_);
lean_dec(v_a_5057_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v_a_5165_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5141_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5141_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
}
}
v___jp_5110_:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5114_; 
v___x_5111_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5112_ = l_Lean_MessageData_ofName(v___x_5104_);
if (v_isShared_5094_ == 0)
{
lean_ctor_set_tag(v___x_5093_, 7);
lean_ctor_set(v___x_5093_, 1, v___x_5112_);
lean_ctor_set(v___x_5093_, 0, v___x_5111_);
v___x_5114_ = v___x_5093_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5111_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v___x_5112_);
v___x_5114_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
lean_object* v___x_5115_; lean_object* v___x_5117_; 
v___x_5115_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__18, &l_Lean_Meta_mkNoConfusion___closed__18_once, _init_l_Lean_Meta_mkNoConfusion___closed__18);
if (v_isShared_5086_ == 0)
{
lean_ctor_set_tag(v___x_5085_, 7);
lean_ctor_set(v___x_5085_, 1, v___x_5115_);
lean_ctor_set(v___x_5085_, 0, v___x_5114_);
v___x_5117_ = v___x_5085_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5114_);
lean_ctor_set(v_reuseFailAlloc_5129_, 1, v___x_5115_);
v___x_5117_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
v___x_5118_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__19, &l_Lean_Meta_mkNoConfusion___closed__19_once, _init_l_Lean_Meta_mkNoConfusion___closed__19);
v___x_5119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5119_, 0, v___x_5117_);
lean_ctor_set(v___x_5119_, 1, v___x_5118_);
v___x_5120_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5119_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5120_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5120_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
}
}
else
{
lean_object* v___x_5173_; uint8_t v___x_5174_; 
lean_dec_ref(v_val_5076_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
v___x_5173_ = lean_unsigned_to_nat(0u);
v___x_5174_ = lean_nat_dec_eq(v_numFields_5098_, v___x_5173_);
lean_dec(v_numFields_5098_);
if (v___x_5174_ == 0)
{
lean_object* v_name_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___y_5179_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___x_5266_; lean_object* v_a_5267_; uint8_t v___x_5268_; 
v_name_5175_ = lean_ctor_get(v_toConstantVal_5095_, 0);
lean_inc(v_name_5175_);
lean_dec_ref(v_toConstantVal_5095_);
v___x_5176_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5177_ = l_Lean_Name_str___override(v_name_5175_, v___x_5176_);
lean_inc(v___x_5177_);
v___x_5266_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5177_, v___x_5032_, v_a_5024_);
v_a_5267_ = lean_ctor_get(v___x_5266_, 0);
lean_inc(v_a_5267_);
lean_dec_ref(v___x_5266_);
v___x_5268_ = lean_unbox(v_a_5267_);
lean_dec(v_a_5267_);
if (v___x_5268_ == 0)
{
lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5272_; 
lean_dec(v_numParams_5097_);
lean_del_object(v___x_5093_);
lean_dec(v_snd_5091_);
lean_dec(v_snd_5083_);
lean_dec(v_a_5078_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v___x_5269_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5270_ = l_Lean_MessageData_ofName(v___x_5177_);
if (v_isShared_5086_ == 0)
{
lean_ctor_set_tag(v___x_5085_, 7);
lean_ctor_set(v___x_5085_, 1, v___x_5270_);
lean_ctor_set(v___x_5085_, 0, v___x_5269_);
v___x_5272_ = v___x_5085_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5269_);
lean_ctor_set(v_reuseFailAlloc_5282_, 1, v___x_5270_);
v___x_5272_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5273_; lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
v___x_5273_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5272_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5273_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5273_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
else
{
lean_del_object(v___x_5085_);
v___y_5179_ = v_a_5021_;
v___y_5180_ = v_a_5022_;
v___y_5181_ = v_a_5023_;
v___y_5182_ = v_a_5024_;
goto v___jp_5178_;
}
v___jp_5178_:
{
lean_object* v___x_5183_; 
lean_inc(v___x_5177_);
v___x_5183_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___x_5177_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v_a_5184_; lean_object* v_dummy_5185_; lean_object* v_nargs_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v_type_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5255_; 
v_a_5184_ = lean_ctor_get(v___x_5183_, 0);
lean_inc(v_a_5184_);
lean_dec_ref_known(v___x_5183_, 1);
v_dummy_5185_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5186_ = l_Lean_Expr_getAppNumArgs(v_a_5057_);
lean_inc(v_nargs_5186_);
v___x_5187_ = lean_mk_array(v_nargs_5186_, v_dummy_5185_);
v___x_5188_ = lean_unsigned_to_nat(1u);
v___x_5189_ = lean_nat_sub(v_nargs_5186_, v___x_5188_);
lean_dec(v_nargs_5186_);
v___x_5190_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5057_, v___x_5187_, v___x_5189_);
lean_inc(v_numParams_5097_);
v___x_5191_ = l_Array_toSubarray___redArg(v___x_5190_, v___x_5173_, v_numParams_5097_);
v___x_5192_ = lean_array_get_size(v_snd_5083_);
v_type_5193_ = lean_ctor_get(v_a_5184_, 2);
v_isSharedCheck_5255_ = !lean_is_exclusive(v_a_5184_);
if (v_isSharedCheck_5255_ == 0)
{
lean_object* v_unused_5256_; lean_object* v_unused_5257_; 
v_unused_5256_ = lean_ctor_get(v_a_5184_, 1);
lean_dec(v_unused_5256_);
v_unused_5257_ = lean_ctor_get(v_a_5184_, 0);
lean_dec(v_unused_5257_);
v___x_5195_ = v_a_5184_;
v_isShared_5196_ = v_isSharedCheck_5255_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_type_5193_);
lean_dec(v_a_5184_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5255_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v_start_5197_; lean_object* v_stop_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; uint8_t v___x_5211_; 
v_start_5197_ = lean_ctor_get(v___x_5191_, 1);
v_stop_5198_ = lean_ctor_get(v___x_5191_, 2);
lean_inc(v_numParams_5097_);
v___x_5199_ = l_Array_toSubarray___redArg(v_snd_5083_, v_numParams_5097_, v___x_5192_);
v___x_5200_ = lean_array_get_size(v_snd_5091_);
v___x_5201_ = l_Subarray_copy___redArg(v___x_5199_);
v___x_5202_ = l_Array_toSubarray___redArg(v_snd_5091_, v_numParams_5097_, v___x_5200_);
v___x_5203_ = l_Subarray_copy___redArg(v___x_5202_);
v___x_5204_ = l_Lean_Expr_getNumHeadForalls(v_type_5193_);
lean_dec_ref(v_type_5193_);
v___x_5205_ = lean_nat_sub(v_stop_5198_, v_start_5197_);
v___x_5206_ = lean_array_get_size(v___x_5201_);
v___x_5207_ = lean_nat_add(v___x_5205_, v___x_5206_);
lean_dec(v___x_5205_);
v___x_5208_ = lean_array_get_size(v___x_5203_);
v___x_5209_ = lean_nat_add(v___x_5207_, v___x_5208_);
lean_dec(v___x_5207_);
v___x_5210_ = lean_nat_add(v___x_5209_, v___x_5031_);
lean_dec(v___x_5209_);
v___x_5211_ = lean_nat_dec_le(v___x_5210_, v___x_5204_);
if (v___x_5211_ == 0)
{
lean_object* v___x_5212_; lean_object* v___x_5213_; 
lean_dec(v___x_5210_);
lean_dec(v___x_5204_);
lean_dec_ref(v___x_5203_);
lean_dec_ref(v___x_5201_);
lean_del_object(v___x_5195_);
lean_dec_ref(v___x_5191_);
lean_dec(v___x_5177_);
lean_del_object(v___x_5093_);
lean_dec(v_a_5078_);
lean_dec(v_us_5070_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v___x_5212_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__22, &l_Lean_Meta_mkNoConfusion___closed__22_once, _init_l_Lean_Meta_mkNoConfusion___closed__22);
v___x_5213_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5212_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
return v___x_5213_;
}
else
{
lean_object* v___x_5215_; 
if (v_isShared_5094_ == 0)
{
lean_ctor_set_tag(v___x_5093_, 1);
lean_ctor_set(v___x_5093_, 1, v_us_5070_);
lean_ctor_set(v___x_5093_, 0, v_a_5078_);
v___x_5215_ = v___x_5093_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5078_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v_us_5070_);
v___x_5215_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5226_; 
v___x_5216_ = l_Lean_mkConst(v___x_5177_, v___x_5215_);
v___x_5217_ = l_Subarray_copy___redArg(v___x_5191_);
v___x_5218_ = l_Lean_mkAppN(v___x_5216_, v___x_5217_);
lean_dec_ref(v___x_5217_);
v___x_5219_ = lean_mk_empty_array_with_capacity(v___x_5188_);
v___x_5220_ = lean_array_push(v___x_5219_, v_target_5019_);
v___x_5221_ = l_Array_append___redArg(v___x_5220_, v___x_5201_);
lean_dec_ref(v___x_5201_);
v___x_5222_ = l_Array_append___redArg(v___x_5221_, v___x_5203_);
lean_dec_ref(v___x_5203_);
v___x_5223_ = l_Lean_mkAppN(v___x_5218_, v___x_5222_);
lean_dec_ref(v___x_5222_);
v___x_5224_ = lean_nat_sub(v___x_5204_, v___x_5210_);
lean_dec(v___x_5210_);
lean_dec(v___x_5204_);
if (v_isShared_5196_ == 0)
{
lean_ctor_set(v___x_5195_, 2, v___x_5188_);
lean_ctor_set(v___x_5195_, 1, v___x_5224_);
lean_ctor_set(v___x_5195_, 0, v___x_5173_);
v___x_5226_ = v___x_5195_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v___x_5173_);
lean_ctor_set(v_reuseFailAlloc_5253_, 1, v___x_5224_);
lean_ctor_set(v_reuseFailAlloc_5253_, 2, v___x_5188_);
v___x_5226_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
lean_object* v___x_5227_; 
v___x_5227_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5226_, v___x_5223_, v___x_5173_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
lean_dec_ref(v___x_5226_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5229_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc_n(v_a_5228_, 2);
lean_dec_ref_known(v___x_5227_, 1);
lean_inc(v___y_5182_);
lean_inc_ref(v___y_5181_);
lean_inc(v___y_5180_);
lean_inc_ref(v___y_5179_);
v___x_5229_ = lean_infer_type(v_a_5228_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5231_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_a_5230_);
lean_dec_ref_known(v___x_5229_, 1);
v___x_5231_ = l_Lean_Meta_whnfForall(v_a_5230_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
if (lean_obj_tag(v___x_5231_) == 0)
{
lean_object* v_a_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5252_; 
v_a_5232_ = lean_ctor_get(v___x_5231_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5231_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5234_ = v___x_5231_;
v_isShared_5235_ = v_isSharedCheck_5252_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_a_5232_);
lean_dec(v___x_5231_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5252_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___x_5236_; uint8_t v___x_5237_; 
v___x_5236_ = l_Lean_Expr_bindingDomain_x21(v_a_5232_);
lean_dec(v_a_5232_);
v___x_5237_ = l_Lean_Expr_isHEq(v___x_5236_);
lean_dec_ref(v___x_5236_);
if (v___x_5237_ == 0)
{
lean_object* v___x_5238_; lean_object* v___x_5240_; 
v___x_5238_ = l_Lean_Expr_app___override(v_a_5228_, v_h_5020_);
if (v_isShared_5235_ == 0)
{
lean_ctor_set(v___x_5234_, 0, v___x_5238_);
v___x_5240_ = v___x_5234_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v___x_5238_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
else
{
lean_object* v___x_5242_; 
lean_del_object(v___x_5234_);
v___x_5242_ = l_Lean_Meta_mkHEqOfEq(v_h_5020_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5251_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5245_ = v___x_5242_;
v_isShared_5246_ = v_isSharedCheck_5251_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5242_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5251_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5247_; lean_object* v___x_5249_; 
v___x_5247_ = l_Lean_Expr_app___override(v_a_5228_, v_a_5243_);
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v___x_5247_);
v___x_5249_ = v___x_5245_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5247_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
}
else
{
lean_dec(v_a_5228_);
return v___x_5242_;
}
}
}
}
else
{
lean_dec(v_a_5228_);
lean_dec_ref(v_h_5020_);
return v___x_5231_;
}
}
else
{
lean_dec(v_a_5228_);
lean_dec_ref(v_h_5020_);
return v___x_5229_;
}
}
else
{
lean_dec_ref(v_h_5020_);
return v___x_5227_;
}
}
}
}
}
}
else
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5265_; 
lean_dec(v___x_5177_);
lean_dec(v_numParams_5097_);
lean_del_object(v___x_5093_);
lean_dec(v_snd_5091_);
lean_dec(v_snd_5083_);
lean_dec(v_a_5078_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v_a_5258_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5260_ = v___x_5183_;
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v___x_5183_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5263_; 
if (v_isShared_5261_ == 0)
{
v___x_5263_ = v___x_5260_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5258_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
}
}
else
{
lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___f_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; 
lean_dec(v_numParams_5097_);
lean_dec_ref(v_toConstantVal_5095_);
lean_del_object(v___x_5093_);
lean_dec(v_snd_5091_);
lean_del_object(v___x_5085_);
lean_dec(v_snd_5083_);
lean_dec(v_a_5078_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v_h_5020_);
v___x_5283_ = lean_box(v___x_5073_);
v___x_5284_ = lean_box(v___x_5174_);
v___f_5285_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5285_, 0, v___x_5283_);
lean_closure_set(v___f_5285_, 1, v___x_5284_);
v___x_5286_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__24));
v___x_5287_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5286_, v_target_5019_, v___f_5285_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
return v___x_5287_;
}
}
}
}
else
{
lean_dec(v_a_5088_);
lean_del_object(v___x_5085_);
lean_dec(v_snd_5083_);
lean_dec(v_fst_5082_);
lean_dec(v_a_5078_);
lean_dec_ref(v_val_5076_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v___y_5044_ = v_a_5021_;
v___y_5045_ = v_a_5022_;
v___y_5046_ = v_a_5023_;
v___y_5047_ = v_a_5024_;
goto v___jp_5043_;
}
}
else
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
lean_del_object(v___x_5085_);
lean_dec(v_snd_5083_);
lean_dec(v_fst_5082_);
lean_dec(v_a_5078_);
lean_dec_ref(v_val_5076_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v_a_5289_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5087_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5087_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5294_; 
if (v_isShared_5292_ == 0)
{
v___x_5294_ = v___x_5291_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
}
}
else
{
lean_dec(v_a_5080_);
lean_dec(v_a_5078_);
lean_dec_ref(v_val_5076_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v___y_5044_ = v_a_5021_;
v___y_5045_ = v_a_5022_;
v___y_5046_ = v_a_5023_;
v___y_5047_ = v_a_5024_;
goto v___jp_5043_;
}
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
lean_dec(v_a_5078_);
lean_dec_ref(v_val_5076_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v_a_5298_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5079_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5079_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5301_ == 0)
{
v___x_5303_ = v___x_5300_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
else
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5313_; 
lean_dec_ref(v_val_5076_);
lean_dec(v_us_5070_);
lean_dec(v_a_5057_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v_a_5306_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5308_ = v___x_5077_;
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5077_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
if (v_isShared_5309_ == 0)
{
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
else
{
lean_dec(v_val_5075_);
lean_dec(v_us_5070_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v___y_5059_ = v_a_5021_;
v___y_5060_ = v_a_5022_;
v___y_5061_ = v_a_5023_;
v___y_5062_ = v_a_5024_;
goto v___jp_5058_;
}
}
}
else
{
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
v___y_5059_ = v_a_5021_;
v___y_5060_ = v_a_5022_;
v___y_5061_ = v_a_5023_;
v___y_5062_ = v_a_5024_;
goto v___jp_5058_;
}
v___jp_5058_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5063_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5064_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5065_ = l_Lean_indentExpr(v_a_5057_);
v___x_5066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5064_);
lean_ctor_set(v___x_5066_, 1, v___x_5065_);
v___x_5067_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5063_, v___x_5066_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
return v___x_5067_;
}
}
else
{
lean_dec_ref(v___x_5042_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
return v___x_5056_;
}
v___jp_5043_:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5048_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__6, &l_Lean_Meta_mkNoConfusion___closed__6_once, _init_l_Lean_Meta_mkNoConfusion___closed__6);
v___x_5049_ = l_Lean_MessageData_ofExpr(v___x_5041_);
v___x_5050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5050_, 0, v___x_5048_);
lean_ctor_set(v___x_5050_, 1, v___x_5049_);
v___x_5051_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__8, &l_Lean_Meta_mkNoConfusion___closed__8_once, _init_l_Lean_Meta_mkNoConfusion___closed__8);
v___x_5052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5050_);
lean_ctor_set(v___x_5052_, 1, v___x_5051_);
v___x_5053_ = l_Lean_MessageData_ofExpr(v___x_5042_);
v___x_5054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5052_);
lean_ctor_set(v___x_5054_, 1, v___x_5053_);
v___x_5055_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5054_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
return v___x_5055_;
}
}
}
else
{
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
return v___x_5028_;
}
}
else
{
lean_dec_ref(v_h_5020_);
lean_dec_ref(v_target_5019_);
return v___x_5026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5314_, lean_object* v_h_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = l_Lean_Meta_mkNoConfusion(v_target_5314_, v_h_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
lean_dec(v_a_5319_);
lean_dec_ref(v_a_5318_);
lean_dec(v_a_5317_);
lean_dec_ref(v_a_5316_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5322_, lean_object* v_b_5323_, lean_object* v_i_5324_, lean_object* v_hs_5325_, lean_object* v_hl_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v___x_5332_; 
v___x_5332_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5322_, v_b_5323_, v_i_5324_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
return v___x_5332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5333_, lean_object* v_b_5334_, lean_object* v_i_5335_, lean_object* v_hs_5336_, lean_object* v_hl_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5333_, v_b_5334_, v_i_5335_, v_hs_5336_, v_hl_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec_ref(v_range_5333_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5344_, lean_object* v_name_5345_, uint8_t v_bi_5346_, lean_object* v_type_5347_, lean_object* v_k_5348_, uint8_t v_kind_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
lean_object* v___x_5355_; 
v___x_5355_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5345_, v_bi_5346_, v_type_5347_, v_k_5348_, v_kind_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_);
return v___x_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5356_, lean_object* v_name_5357_, lean_object* v_bi_5358_, lean_object* v_type_5359_, lean_object* v_k_5360_, lean_object* v_kind_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_){
_start:
{
uint8_t v_bi_boxed_5367_; uint8_t v_kind_boxed_5368_; lean_object* v_res_5369_; 
v_bi_boxed_5367_ = lean_unbox(v_bi_5358_);
v_kind_boxed_5368_ = lean_unbox(v_kind_5361_);
v_res_5369_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5356_, v_name_5357_, v_bi_boxed_5367_, v_type_5359_, v_k_5360_, v_kind_boxed_5368_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
lean_dec(v___y_5365_);
lean_dec_ref(v___y_5364_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
return v_res_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5370_, lean_object* v_name_5371_, lean_object* v_type_5372_, lean_object* v_k_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_){
_start:
{
lean_object* v___x_5379_; 
v___x_5379_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5371_, v_type_5372_, v_k_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
return v___x_5379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5380_, lean_object* v_name_5381_, lean_object* v_type_5382_, lean_object* v_k_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
lean_object* v_res_5389_; 
v_res_5389_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5380_, v_name_5381_, v_type_5382_, v_k_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5395_, lean_object* v_e_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_){
_start:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5402_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5403_, 0, v_monad_5395_);
v___x_5404_ = lean_box(0);
v___x_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5405_, 0, v_e_5396_);
v___x_5406_ = lean_unsigned_to_nat(4u);
v___x_5407_ = lean_mk_empty_array_with_capacity(v___x_5406_);
v___x_5408_ = lean_array_push(v___x_5407_, v___x_5403_);
v___x_5409_ = lean_array_push(v___x_5408_, v___x_5404_);
v___x_5410_ = lean_array_push(v___x_5409_, v___x_5404_);
v___x_5411_ = lean_array_push(v___x_5410_, v___x_5405_);
v___x_5412_ = l_Lean_Meta_mkAppOptM(v___x_5402_, v___x_5411_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5413_, lean_object* v_e_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l_Lean_Meta_mkPure(v_monad_5413_, v_e_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
lean_dec(v_a_5416_);
lean_dec_ref(v_a_5415_);
return v_res_5420_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5430_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5431_ = l_Lean_MessageData_ofFormat(v___x_5430_);
return v___x_5431_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; 
v___x_5435_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5436_ = l_Lean_MessageData_ofFormat(v___x_5435_);
return v___x_5436_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5440_; lean_object* v___x_5441_; 
v___x_5440_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5441_ = l_Lean_MessageData_ofFormat(v___x_5440_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5442_, lean_object* v_fieldName_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_){
_start:
{
lean_object* v___x_5449_; 
lean_inc(v_a_5447_);
lean_inc_ref(v_a_5446_);
lean_inc(v_a_5445_);
lean_inc_ref(v_a_5444_);
lean_inc_ref(v_s_5442_);
v___x_5449_ = lean_infer_type(v_s_5442_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5546_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5452_ = v___x_5449_;
v_isShared_5453_ = v_isSharedCheck_5546_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5449_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5546_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5454_; 
lean_inc(v_a_5447_);
lean_inc_ref(v_a_5446_);
lean_inc(v_a_5445_);
lean_inc_ref(v_a_5444_);
v___x_5454_ = lean_whnf(v_a_5450_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5545_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5457_ = v___x_5454_;
v_isShared_5458_ = v_isSharedCheck_5545_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___x_5454_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5545_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___y_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___y_5463_; lean_object* v___x_5478_; 
v___x_5478_ = l_Lean_Expr_getAppFn(v_a_5455_);
if (lean_obj_tag(v___x_5478_) == 4)
{
lean_object* v_declName_5479_; lean_object* v_us_5480_; lean_object* v___x_5481_; lean_object* v_env_5482_; lean_object* v___y_5484_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; uint8_t v___x_5526_; 
v_declName_5479_ = lean_ctor_get(v___x_5478_, 0);
lean_inc_n(v_declName_5479_, 2);
v_us_5480_ = lean_ctor_get(v___x_5478_, 1);
lean_inc(v_us_5480_);
lean_dec_ref_known(v___x_5478_, 2);
v___x_5481_ = lean_st_ref_get(v_a_5447_);
v_env_5482_ = lean_ctor_get(v___x_5481_, 0);
lean_inc_ref_n(v_env_5482_, 2);
lean_dec(v___x_5481_);
v___x_5526_ = l_Lean_isStructure(v_env_5482_, v_declName_5479_);
if (v___x_5526_ == 0)
{
lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5527_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5528_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5455_);
lean_inc_ref(v_s_5442_);
v___x_5529_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5442_, v_a_5455_);
v___x_5530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5530_, 0, v___x_5528_);
lean_ctor_set(v___x_5530_, 1, v___x_5529_);
v___x_5531_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5527_, v___x_5530_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_dec_ref_known(v___x_5531_, 1);
v___y_5484_ = v_a_5444_;
v___y_5485_ = v_a_5445_;
v___y_5486_ = v_a_5446_;
v___y_5487_ = v_a_5447_;
goto v___jp_5483_;
}
else
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5539_; 
lean_dec_ref(v_env_5482_);
lean_dec(v_us_5480_);
lean_dec(v_declName_5479_);
lean_del_object(v___x_5457_);
lean_dec(v_a_5455_);
lean_del_object(v___x_5452_);
lean_dec(v_fieldName_5443_);
lean_dec_ref(v_s_5442_);
v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5531_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5531_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
else
{
v___y_5484_ = v_a_5444_;
v___y_5485_ = v_a_5445_;
v___y_5486_ = v_a_5446_;
v___y_5487_ = v_a_5447_;
goto v___jp_5483_;
}
v___jp_5483_:
{
lean_object* v___x_5488_; 
lean_inc(v_fieldName_5443_);
lean_inc(v_declName_5479_);
lean_inc_ref(v_env_5482_);
v___x_5488_ = l_Lean_getProjFnForField_x3f(v_env_5482_, v_declName_5479_, v_fieldName_5443_);
if (lean_obj_tag(v___x_5488_) == 0)
{
lean_object* v___x_5489_; lean_object* v___x_5490_; size_t v_sz_5491_; size_t v___x_5492_; lean_object* v___x_5493_; 
lean_dec(v_us_5480_);
lean_del_object(v___x_5457_);
lean_inc(v_declName_5479_);
lean_inc_ref(v_env_5482_);
v___x_5489_ = l_Lean_getStructureFields(v_env_5482_, v_declName_5479_);
v___x_5490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5491_ = lean_array_size(v___x_5489_);
v___x_5492_ = ((size_t)0ULL);
lean_inc(v_fieldName_5443_);
lean_inc_ref(v_s_5442_);
v___x_5493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5482_, v_declName_5479_, v_s_5442_, v_fieldName_5443_, v___x_5489_, v_sz_5491_, v___x_5492_, v___x_5490_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_);
lean_dec_ref(v___x_5489_);
if (lean_obj_tag(v___x_5493_) == 0)
{
lean_object* v_a_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5504_; 
v_a_5494_ = lean_ctor_get(v___x_5493_, 0);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5496_ = v___x_5493_;
v_isShared_5497_ = v_isSharedCheck_5504_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_a_5494_);
lean_dec(v___x_5493_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5504_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v_fst_5498_; 
v_fst_5498_ = lean_ctor_get(v_a_5494_, 0);
lean_inc(v_fst_5498_);
lean_dec(v_a_5494_);
if (lean_obj_tag(v_fst_5498_) == 0)
{
lean_del_object(v___x_5496_);
v___y_5460_ = v___y_5484_;
v___y_5461_ = v___y_5486_;
v___y_5462_ = v___y_5487_;
v___y_5463_ = v___y_5485_;
goto v___jp_5459_;
}
else
{
lean_object* v_val_5499_; 
v_val_5499_ = lean_ctor_get(v_fst_5498_, 0);
lean_inc(v_val_5499_);
lean_dec_ref_known(v_fst_5498_, 1);
if (lean_obj_tag(v_val_5499_) == 0)
{
lean_del_object(v___x_5496_);
v___y_5460_ = v___y_5484_;
v___y_5461_ = v___y_5486_;
v___y_5462_ = v___y_5487_;
v___y_5463_ = v___y_5485_;
goto v___jp_5459_;
}
else
{
lean_object* v_val_5500_; lean_object* v___x_5502_; 
lean_dec(v_a_5455_);
lean_del_object(v___x_5452_);
lean_dec(v_fieldName_5443_);
lean_dec_ref(v_s_5442_);
v_val_5500_ = lean_ctor_get(v_val_5499_, 0);
lean_inc(v_val_5500_);
lean_dec_ref_known(v_val_5499_, 1);
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 0, v_val_5500_);
v___x_5502_ = v___x_5496_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v_val_5500_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
}
}
else
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5512_; 
lean_dec(v_a_5455_);
lean_del_object(v___x_5452_);
lean_dec(v_fieldName_5443_);
lean_dec_ref(v_s_5442_);
v_a_5505_ = lean_ctor_get(v___x_5493_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5507_ = v___x_5493_;
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5493_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
if (v_isShared_5508_ == 0)
{
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_a_5505_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
else
{
lean_object* v_val_5513_; lean_object* v_dummy_5514_; lean_object* v_nargs_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5524_; 
lean_dec_ref(v_env_5482_);
lean_dec(v_declName_5479_);
lean_del_object(v___x_5452_);
lean_dec(v_fieldName_5443_);
v_val_5513_ = lean_ctor_get(v___x_5488_, 0);
lean_inc(v_val_5513_);
lean_dec_ref_known(v___x_5488_, 1);
v_dummy_5514_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5515_ = l_Lean_Expr_getAppNumArgs(v_a_5455_);
lean_inc(v_nargs_5515_);
v___x_5516_ = lean_mk_array(v_nargs_5515_, v_dummy_5514_);
v___x_5517_ = lean_unsigned_to_nat(1u);
v___x_5518_ = lean_nat_sub(v_nargs_5515_, v___x_5517_);
lean_dec(v_nargs_5515_);
v___x_5519_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5455_, v___x_5516_, v___x_5518_);
v___x_5520_ = l_Lean_mkConst(v_val_5513_, v_us_5480_);
v___x_5521_ = l_Lean_mkAppN(v___x_5520_, v___x_5519_);
lean_dec_ref(v___x_5519_);
v___x_5522_ = l_Lean_Expr_app___override(v___x_5521_, v_s_5442_);
if (v_isShared_5458_ == 0)
{
lean_ctor_set(v___x_5457_, 0, v___x_5522_);
v___x_5524_ = v___x_5457_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v___x_5522_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
}
else
{
lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; 
lean_dec_ref(v___x_5478_);
lean_del_object(v___x_5457_);
lean_del_object(v___x_5452_);
lean_dec(v_fieldName_5443_);
v___x_5540_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5541_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5542_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5442_, v_a_5455_);
v___x_5543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5543_, 0, v___x_5541_);
lean_ctor_set(v___x_5543_, 1, v___x_5542_);
v___x_5544_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5540_, v___x_5543_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_);
return v___x_5544_;
}
v___jp_5459_:
{
lean_object* v___x_5464_; lean_object* v___x_5465_; uint8_t v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5469_; 
v___x_5464_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5465_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5466_ = 1;
v___x_5467_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5443_, v___x_5466_);
if (v_isShared_5453_ == 0)
{
lean_ctor_set_tag(v___x_5452_, 3);
lean_ctor_set(v___x_5452_, 0, v___x_5467_);
v___x_5469_ = v___x_5452_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v___x_5467_);
v___x_5469_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; 
v___x_5470_ = l_Lean_MessageData_ofFormat(v___x_5469_);
v___x_5471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5471_, 0, v___x_5465_);
lean_ctor_set(v___x_5471_, 1, v___x_5470_);
v___x_5472_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5473_, 0, v___x_5471_);
lean_ctor_set(v___x_5473_, 1, v___x_5472_);
v___x_5474_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5442_, v_a_5455_);
v___x_5475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5475_, 0, v___x_5473_);
lean_ctor_set(v___x_5475_, 1, v___x_5474_);
v___x_5476_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5464_, v___x_5475_, v___y_5460_, v___y_5463_, v___y_5461_, v___y_5462_);
return v___x_5476_;
}
}
}
}
else
{
lean_del_object(v___x_5452_);
lean_dec(v_fieldName_5443_);
lean_dec_ref(v_s_5442_);
return v___x_5454_;
}
}
}
else
{
lean_dec(v_fieldName_5443_);
lean_dec_ref(v_s_5442_);
return v___x_5449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5547_, lean_object* v_declName_5548_, lean_object* v_s_5549_, lean_object* v_fieldName_5550_, lean_object* v_as_5551_, size_t v_sz_5552_, size_t v_i_5553_, lean_object* v_b_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_){
_start:
{
lean_object* v_a_5561_; uint8_t v___x_5565_; 
v___x_5565_ = lean_usize_dec_lt(v_i_5553_, v_sz_5552_);
if (v___x_5565_ == 0)
{
lean_object* v___x_5566_; 
lean_dec(v_fieldName_5550_);
lean_dec_ref(v_s_5549_);
lean_dec(v_declName_5548_);
lean_dec_ref(v___x_5547_);
v___x_5566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5566_, 0, v_b_5554_);
return v___x_5566_;
}
else
{
lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v_a_5569_; lean_object* v___x_5570_; 
lean_dec_ref(v_b_5554_);
v___x_5567_ = lean_box(0);
v___x_5568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5569_ = lean_array_uget_borrowed(v_as_5551_, v_i_5553_);
lean_inc(v_a_5569_);
lean_inc(v_declName_5548_);
lean_inc_ref(v___x_5547_);
v___x_5570_ = l_Lean_isSubobjectField_x3f(v___x_5547_, v_declName_5548_, v_a_5569_);
if (lean_obj_tag(v___x_5570_) == 0)
{
v_a_5561_ = v___x_5568_;
goto v___jp_5560_;
}
else
{
lean_object* v___x_5572_; uint8_t v_isShared_5573_; uint8_t v_isSharedCheck_5630_; 
v_isSharedCheck_5630_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5630_ == 0)
{
lean_object* v_unused_5631_; 
v_unused_5631_ = lean_ctor_get(v___x_5570_, 0);
lean_dec(v_unused_5631_);
v___x_5572_ = v___x_5570_;
v_isShared_5573_ = v_isSharedCheck_5630_;
goto v_resetjp_5571_;
}
else
{
lean_dec(v___x_5570_);
v___x_5572_ = lean_box(0);
v_isShared_5573_ = v_isSharedCheck_5630_;
goto v_resetjp_5571_;
}
v_resetjp_5571_:
{
lean_object* v___x_5574_; 
lean_inc(v_a_5569_);
lean_inc_ref(v_s_5549_);
v___x_5574_ = l_Lean_Meta_mkProjection(v_s_5549_, v_a_5569_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v_a_5575_; lean_object* v___x_5576_; 
v_a_5575_ = lean_ctor_get(v___x_5574_, 0);
lean_inc(v_a_5575_);
lean_dec_ref_known(v___x_5574_, 1);
v___x_5576_ = l_Lean_Meta_saveState___redArg(v___y_5556_, v___y_5558_);
if (lean_obj_tag(v___x_5576_) == 0)
{
lean_object* v_a_5577_; lean_object* v___x_5578_; 
v_a_5577_ = lean_ctor_get(v___x_5576_, 0);
lean_inc(v_a_5577_);
lean_dec_ref_known(v___x_5576_, 1);
lean_inc(v_fieldName_5550_);
v___x_5578_ = l_Lean_Meta_mkProjection(v_a_5575_, v_fieldName_5550_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5591_; 
lean_dec(v_a_5577_);
lean_dec(v_fieldName_5550_);
lean_dec_ref(v_s_5549_);
lean_dec(v_declName_5548_);
lean_dec_ref(v___x_5547_);
v_a_5579_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5581_ = v___x_5578_;
v_isShared_5582_ = v_isSharedCheck_5591_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v___x_5578_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5591_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5584_; 
if (v_isShared_5573_ == 0)
{
lean_ctor_set(v___x_5572_, 0, v_a_5579_);
v___x_5584_ = v___x_5572_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5579_);
v___x_5584_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5588_; 
v___x_5585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
v___x_5586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5585_);
lean_ctor_set(v___x_5586_, 1, v___x_5567_);
if (v_isShared_5582_ == 0)
{
lean_ctor_set(v___x_5581_, 0, v___x_5586_);
v___x_5588_ = v___x_5581_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5586_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5613_; 
lean_del_object(v___x_5572_);
v_a_5592_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5594_ = v___x_5578_;
v_isShared_5595_ = v_isSharedCheck_5613_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5578_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5613_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
uint8_t v___x_5596_; 
v___x_5596_ = l_Lean_Exception_isInterrupt(v_a_5592_);
if (v___x_5596_ == 0)
{
uint8_t v___x_5597_; 
lean_inc(v_a_5592_);
v___x_5597_ = l_Lean_Exception_isRuntime(v_a_5592_);
if (v___x_5597_ == 0)
{
lean_object* v___x_5598_; 
lean_del_object(v___x_5594_);
lean_dec(v_a_5592_);
v___x_5598_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5577_, v___y_5556_, v___y_5558_);
if (lean_obj_tag(v___x_5598_) == 0)
{
lean_dec_ref_known(v___x_5598_, 1);
v_a_5561_ = v___x_5568_;
goto v___jp_5560_;
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5606_; 
lean_dec(v_fieldName_5550_);
lean_dec_ref(v_s_5549_);
lean_dec(v_declName_5548_);
lean_dec_ref(v___x_5547_);
v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5601_ = v___x_5598_;
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5598_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_a_5599_);
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
lean_object* v___x_5608_; 
lean_dec(v_a_5577_);
lean_dec(v_fieldName_5550_);
lean_dec_ref(v_s_5549_);
lean_dec(v_declName_5548_);
lean_dec_ref(v___x_5547_);
if (v_isShared_5595_ == 0)
{
v___x_5608_ = v___x_5594_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5592_);
v___x_5608_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
return v___x_5608_;
}
}
}
else
{
lean_object* v___x_5611_; 
lean_dec(v_a_5577_);
lean_dec(v_fieldName_5550_);
lean_dec_ref(v_s_5549_);
lean_dec(v_declName_5548_);
lean_dec_ref(v___x_5547_);
if (v_isShared_5595_ == 0)
{
v___x_5611_ = v___x_5594_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5592_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
return v___x_5611_;
}
}
}
}
}
else
{
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5621_; 
lean_dec(v_a_5575_);
lean_del_object(v___x_5572_);
lean_dec(v_fieldName_5550_);
lean_dec_ref(v_s_5549_);
lean_dec(v_declName_5548_);
lean_dec_ref(v___x_5547_);
v_a_5614_ = lean_ctor_get(v___x_5576_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5576_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5616_ = v___x_5576_;
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5576_);
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
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5629_; 
lean_del_object(v___x_5572_);
lean_dec(v_fieldName_5550_);
lean_dec_ref(v_s_5549_);
lean_dec(v_declName_5548_);
lean_dec_ref(v___x_5547_);
v_a_5622_ = lean_ctor_get(v___x_5574_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5574_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5574_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5627_; 
if (v_isShared_5625_ == 0)
{
v___x_5627_ = v___x_5624_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_a_5622_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
}
}
}
v___jp_5560_:
{
size_t v___x_5562_; size_t v___x_5563_; 
v___x_5562_ = ((size_t)1ULL);
v___x_5563_ = lean_usize_add(v_i_5553_, v___x_5562_);
lean_inc_ref(v_a_5561_);
v_i_5553_ = v___x_5563_;
v_b_5554_ = v_a_5561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5632_, lean_object* v_declName_5633_, lean_object* v_s_5634_, lean_object* v_fieldName_5635_, lean_object* v_as_5636_, lean_object* v_sz_5637_, lean_object* v_i_5638_, lean_object* v_b_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
size_t v_sz_boxed_5645_; size_t v_i_boxed_5646_; lean_object* v_res_5647_; 
v_sz_boxed_5645_ = lean_unbox_usize(v_sz_5637_);
lean_dec(v_sz_5637_);
v_i_boxed_5646_ = lean_unbox_usize(v_i_5638_);
lean_dec(v_i_5638_);
v_res_5647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5632_, v_declName_5633_, v_s_5634_, v_fieldName_5635_, v_as_5636_, v_sz_boxed_5645_, v_i_boxed_5646_, v_b_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec_ref(v___y_5640_);
lean_dec_ref(v_as_5636_);
return v_res_5647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5648_, lean_object* v_fieldName_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_){
_start:
{
lean_object* v_res_5655_; 
v_res_5655_ = l_Lean_Meta_mkProjection(v_s_5648_, v_fieldName_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_);
lean_dec(v_a_5653_);
lean_dec_ref(v_a_5652_);
lean_dec(v_a_5651_);
lean_dec_ref(v_a_5650_);
return v_res_5655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5656_, lean_object* v_cons_5657_, lean_object* v_x_5658_){
_start:
{
if (lean_obj_tag(v_x_5658_) == 0)
{
lean_dec_ref(v_cons_5657_);
lean_inc_ref(v_nil_5656_);
return v_nil_5656_;
}
else
{
lean_object* v_head_5659_; lean_object* v_tail_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; 
v_head_5659_ = lean_ctor_get(v_x_5658_, 0);
lean_inc(v_head_5659_);
v_tail_5660_ = lean_ctor_get(v_x_5658_, 1);
lean_inc(v_tail_5660_);
lean_dec_ref_known(v_x_5658_, 2);
lean_inc_ref(v_cons_5657_);
v___x_5661_ = l_Lean_Expr_app___override(v_cons_5657_, v_head_5659_);
v___x_5662_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5656_, v_cons_5657_, v_tail_5660_);
v___x_5663_ = l_Lean_Expr_app___override(v___x_5661_, v___x_5662_);
return v___x_5663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5664_, lean_object* v_cons_5665_, lean_object* v_x_5666_){
_start:
{
lean_object* v_res_5667_; 
v_res_5667_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5664_, v_cons_5665_, v_x_5666_);
lean_dec_ref(v_nil_5664_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5677_, lean_object* v_xs_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_){
_start:
{
lean_object* v___x_5684_; 
lean_inc_ref(v_type_5677_);
v___x_5684_ = l_Lean_Meta_getDecLevel(v_type_5677_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v_a_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5704_; 
v_a_5685_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5687_ = v___x_5684_;
v_isShared_5688_ = v_isSharedCheck_5704_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_a_5685_);
lean_dec(v___x_5684_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5704_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; 
v___x_5689_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5690_ = lean_box(0);
v___x_5691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5691_, 0, v_a_5685_);
lean_ctor_set(v___x_5691_, 1, v___x_5690_);
lean_inc_ref(v___x_5691_);
v___x_5692_ = l_Lean_mkConst(v___x_5689_, v___x_5691_);
lean_inc_ref(v_type_5677_);
v___x_5693_ = l_Lean_Expr_app___override(v___x_5692_, v_type_5677_);
if (lean_obj_tag(v_xs_5678_) == 0)
{
lean_object* v___x_5695_; 
lean_dec_ref_known(v___x_5691_, 2);
lean_dec_ref(v_type_5677_);
if (v_isShared_5688_ == 0)
{
lean_ctor_set(v___x_5687_, 0, v___x_5693_);
v___x_5695_ = v___x_5687_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5693_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
else
{
lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5702_; 
v___x_5697_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5698_ = l_Lean_mkConst(v___x_5697_, v___x_5691_);
v___x_5699_ = l_Lean_Expr_app___override(v___x_5698_, v_type_5677_);
v___x_5700_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5693_, v___x_5699_, v_xs_5678_);
lean_dec_ref(v___x_5693_);
if (v_isShared_5688_ == 0)
{
lean_ctor_set(v___x_5687_, 0, v___x_5700_);
v___x_5702_ = v___x_5687_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v___x_5700_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
}
else
{
lean_object* v_a_5705_; lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5712_; 
lean_dec(v_xs_5678_);
lean_dec_ref(v_type_5677_);
v_a_5705_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5712_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5712_ == 0)
{
v___x_5707_ = v___x_5684_;
v_isShared_5708_ = v_isSharedCheck_5712_;
goto v_resetjp_5706_;
}
else
{
lean_inc(v_a_5705_);
lean_dec(v___x_5684_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5712_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
lean_object* v___x_5710_; 
if (v_isShared_5708_ == 0)
{
v___x_5710_ = v___x_5707_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v_a_5705_);
v___x_5710_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
return v___x_5710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5713_, lean_object* v_xs_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_){
_start:
{
lean_object* v_res_5720_; 
v_res_5720_ = l_Lean_Meta_mkListLit(v_type_5713_, v_xs_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_);
lean_dec(v_a_5718_);
lean_dec_ref(v_a_5717_);
lean_dec(v_a_5716_);
lean_dec_ref(v_a_5715_);
return v_res_5720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5725_, lean_object* v_xs_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_){
_start:
{
lean_object* v___x_5732_; 
lean_inc_ref(v_type_5725_);
v___x_5732_ = l_Lean_Meta_getDecLevel(v_type_5725_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_);
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v_a_5733_; lean_object* v___x_5734_; 
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
lean_inc(v_a_5733_);
lean_dec_ref_known(v___x_5732_, 1);
lean_inc_ref(v_type_5725_);
v___x_5734_ = l_Lean_Meta_mkListLit(v_type_5725_, v_xs_5726_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v_a_5735_; lean_object* v___x_5737_; uint8_t v_isShared_5738_; uint8_t v_isSharedCheck_5748_; 
v_a_5735_ = lean_ctor_get(v___x_5734_, 0);
v_isSharedCheck_5748_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5748_ == 0)
{
v___x_5737_ = v___x_5734_;
v_isShared_5738_ = v_isSharedCheck_5748_;
goto v_resetjp_5736_;
}
else
{
lean_inc(v_a_5735_);
lean_dec(v___x_5734_);
v___x_5737_ = lean_box(0);
v_isShared_5738_ = v_isSharedCheck_5748_;
goto v_resetjp_5736_;
}
v_resetjp_5736_:
{
lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5746_; 
v___x_5739_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5740_ = lean_box(0);
v___x_5741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5741_, 0, v_a_5733_);
lean_ctor_set(v___x_5741_, 1, v___x_5740_);
v___x_5742_ = l_Lean_mkConst(v___x_5739_, v___x_5741_);
v___x_5743_ = l_Lean_Expr_app___override(v___x_5742_, v_type_5725_);
v___x_5744_ = l_Lean_Expr_app___override(v___x_5743_, v_a_5735_);
if (v_isShared_5738_ == 0)
{
lean_ctor_set(v___x_5737_, 0, v___x_5744_);
v___x_5746_ = v___x_5737_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v___x_5744_);
v___x_5746_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
return v___x_5746_;
}
}
}
else
{
lean_dec(v_a_5733_);
lean_dec_ref(v_type_5725_);
return v___x_5734_;
}
}
else
{
lean_object* v_a_5749_; lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5756_; 
lean_dec(v_xs_5726_);
lean_dec_ref(v_type_5725_);
v_a_5749_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5751_ = v___x_5732_;
v_isShared_5752_ = v_isSharedCheck_5756_;
goto v_resetjp_5750_;
}
else
{
lean_inc(v_a_5749_);
lean_dec(v___x_5732_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5756_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v___x_5754_; 
if (v_isShared_5752_ == 0)
{
v___x_5754_ = v___x_5751_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_a_5749_);
v___x_5754_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5753_;
}
v_reusejp_5753_:
{
return v___x_5754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5757_, lean_object* v_xs_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_){
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l_Lean_Meta_mkArrayLit(v_type_5757_, v_xs_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_);
lean_dec(v_a_5762_);
lean_dec_ref(v_a_5761_);
lean_dec(v_a_5760_);
lean_dec_ref(v_a_5759_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_){
_start:
{
lean_object* v___x_5776_; 
lean_inc_ref(v_type_5770_);
v___x_5776_ = l_Lean_Meta_getDecLevel(v_type_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_);
if (lean_obj_tag(v___x_5776_) == 0)
{
lean_object* v_a_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5789_; 
v_a_5777_ = lean_ctor_get(v___x_5776_, 0);
v_isSharedCheck_5789_ = !lean_is_exclusive(v___x_5776_);
if (v_isSharedCheck_5789_ == 0)
{
v___x_5779_ = v___x_5776_;
v_isShared_5780_ = v_isSharedCheck_5789_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_a_5777_);
lean_dec(v___x_5776_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5789_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5787_; 
v___x_5781_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5782_ = lean_box(0);
v___x_5783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5783_, 0, v_a_5777_);
lean_ctor_set(v___x_5783_, 1, v___x_5782_);
v___x_5784_ = l_Lean_mkConst(v___x_5781_, v___x_5783_);
v___x_5785_ = l_Lean_Expr_app___override(v___x_5784_, v_type_5770_);
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 0, v___x_5785_);
v___x_5787_ = v___x_5779_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v___x_5785_);
v___x_5787_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
return v___x_5787_;
}
}
}
else
{
lean_object* v_a_5790_; lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5797_; 
lean_dec_ref(v_type_5770_);
v_a_5790_ = lean_ctor_get(v___x_5776_, 0);
v_isSharedCheck_5797_ = !lean_is_exclusive(v___x_5776_);
if (v_isSharedCheck_5797_ == 0)
{
v___x_5792_ = v___x_5776_;
v_isShared_5793_ = v_isSharedCheck_5797_;
goto v_resetjp_5791_;
}
else
{
lean_inc(v_a_5790_);
lean_dec(v___x_5776_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5797_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
lean_object* v___x_5795_; 
if (v_isShared_5793_ == 0)
{
v___x_5795_ = v___x_5792_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v_a_5790_);
v___x_5795_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
return v___x_5795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_){
_start:
{
lean_object* v_res_5804_; 
v_res_5804_ = l_Lean_Meta_mkNone(v_type_5798_, v_a_5799_, v_a_5800_, v_a_5801_, v_a_5802_);
lean_dec(v_a_5802_);
lean_dec_ref(v_a_5801_);
lean_dec(v_a_5800_);
lean_dec_ref(v_a_5799_);
return v_res_5804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5809_, lean_object* v_value_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_){
_start:
{
lean_object* v___x_5816_; 
lean_inc_ref(v_type_5809_);
v___x_5816_ = l_Lean_Meta_getDecLevel(v_type_5809_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_);
if (lean_obj_tag(v___x_5816_) == 0)
{
lean_object* v_a_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5829_; 
v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5829_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5829_ == 0)
{
v___x_5819_ = v___x_5816_;
v_isShared_5820_ = v_isSharedCheck_5829_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_a_5817_);
lean_dec(v___x_5816_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5829_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5827_; 
v___x_5821_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5822_ = lean_box(0);
v___x_5823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5823_, 0, v_a_5817_);
lean_ctor_set(v___x_5823_, 1, v___x_5822_);
v___x_5824_ = l_Lean_mkConst(v___x_5821_, v___x_5823_);
v___x_5825_ = l_Lean_mkAppB(v___x_5824_, v_type_5809_, v_value_5810_);
if (v_isShared_5820_ == 0)
{
lean_ctor_set(v___x_5819_, 0, v___x_5825_);
v___x_5827_ = v___x_5819_;
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
lean_object* v_a_5830_; lean_object* v___x_5832_; uint8_t v_isShared_5833_; uint8_t v_isSharedCheck_5837_; 
lean_dec_ref(v_value_5810_);
lean_dec_ref(v_type_5809_);
v_a_5830_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5837_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5837_ == 0)
{
v___x_5832_ = v___x_5816_;
v_isShared_5833_ = v_isSharedCheck_5837_;
goto v_resetjp_5831_;
}
else
{
lean_inc(v_a_5830_);
lean_dec(v___x_5816_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5838_, lean_object* v_value_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_){
_start:
{
lean_object* v_res_5845_; 
v_res_5845_ = l_Lean_Meta_mkSome(v_type_5838_, v_value_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_);
lean_dec(v_a_5843_);
lean_dec_ref(v_a_5842_);
lean_dec(v_a_5841_);
lean_dec_ref(v_a_5840_);
return v_res_5845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5857_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5858_, 0, v_p_5851_);
v___x_5859_ = lean_box(0);
v___x_5860_ = lean_unsigned_to_nat(2u);
v___x_5861_ = lean_mk_empty_array_with_capacity(v___x_5860_);
v___x_5862_ = lean_array_push(v___x_5861_, v___x_5858_);
v___x_5863_ = lean_array_push(v___x_5862_, v___x_5859_);
v___x_5864_ = l_Lean_Meta_mkAppOptM(v___x_5857_, v___x_5863_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5865_, lean_object* v_a_5866_, lean_object* v_a_5867_, lean_object* v_a_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_){
_start:
{
lean_object* v_res_5871_; 
v_res_5871_ = l_Lean_Meta_mkDecide(v_p_5865_, v_a_5866_, v_a_5867_, v_a_5868_, v_a_5869_);
lean_dec(v_a_5869_);
lean_dec_ref(v_a_5868_);
lean_dec(v_a_5867_);
lean_dec_ref(v_a_5866_);
return v_res_5871_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; 
v___x_5877_ = lean_box(0);
v___x_5878_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5879_ = l_Lean_mkConst(v___x_5878_, v___x_5877_);
return v___x_5879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_){
_start:
{
lean_object* v___x_5889_; 
v___x_5889_ = l_Lean_Meta_mkDecide(v_p_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_);
if (lean_obj_tag(v___x_5889_) == 0)
{
lean_object* v_a_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v_a_5890_ = lean_ctor_get(v___x_5889_, 0);
lean_inc(v_a_5890_);
lean_dec_ref_known(v___x_5889_, 1);
v___x_5891_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5892_ = l_Lean_Meta_mkEq(v_a_5890_, v___x_5891_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_);
if (lean_obj_tag(v___x_5892_) == 0)
{
lean_object* v_a_5893_; lean_object* v___x_5894_; 
v_a_5893_ = lean_ctor_get(v___x_5892_, 0);
lean_inc(v_a_5893_);
lean_dec_ref_known(v___x_5892_, 1);
v___x_5894_ = l_Lean_Meta_mkEqRefl(v___x_5891_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_);
if (lean_obj_tag(v___x_5894_) == 0)
{
lean_object* v_a_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; 
v_a_5895_ = lean_ctor_get(v___x_5894_, 0);
lean_inc(v_a_5895_);
lean_dec_ref_known(v___x_5894_, 1);
v___x_5896_ = l_Lean_Meta_mkExpectedPropHint(v_a_5895_, v_a_5893_);
v___x_5897_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5898_ = lean_unsigned_to_nat(1u);
v___x_5899_ = lean_mk_empty_array_with_capacity(v___x_5898_);
v___x_5900_ = lean_array_push(v___x_5899_, v___x_5896_);
v___x_5901_ = l_Lean_Meta_mkAppM(v___x_5897_, v___x_5900_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_);
return v___x_5901_;
}
else
{
lean_dec(v_a_5893_);
return v___x_5894_;
}
}
else
{
return v___x_5892_;
}
}
else
{
return v___x_5889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_, lean_object* v_a_5906_, lean_object* v_a_5907_){
_start:
{
lean_object* v_res_5908_; 
v_res_5908_ = l_Lean_Meta_mkDecideProof(v_p_5902_, v_a_5903_, v_a_5904_, v_a_5905_, v_a_5906_);
lean_dec(v_a_5906_);
lean_dec_ref(v_a_5905_);
lean_dec(v_a_5904_);
lean_dec_ref(v_a_5903_);
return v_res_5908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5914_, lean_object* v_b_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_){
_start:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; 
v___x_5921_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_5922_ = lean_unsigned_to_nat(2u);
v___x_5923_ = lean_mk_empty_array_with_capacity(v___x_5922_);
v___x_5924_ = lean_array_push(v___x_5923_, v_a_5914_);
v___x_5925_ = lean_array_push(v___x_5924_, v_b_5915_);
v___x_5926_ = l_Lean_Meta_mkAppM(v___x_5921_, v___x_5925_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_);
return v___x_5926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_5927_, lean_object* v_b_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_){
_start:
{
lean_object* v_res_5934_; 
v_res_5934_ = l_Lean_Meta_mkLt(v_a_5927_, v_b_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_);
lean_dec(v_a_5932_);
lean_dec_ref(v_a_5931_);
lean_dec(v_a_5930_);
lean_dec_ref(v_a_5929_);
return v_res_5934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_5940_, lean_object* v_b_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; 
v___x_5947_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_5948_ = lean_unsigned_to_nat(2u);
v___x_5949_ = lean_mk_empty_array_with_capacity(v___x_5948_);
v___x_5950_ = lean_array_push(v___x_5949_, v_a_5940_);
v___x_5951_ = lean_array_push(v___x_5950_, v_b_5941_);
v___x_5952_ = l_Lean_Meta_mkAppM(v___x_5947_, v___x_5951_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_);
return v___x_5952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_5953_, lean_object* v_b_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_){
_start:
{
lean_object* v_res_5960_; 
v_res_5960_ = l_Lean_Meta_mkLe(v_a_5953_, v_b_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_);
lean_dec(v_a_5958_);
lean_dec_ref(v_a_5957_);
lean_dec(v_a_5956_);
lean_dec_ref(v_a_5955_);
return v_res_5960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_){
_start:
{
lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; 
v___x_5972_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_5973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5973_, 0, v_00_u03b1_5966_);
v___x_5974_ = lean_box(0);
v___x_5975_ = lean_unsigned_to_nat(2u);
v___x_5976_ = lean_mk_empty_array_with_capacity(v___x_5975_);
v___x_5977_ = lean_array_push(v___x_5976_, v___x_5973_);
v___x_5978_ = lean_array_push(v___x_5977_, v___x_5974_);
v___x_5979_ = l_Lean_Meta_mkAppOptM(v___x_5972_, v___x_5978_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_);
return v___x_5979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_){
_start:
{
lean_object* v_res_5986_; 
v_res_5986_ = l_Lean_Meta_mkDefault(v_00_u03b1_5980_, v_a_5981_, v_a_5982_, v_a_5983_, v_a_5984_);
lean_dec(v_a_5984_);
lean_dec_ref(v_a_5983_);
lean_dec(v_a_5982_);
lean_dec_ref(v_a_5981_);
return v_res_5986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_5998_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_5999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5999_, 0, v_00_u03b1_5992_);
v___x_6000_ = lean_box(0);
v___x_6001_ = lean_unsigned_to_nat(2u);
v___x_6002_ = lean_mk_empty_array_with_capacity(v___x_6001_);
v___x_6003_ = lean_array_push(v___x_6002_, v___x_5999_);
v___x_6004_ = lean_array_push(v___x_6003_, v___x_6000_);
v___x_6005_ = l_Lean_Meta_mkAppOptM(v___x_5998_, v___x_6004_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_);
return v___x_6005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_){
_start:
{
lean_object* v_res_6012_; 
v_res_6012_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6006_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
lean_dec(v_a_6010_);
lean_dec_ref(v_a_6009_);
lean_dec(v_a_6008_);
lean_dec_ref(v_a_6007_);
return v_res_6012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_){
_start:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; 
v___x_6022_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6023_ = lean_unsigned_to_nat(1u);
v___x_6024_ = lean_mk_empty_array_with_capacity(v___x_6023_);
v___x_6025_ = lean_array_push(v___x_6024_, v_h_6016_);
v___x_6026_ = l_Lean_Meta_mkAppM(v___x_6022_, v___x_6025_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_);
return v___x_6026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_){
_start:
{
lean_object* v_res_6033_; 
v_res_6033_ = l_Lean_Meta_mkFunExt(v_h_6027_, v_a_6028_, v_a_6029_, v_a_6030_, v_a_6031_);
lean_dec(v_a_6031_);
lean_dec_ref(v_a_6030_);
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6028_);
return v_res_6033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6037_, lean_object* v_a_6038_, lean_object* v_a_6039_, lean_object* v_a_6040_, lean_object* v_a_6041_){
_start:
{
lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v___x_6043_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6044_ = lean_unsigned_to_nat(1u);
v___x_6045_ = lean_mk_empty_array_with_capacity(v___x_6044_);
v___x_6046_ = lean_array_push(v___x_6045_, v_h_6037_);
v___x_6047_ = l_Lean_Meta_mkAppM(v___x_6043_, v___x_6046_, v_a_6038_, v_a_6039_, v_a_6040_, v_a_6041_);
return v___x_6047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_){
_start:
{
lean_object* v_res_6054_; 
v_res_6054_ = l_Lean_Meta_mkPropExt(v_h_6048_, v_a_6049_, v_a_6050_, v_a_6051_, v_a_6052_);
lean_dec(v_a_6052_);
lean_dec_ref(v_a_6051_);
lean_dec(v_a_6050_);
lean_dec_ref(v_a_6049_);
return v_res_6054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6058_, lean_object* v_h_u2082_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_){
_start:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
v___x_6065_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6066_ = lean_unsigned_to_nat(2u);
v___x_6067_ = lean_mk_empty_array_with_capacity(v___x_6066_);
v___x_6068_ = lean_array_push(v___x_6067_, v_h_u2081_6058_);
v___x_6069_ = lean_array_push(v___x_6068_, v_h_u2082_6059_);
v___x_6070_ = l_Lean_Meta_mkAppM(v___x_6065_, v___x_6069_, v_a_6060_, v_a_6061_, v_a_6062_, v_a_6063_);
return v___x_6070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6071_, lean_object* v_h_u2082_6072_, lean_object* v_a_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_, lean_object* v_a_6077_){
_start:
{
lean_object* v_res_6078_; 
v_res_6078_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6071_, v_h_u2082_6072_, v_a_6073_, v_a_6074_, v_a_6075_, v_a_6076_);
lean_dec(v_a_6076_);
lean_dec_ref(v_a_6075_);
lean_dec(v_a_6074_);
lean_dec_ref(v_a_6073_);
return v_res_6078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6082_, lean_object* v_h_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_){
_start:
{
lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; 
v___x_6089_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6090_ = lean_unsigned_to_nat(2u);
v___x_6091_ = lean_mk_empty_array_with_capacity(v___x_6090_);
v___x_6092_ = lean_array_push(v___x_6091_, v_b_6082_);
v___x_6093_ = lean_array_push(v___x_6092_, v_h_6083_);
v___x_6094_ = l_Lean_Meta_mkAppM(v___x_6089_, v___x_6093_, v_a_6084_, v_a_6085_, v_a_6086_, v_a_6087_);
return v___x_6094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6095_, lean_object* v_h_6096_, lean_object* v_a_6097_, lean_object* v_a_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_, lean_object* v_a_6101_){
_start:
{
lean_object* v_res_6102_; 
v_res_6102_ = l_Lean_Meta_mkLetValCongr(v_b_6095_, v_h_6096_, v_a_6097_, v_a_6098_, v_a_6099_, v_a_6100_);
lean_dec(v_a_6100_);
lean_dec_ref(v_a_6099_);
lean_dec(v_a_6098_);
lean_dec_ref(v_a_6097_);
return v_res_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6106_, lean_object* v_h_6107_, lean_object* v_a_6108_, lean_object* v_a_6109_, lean_object* v_a_6110_, lean_object* v_a_6111_){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; 
v___x_6113_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6114_ = lean_unsigned_to_nat(2u);
v___x_6115_ = lean_mk_empty_array_with_capacity(v___x_6114_);
v___x_6116_ = lean_array_push(v___x_6115_, v_a_6106_);
v___x_6117_ = lean_array_push(v___x_6116_, v_h_6107_);
v___x_6118_ = l_Lean_Meta_mkAppM(v___x_6113_, v___x_6117_, v_a_6108_, v_a_6109_, v_a_6110_, v_a_6111_);
return v___x_6118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6119_, lean_object* v_h_6120_, lean_object* v_a_6121_, lean_object* v_a_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_, lean_object* v_a_6125_){
_start:
{
lean_object* v_res_6126_; 
v_res_6126_ = l_Lean_Meta_mkLetBodyCongr(v_a_6119_, v_h_6120_, v_a_6121_, v_a_6122_, v_a_6123_, v_a_6124_);
lean_dec(v_a_6124_);
lean_dec_ref(v_a_6123_);
lean_dec(v_a_6122_);
lean_dec_ref(v_a_6121_);
return v_res_6126_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; 
v___x_6130_ = lean_box(0);
v___x_6131_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6132_ = l_Lean_mkConst(v___x_6131_, v___x_6130_);
return v___x_6132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6136_, lean_object* v_h_6137_){
_start:
{
lean_object* v___x_6141_; uint8_t v___x_6142_; 
lean_inc_ref(v_h_6137_);
v___x_6141_ = l_Lean_Expr_cleanupAnnotations(v_h_6137_);
v___x_6142_ = l_Lean_Expr_isApp(v___x_6141_);
if (v___x_6142_ == 0)
{
lean_dec_ref(v___x_6141_);
goto v___jp_6138_;
}
else
{
lean_object* v_arg_6143_; lean_object* v___x_6144_; uint8_t v___x_6145_; 
v_arg_6143_ = lean_ctor_get(v___x_6141_, 1);
lean_inc_ref(v_arg_6143_);
v___x_6144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6141_);
v___x_6145_ = l_Lean_Expr_isApp(v___x_6144_);
if (v___x_6145_ == 0)
{
lean_dec_ref(v___x_6144_);
lean_dec_ref(v_arg_6143_);
goto v___jp_6138_;
}
else
{
lean_object* v___x_6146_; lean_object* v___x_6147_; uint8_t v___x_6148_; 
v___x_6146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6144_);
v___x_6147_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6148_ = l_Lean_Expr_isConstOf(v___x_6146_, v___x_6147_);
lean_dec_ref(v___x_6146_);
if (v___x_6148_ == 0)
{
lean_dec_ref(v_arg_6143_);
goto v___jp_6138_;
}
else
{
lean_dec_ref(v_h_6137_);
lean_dec_ref(v_p_6136_);
return v_arg_6143_;
}
}
}
v___jp_6138_:
{
lean_object* v___x_6139_; lean_object* v___x_6140_; 
v___x_6139_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6140_ = l_Lean_mkAppB(v___x_6139_, v_p_6136_, v_h_6137_);
return v___x_6140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6149_, lean_object* v_a_6150_, lean_object* v_a_6151_, lean_object* v_a_6152_, lean_object* v_a_6153_){
_start:
{
lean_object* v___y_6156_; lean_object* v___y_6157_; lean_object* v___y_6158_; lean_object* v___y_6159_; lean_object* v___x_6165_; 
lean_inc_ref(v_h_6149_);
v___x_6165_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6149_, v_a_6151_);
if (lean_obj_tag(v___x_6165_) == 0)
{
lean_object* v_a_6166_; lean_object* v___x_6168_; uint8_t v_isShared_6169_; uint8_t v_isSharedCheck_6181_; 
v_a_6166_ = lean_ctor_get(v___x_6165_, 0);
v_isSharedCheck_6181_ = !lean_is_exclusive(v___x_6165_);
if (v_isSharedCheck_6181_ == 0)
{
v___x_6168_ = v___x_6165_;
v_isShared_6169_ = v_isSharedCheck_6181_;
goto v_resetjp_6167_;
}
else
{
lean_inc(v_a_6166_);
lean_dec(v___x_6165_);
v___x_6168_ = lean_box(0);
v_isShared_6169_ = v_isSharedCheck_6181_;
goto v_resetjp_6167_;
}
v_resetjp_6167_:
{
lean_object* v___x_6170_; uint8_t v___x_6171_; 
v___x_6170_ = l_Lean_Expr_cleanupAnnotations(v_a_6166_);
v___x_6171_ = l_Lean_Expr_isApp(v___x_6170_);
if (v___x_6171_ == 0)
{
lean_dec_ref(v___x_6170_);
lean_del_object(v___x_6168_);
v___y_6156_ = v_a_6150_;
v___y_6157_ = v_a_6151_;
v___y_6158_ = v_a_6152_;
v___y_6159_ = v_a_6153_;
goto v___jp_6155_;
}
else
{
lean_object* v_arg_6172_; lean_object* v___x_6173_; uint8_t v___x_6174_; 
v_arg_6172_ = lean_ctor_get(v___x_6170_, 1);
lean_inc_ref(v_arg_6172_);
v___x_6173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6170_);
v___x_6174_ = l_Lean_Expr_isApp(v___x_6173_);
if (v___x_6174_ == 0)
{
lean_dec_ref(v___x_6173_);
lean_dec_ref(v_arg_6172_);
lean_del_object(v___x_6168_);
v___y_6156_ = v_a_6150_;
v___y_6157_ = v_a_6151_;
v___y_6158_ = v_a_6152_;
v___y_6159_ = v_a_6153_;
goto v___jp_6155_;
}
else
{
lean_object* v___x_6175_; lean_object* v___x_6176_; uint8_t v___x_6177_; 
v___x_6175_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6173_);
v___x_6176_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6177_ = l_Lean_Expr_isConstOf(v___x_6175_, v___x_6176_);
lean_dec_ref(v___x_6175_);
if (v___x_6177_ == 0)
{
lean_dec_ref(v_arg_6172_);
lean_del_object(v___x_6168_);
v___y_6156_ = v_a_6150_;
v___y_6157_ = v_a_6151_;
v___y_6158_ = v_a_6152_;
v___y_6159_ = v_a_6153_;
goto v___jp_6155_;
}
else
{
lean_object* v___x_6179_; 
lean_dec_ref(v_h_6149_);
if (v_isShared_6169_ == 0)
{
lean_ctor_set(v___x_6168_, 0, v_arg_6172_);
v___x_6179_ = v___x_6168_;
goto v_reusejp_6178_;
}
else
{
lean_object* v_reuseFailAlloc_6180_; 
v_reuseFailAlloc_6180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_arg_6172_);
v___x_6179_ = v_reuseFailAlloc_6180_;
goto v_reusejp_6178_;
}
v_reusejp_6178_:
{
return v___x_6179_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6149_);
return v___x_6165_;
}
v___jp_6155_:
{
lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; 
v___x_6160_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6161_ = lean_unsigned_to_nat(1u);
v___x_6162_ = lean_mk_empty_array_with_capacity(v___x_6161_);
v___x_6163_ = lean_array_push(v___x_6162_, v_h_6149_);
v___x_6164_ = l_Lean_Meta_mkAppM(v___x_6160_, v___x_6163_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_);
return v___x_6164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6182_, lean_object* v_a_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_, lean_object* v_a_6187_){
_start:
{
lean_object* v_res_6188_; 
v_res_6188_ = l_Lean_Meta_mkOfEqFalse(v_h_6182_, v_a_6183_, v_a_6184_, v_a_6185_, v_a_6186_);
lean_dec(v_a_6186_);
lean_dec_ref(v_a_6185_);
lean_dec(v_a_6184_);
lean_dec_ref(v_a_6183_);
return v_res_6188_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; 
v___x_6192_ = lean_box(0);
v___x_6193_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6194_ = l_Lean_mkConst(v___x_6193_, v___x_6192_);
return v___x_6194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6198_, lean_object* v_h_6199_){
_start:
{
lean_object* v___x_6203_; uint8_t v___x_6204_; 
lean_inc_ref(v_h_6199_);
v___x_6203_ = l_Lean_Expr_cleanupAnnotations(v_h_6199_);
v___x_6204_ = l_Lean_Expr_isApp(v___x_6203_);
if (v___x_6204_ == 0)
{
lean_dec_ref(v___x_6203_);
goto v___jp_6200_;
}
else
{
lean_object* v_arg_6205_; lean_object* v___x_6206_; uint8_t v___x_6207_; 
v_arg_6205_ = lean_ctor_get(v___x_6203_, 1);
lean_inc_ref(v_arg_6205_);
v___x_6206_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6203_);
v___x_6207_ = l_Lean_Expr_isApp(v___x_6206_);
if (v___x_6207_ == 0)
{
lean_dec_ref(v___x_6206_);
lean_dec_ref(v_arg_6205_);
goto v___jp_6200_;
}
else
{
lean_object* v___x_6208_; lean_object* v___x_6209_; uint8_t v___x_6210_; 
v___x_6208_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6206_);
v___x_6209_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6210_ = l_Lean_Expr_isConstOf(v___x_6208_, v___x_6209_);
lean_dec_ref(v___x_6208_);
if (v___x_6210_ == 0)
{
lean_dec_ref(v_arg_6205_);
goto v___jp_6200_;
}
else
{
lean_dec_ref(v_h_6199_);
lean_dec_ref(v_p_6198_);
return v_arg_6205_;
}
}
}
v___jp_6200_:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6201_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6202_ = l_Lean_mkAppB(v___x_6201_, v_p_6198_, v_h_6199_);
return v___x_6202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6211_, lean_object* v_a_6212_, lean_object* v_a_6213_, lean_object* v_a_6214_, lean_object* v_a_6215_){
_start:
{
lean_object* v___y_6218_; lean_object* v___y_6219_; lean_object* v___y_6220_; lean_object* v___y_6221_; lean_object* v___x_6227_; 
lean_inc_ref(v_h_6211_);
v___x_6227_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6211_, v_a_6213_);
if (lean_obj_tag(v___x_6227_) == 0)
{
lean_object* v_a_6228_; lean_object* v___x_6230_; uint8_t v_isShared_6231_; uint8_t v_isSharedCheck_6243_; 
v_a_6228_ = lean_ctor_get(v___x_6227_, 0);
v_isSharedCheck_6243_ = !lean_is_exclusive(v___x_6227_);
if (v_isSharedCheck_6243_ == 0)
{
v___x_6230_ = v___x_6227_;
v_isShared_6231_ = v_isSharedCheck_6243_;
goto v_resetjp_6229_;
}
else
{
lean_inc(v_a_6228_);
lean_dec(v___x_6227_);
v___x_6230_ = lean_box(0);
v_isShared_6231_ = v_isSharedCheck_6243_;
goto v_resetjp_6229_;
}
v_resetjp_6229_:
{
lean_object* v___x_6232_; uint8_t v___x_6233_; 
v___x_6232_ = l_Lean_Expr_cleanupAnnotations(v_a_6228_);
v___x_6233_ = l_Lean_Expr_isApp(v___x_6232_);
if (v___x_6233_ == 0)
{
lean_dec_ref(v___x_6232_);
lean_del_object(v___x_6230_);
v___y_6218_ = v_a_6212_;
v___y_6219_ = v_a_6213_;
v___y_6220_ = v_a_6214_;
v___y_6221_ = v_a_6215_;
goto v___jp_6217_;
}
else
{
lean_object* v_arg_6234_; lean_object* v___x_6235_; uint8_t v___x_6236_; 
v_arg_6234_ = lean_ctor_get(v___x_6232_, 1);
lean_inc_ref(v_arg_6234_);
v___x_6235_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6232_);
v___x_6236_ = l_Lean_Expr_isApp(v___x_6235_);
if (v___x_6236_ == 0)
{
lean_dec_ref(v___x_6235_);
lean_dec_ref(v_arg_6234_);
lean_del_object(v___x_6230_);
v___y_6218_ = v_a_6212_;
v___y_6219_ = v_a_6213_;
v___y_6220_ = v_a_6214_;
v___y_6221_ = v_a_6215_;
goto v___jp_6217_;
}
else
{
lean_object* v___x_6237_; lean_object* v___x_6238_; uint8_t v___x_6239_; 
v___x_6237_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6235_);
v___x_6238_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6239_ = l_Lean_Expr_isConstOf(v___x_6237_, v___x_6238_);
lean_dec_ref(v___x_6237_);
if (v___x_6239_ == 0)
{
lean_dec_ref(v_arg_6234_);
lean_del_object(v___x_6230_);
v___y_6218_ = v_a_6212_;
v___y_6219_ = v_a_6213_;
v___y_6220_ = v_a_6214_;
v___y_6221_ = v_a_6215_;
goto v___jp_6217_;
}
else
{
lean_object* v___x_6241_; 
lean_dec_ref(v_h_6211_);
if (v_isShared_6231_ == 0)
{
lean_ctor_set(v___x_6230_, 0, v_arg_6234_);
v___x_6241_ = v___x_6230_;
goto v_reusejp_6240_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_arg_6234_);
v___x_6241_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6240_;
}
v_reusejp_6240_:
{
return v___x_6241_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6211_);
return v___x_6227_;
}
v___jp_6217_:
{
lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; 
v___x_6222_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6223_ = lean_unsigned_to_nat(1u);
v___x_6224_ = lean_mk_empty_array_with_capacity(v___x_6223_);
v___x_6225_ = lean_array_push(v___x_6224_, v_h_6211_);
v___x_6226_ = l_Lean_Meta_mkAppM(v___x_6222_, v___x_6225_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_);
return v___x_6226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6244_, lean_object* v_a_6245_, lean_object* v_a_6246_, lean_object* v_a_6247_, lean_object* v_a_6248_, lean_object* v_a_6249_){
_start:
{
lean_object* v_res_6250_; 
v_res_6250_ = l_Lean_Meta_mkOfEqTrue(v_h_6244_, v_a_6245_, v_a_6246_, v_a_6247_, v_a_6248_);
lean_dec(v_a_6248_);
lean_dec_ref(v_a_6247_);
lean_dec(v_a_6246_);
lean_dec_ref(v_a_6245_);
return v_res_6250_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; 
v___x_6251_ = lean_box(0);
v___x_6252_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6253_ = l_Lean_mkConst(v___x_6252_, v___x_6251_);
return v___x_6253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6254_, lean_object* v_h_6255_){
_start:
{
lean_object* v___x_6259_; uint8_t v___x_6260_; 
lean_inc_ref(v_h_6255_);
v___x_6259_ = l_Lean_Expr_cleanupAnnotations(v_h_6255_);
v___x_6260_ = l_Lean_Expr_isApp(v___x_6259_);
if (v___x_6260_ == 0)
{
lean_dec_ref(v___x_6259_);
goto v___jp_6256_;
}
else
{
lean_object* v_arg_6261_; lean_object* v___x_6262_; uint8_t v___x_6263_; 
v_arg_6261_ = lean_ctor_get(v___x_6259_, 1);
lean_inc_ref(v_arg_6261_);
v___x_6262_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6259_);
v___x_6263_ = l_Lean_Expr_isApp(v___x_6262_);
if (v___x_6263_ == 0)
{
lean_dec_ref(v___x_6262_);
lean_dec_ref(v_arg_6261_);
goto v___jp_6256_;
}
else
{
lean_object* v___x_6264_; lean_object* v___x_6265_; uint8_t v___x_6266_; 
v___x_6264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6262_);
v___x_6265_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6266_ = l_Lean_Expr_isConstOf(v___x_6264_, v___x_6265_);
lean_dec_ref(v___x_6264_);
if (v___x_6266_ == 0)
{
lean_dec_ref(v_arg_6261_);
goto v___jp_6256_;
}
else
{
lean_dec_ref(v_h_6255_);
lean_dec_ref(v_p_6254_);
return v_arg_6261_;
}
}
}
v___jp_6256_:
{
lean_object* v___x_6257_; lean_object* v___x_6258_; 
v___x_6257_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6258_ = l_Lean_mkAppB(v___x_6257_, v_p_6254_, v_h_6255_);
return v___x_6258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6267_, lean_object* v_a_6268_, lean_object* v_a_6269_, lean_object* v_a_6270_, lean_object* v_a_6271_){
_start:
{
lean_object* v___y_6274_; lean_object* v___y_6275_; lean_object* v___y_6276_; lean_object* v___y_6277_; lean_object* v___x_6289_; 
lean_inc_ref(v_h_6267_);
v___x_6289_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6267_, v_a_6269_);
if (lean_obj_tag(v___x_6289_) == 0)
{
lean_object* v_a_6290_; lean_object* v___x_6292_; uint8_t v_isShared_6293_; uint8_t v_isSharedCheck_6305_; 
v_a_6290_ = lean_ctor_get(v___x_6289_, 0);
v_isSharedCheck_6305_ = !lean_is_exclusive(v___x_6289_);
if (v_isSharedCheck_6305_ == 0)
{
v___x_6292_ = v___x_6289_;
v_isShared_6293_ = v_isSharedCheck_6305_;
goto v_resetjp_6291_;
}
else
{
lean_inc(v_a_6290_);
lean_dec(v___x_6289_);
v___x_6292_ = lean_box(0);
v_isShared_6293_ = v_isSharedCheck_6305_;
goto v_resetjp_6291_;
}
v_resetjp_6291_:
{
lean_object* v___x_6294_; uint8_t v___x_6295_; 
v___x_6294_ = l_Lean_Expr_cleanupAnnotations(v_a_6290_);
v___x_6295_ = l_Lean_Expr_isApp(v___x_6294_);
if (v___x_6295_ == 0)
{
lean_dec_ref(v___x_6294_);
lean_del_object(v___x_6292_);
v___y_6274_ = v_a_6268_;
v___y_6275_ = v_a_6269_;
v___y_6276_ = v_a_6270_;
v___y_6277_ = v_a_6271_;
goto v___jp_6273_;
}
else
{
lean_object* v_arg_6296_; lean_object* v___x_6297_; uint8_t v___x_6298_; 
v_arg_6296_ = lean_ctor_get(v___x_6294_, 1);
lean_inc_ref(v_arg_6296_);
v___x_6297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6294_);
v___x_6298_ = l_Lean_Expr_isApp(v___x_6297_);
if (v___x_6298_ == 0)
{
lean_dec_ref(v___x_6297_);
lean_dec_ref(v_arg_6296_);
lean_del_object(v___x_6292_);
v___y_6274_ = v_a_6268_;
v___y_6275_ = v_a_6269_;
v___y_6276_ = v_a_6270_;
v___y_6277_ = v_a_6271_;
goto v___jp_6273_;
}
else
{
lean_object* v___x_6299_; lean_object* v___x_6300_; uint8_t v___x_6301_; 
v___x_6299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6297_);
v___x_6300_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6301_ = l_Lean_Expr_isConstOf(v___x_6299_, v___x_6300_);
lean_dec_ref(v___x_6299_);
if (v___x_6301_ == 0)
{
lean_dec_ref(v_arg_6296_);
lean_del_object(v___x_6292_);
v___y_6274_ = v_a_6268_;
v___y_6275_ = v_a_6269_;
v___y_6276_ = v_a_6270_;
v___y_6277_ = v_a_6271_;
goto v___jp_6273_;
}
else
{
lean_object* v___x_6303_; 
lean_dec_ref(v_h_6267_);
if (v_isShared_6293_ == 0)
{
lean_ctor_set(v___x_6292_, 0, v_arg_6296_);
v___x_6303_ = v___x_6292_;
goto v_reusejp_6302_;
}
else
{
lean_object* v_reuseFailAlloc_6304_; 
v_reuseFailAlloc_6304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6304_, 0, v_arg_6296_);
v___x_6303_ = v_reuseFailAlloc_6304_;
goto v_reusejp_6302_;
}
v_reusejp_6302_:
{
return v___x_6303_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6267_);
return v___x_6289_;
}
v___jp_6273_:
{
lean_object* v___x_6278_; 
lean_inc(v___y_6277_);
lean_inc_ref(v___y_6276_);
lean_inc(v___y_6275_);
lean_inc_ref(v___y_6274_);
lean_inc_ref(v_h_6267_);
v___x_6278_ = lean_infer_type(v_h_6267_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_);
if (lean_obj_tag(v___x_6278_) == 0)
{
lean_object* v_a_6279_; lean_object* v___x_6281_; uint8_t v_isShared_6282_; uint8_t v_isSharedCheck_6288_; 
v_a_6279_ = lean_ctor_get(v___x_6278_, 0);
v_isSharedCheck_6288_ = !lean_is_exclusive(v___x_6278_);
if (v_isSharedCheck_6288_ == 0)
{
v___x_6281_ = v___x_6278_;
v_isShared_6282_ = v_isSharedCheck_6288_;
goto v_resetjp_6280_;
}
else
{
lean_inc(v_a_6279_);
lean_dec(v___x_6278_);
v___x_6281_ = lean_box(0);
v_isShared_6282_ = v_isSharedCheck_6288_;
goto v_resetjp_6280_;
}
v_resetjp_6280_:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6286_; 
v___x_6283_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6284_ = l_Lean_mkAppB(v___x_6283_, v_a_6279_, v_h_6267_);
if (v_isShared_6282_ == 0)
{
lean_ctor_set(v___x_6281_, 0, v___x_6284_);
v___x_6286_ = v___x_6281_;
goto v_reusejp_6285_;
}
else
{
lean_object* v_reuseFailAlloc_6287_; 
v_reuseFailAlloc_6287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6287_, 0, v___x_6284_);
v___x_6286_ = v_reuseFailAlloc_6287_;
goto v_reusejp_6285_;
}
v_reusejp_6285_:
{
return v___x_6286_;
}
}
}
else
{
lean_dec_ref(v_h_6267_);
return v___x_6278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6306_, lean_object* v_a_6307_, lean_object* v_a_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_, lean_object* v_a_6311_){
_start:
{
lean_object* v_res_6312_; 
v_res_6312_ = l_Lean_Meta_mkEqTrue(v_h_6306_, v_a_6307_, v_a_6308_, v_a_6309_, v_a_6310_);
lean_dec(v_a_6310_);
lean_dec_ref(v_a_6309_);
lean_dec(v_a_6308_);
lean_dec_ref(v_a_6307_);
return v_res_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_){
_start:
{
lean_object* v___y_6320_; lean_object* v___y_6321_; lean_object* v___y_6322_; lean_object* v___y_6323_; lean_object* v___x_6329_; uint8_t v___x_6330_; 
lean_inc_ref(v_h_6313_);
v___x_6329_ = l_Lean_Expr_cleanupAnnotations(v_h_6313_);
v___x_6330_ = l_Lean_Expr_isApp(v___x_6329_);
if (v___x_6330_ == 0)
{
lean_dec_ref(v___x_6329_);
v___y_6320_ = v_a_6314_;
v___y_6321_ = v_a_6315_;
v___y_6322_ = v_a_6316_;
v___y_6323_ = v_a_6317_;
goto v___jp_6319_;
}
else
{
lean_object* v_arg_6331_; lean_object* v___x_6332_; uint8_t v___x_6333_; 
v_arg_6331_ = lean_ctor_get(v___x_6329_, 1);
lean_inc_ref(v_arg_6331_);
v___x_6332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6329_);
v___x_6333_ = l_Lean_Expr_isApp(v___x_6332_);
if (v___x_6333_ == 0)
{
lean_dec_ref(v___x_6332_);
lean_dec_ref(v_arg_6331_);
v___y_6320_ = v_a_6314_;
v___y_6321_ = v_a_6315_;
v___y_6322_ = v_a_6316_;
v___y_6323_ = v_a_6317_;
goto v___jp_6319_;
}
else
{
lean_object* v___x_6334_; lean_object* v___x_6335_; uint8_t v___x_6336_; 
v___x_6334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6332_);
v___x_6335_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6336_ = l_Lean_Expr_isConstOf(v___x_6334_, v___x_6335_);
lean_dec_ref(v___x_6334_);
if (v___x_6336_ == 0)
{
lean_dec_ref(v_arg_6331_);
v___y_6320_ = v_a_6314_;
v___y_6321_ = v_a_6315_;
v___y_6322_ = v_a_6316_;
v___y_6323_ = v_a_6317_;
goto v___jp_6319_;
}
else
{
lean_object* v___x_6337_; 
lean_dec_ref(v_h_6313_);
v___x_6337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6337_, 0, v_arg_6331_);
return v___x_6337_;
}
}
}
v___jp_6319_:
{
lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6324_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6325_ = lean_unsigned_to_nat(1u);
v___x_6326_ = lean_mk_empty_array_with_capacity(v___x_6325_);
v___x_6327_ = lean_array_push(v___x_6326_, v_h_6313_);
v___x_6328_ = l_Lean_Meta_mkAppM(v___x_6324_, v___x_6327_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
return v___x_6328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6338_, lean_object* v_a_6339_, lean_object* v_a_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_){
_start:
{
lean_object* v_res_6344_; 
v_res_6344_ = l_Lean_Meta_mkEqFalse(v_h_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_);
lean_dec(v_a_6342_);
lean_dec_ref(v_a_6341_);
lean_dec(v_a_6340_);
lean_dec_ref(v_a_6339_);
return v_res_6344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6348_, lean_object* v_a_6349_, lean_object* v_a_6350_, lean_object* v_a_6351_, lean_object* v_a_6352_){
_start:
{
lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; 
v___x_6354_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6355_ = lean_unsigned_to_nat(1u);
v___x_6356_ = lean_mk_empty_array_with_capacity(v___x_6355_);
v___x_6357_ = lean_array_push(v___x_6356_, v_h_6348_);
v___x_6358_ = l_Lean_Meta_mkAppM(v___x_6354_, v___x_6357_, v_a_6349_, v_a_6350_, v_a_6351_, v_a_6352_);
return v___x_6358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6359_, lean_object* v_a_6360_, lean_object* v_a_6361_, lean_object* v_a_6362_, lean_object* v_a_6363_, lean_object* v_a_6364_){
_start:
{
lean_object* v_res_6365_; 
v_res_6365_ = l_Lean_Meta_mkEqFalse_x27(v_h_6359_, v_a_6360_, v_a_6361_, v_a_6362_, v_a_6363_);
lean_dec(v_a_6363_);
lean_dec_ref(v_a_6362_);
lean_dec(v_a_6361_);
lean_dec_ref(v_a_6360_);
return v_res_6365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6369_, lean_object* v_h_u2082_6370_, lean_object* v_a_6371_, lean_object* v_a_6372_, lean_object* v_a_6373_, lean_object* v_a_6374_){
_start:
{
lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; 
v___x_6376_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6377_ = lean_unsigned_to_nat(2u);
v___x_6378_ = lean_mk_empty_array_with_capacity(v___x_6377_);
v___x_6379_ = lean_array_push(v___x_6378_, v_h_u2081_6369_);
v___x_6380_ = lean_array_push(v___x_6379_, v_h_u2082_6370_);
v___x_6381_ = l_Lean_Meta_mkAppM(v___x_6376_, v___x_6380_, v_a_6371_, v_a_6372_, v_a_6373_, v_a_6374_);
return v___x_6381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6382_, lean_object* v_h_u2082_6383_, lean_object* v_a_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_){
_start:
{
lean_object* v_res_6389_; 
v_res_6389_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6382_, v_h_u2082_6383_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
lean_dec(v_a_6387_);
lean_dec_ref(v_a_6386_);
lean_dec(v_a_6385_);
lean_dec_ref(v_a_6384_);
return v_res_6389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6393_, lean_object* v_h_u2082_6394_, lean_object* v_a_6395_, lean_object* v_a_6396_, lean_object* v_a_6397_, lean_object* v_a_6398_){
_start:
{
lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6400_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6401_ = lean_unsigned_to_nat(2u);
v___x_6402_ = lean_mk_empty_array_with_capacity(v___x_6401_);
v___x_6403_ = lean_array_push(v___x_6402_, v_h_u2081_6393_);
v___x_6404_ = lean_array_push(v___x_6403_, v_h_u2082_6394_);
v___x_6405_ = l_Lean_Meta_mkAppM(v___x_6400_, v___x_6404_, v_a_6395_, v_a_6396_, v_a_6397_, v_a_6398_);
return v___x_6405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6406_, lean_object* v_h_u2082_6407_, lean_object* v_a_6408_, lean_object* v_a_6409_, lean_object* v_a_6410_, lean_object* v_a_6411_, lean_object* v_a_6412_){
_start:
{
lean_object* v_res_6413_; 
v_res_6413_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6406_, v_h_u2082_6407_, v_a_6408_, v_a_6409_, v_a_6410_, v_a_6411_);
lean_dec(v_a_6411_);
lean_dec_ref(v_a_6410_);
lean_dec(v_a_6409_);
lean_dec_ref(v_a_6408_);
return v_res_6413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6417_, lean_object* v_h_u2082_6418_, lean_object* v_a_6419_, lean_object* v_a_6420_, lean_object* v_a_6421_, lean_object* v_a_6422_){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; 
v___x_6424_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6425_ = lean_unsigned_to_nat(2u);
v___x_6426_ = lean_mk_empty_array_with_capacity(v___x_6425_);
v___x_6427_ = lean_array_push(v___x_6426_, v_h_u2081_6417_);
v___x_6428_ = lean_array_push(v___x_6427_, v_h_u2082_6418_);
v___x_6429_ = l_Lean_Meta_mkAppM(v___x_6424_, v___x_6428_, v_a_6419_, v_a_6420_, v_a_6421_, v_a_6422_);
return v___x_6429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6430_, lean_object* v_h_u2082_6431_, lean_object* v_a_6432_, lean_object* v_a_6433_, lean_object* v_a_6434_, lean_object* v_a_6435_, lean_object* v_a_6436_){
_start:
{
lean_object* v_res_6437_; 
v_res_6437_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6430_, v_h_u2082_6431_, v_a_6432_, v_a_6433_, v_a_6434_, v_a_6435_);
lean_dec(v_a_6435_);
lean_dec_ref(v_a_6434_);
lean_dec(v_a_6433_);
lean_dec_ref(v_a_6432_);
return v_res_6437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6441_, lean_object* v_a_6442_, lean_object* v_a_6443_, lean_object* v_a_6444_, lean_object* v_a_6445_){
_start:
{
lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6447_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6448_ = lean_unsigned_to_nat(1u);
v___x_6449_ = lean_mk_empty_array_with_capacity(v___x_6448_);
v___x_6450_ = lean_array_push(v___x_6449_, v_h_6441_);
v___x_6451_ = l_Lean_Meta_mkAppM(v___x_6447_, v___x_6450_, v_a_6442_, v_a_6443_, v_a_6444_, v_a_6445_);
return v___x_6451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6452_, lean_object* v_a_6453_, lean_object* v_a_6454_, lean_object* v_a_6455_, lean_object* v_a_6456_, lean_object* v_a_6457_){
_start:
{
lean_object* v_res_6458_; 
v_res_6458_ = l_Lean_Meta_mkForallCongr(v_h_6452_, v_a_6453_, v_a_6454_, v_a_6455_, v_a_6456_);
lean_dec(v_a_6456_);
lean_dec_ref(v_a_6455_);
lean_dec(v_a_6454_);
lean_dec_ref(v_a_6453_);
return v_res_6458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_){
_start:
{
lean_object* v___y_6469_; lean_object* v_a_6470_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; 
v___x_6475_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6476_ = lean_unsigned_to_nat(1u);
v___x_6477_ = lean_mk_empty_array_with_capacity(v___x_6476_);
v___x_6478_ = lean_array_push(v___x_6477_, v_m_6462_);
v___x_6479_ = l_Lean_Meta_mkAppM(v___x_6475_, v___x_6478_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_);
if (lean_obj_tag(v___x_6479_) == 0)
{
lean_object* v_a_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; 
v_a_6480_ = lean_ctor_get(v___x_6479_, 0);
lean_inc(v_a_6480_);
lean_dec_ref_known(v___x_6479_, 1);
v___x_6481_ = lean_box(0);
v___x_6482_ = l_Lean_Meta_trySynthInstance(v_a_6480_, v___x_6481_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_);
if (lean_obj_tag(v___x_6482_) == 0)
{
lean_object* v_a_6483_; lean_object* v___x_6485_; uint8_t v_isShared_6486_; uint8_t v_isSharedCheck_6501_; 
v_a_6483_ = lean_ctor_get(v___x_6482_, 0);
v_isSharedCheck_6501_ = !lean_is_exclusive(v___x_6482_);
if (v_isSharedCheck_6501_ == 0)
{
v___x_6485_ = v___x_6482_;
v_isShared_6486_ = v_isSharedCheck_6501_;
goto v_resetjp_6484_;
}
else
{
lean_inc(v_a_6483_);
lean_dec(v___x_6482_);
v___x_6485_ = lean_box(0);
v_isShared_6486_ = v_isSharedCheck_6501_;
goto v_resetjp_6484_;
}
v_resetjp_6484_:
{
if (lean_obj_tag(v_a_6483_) == 1)
{
lean_object* v_a_6487_; lean_object* v___x_6489_; uint8_t v_isShared_6490_; uint8_t v_isSharedCheck_6497_; 
v_a_6487_ = lean_ctor_get(v_a_6483_, 0);
v_isSharedCheck_6497_ = !lean_is_exclusive(v_a_6483_);
if (v_isSharedCheck_6497_ == 0)
{
v___x_6489_ = v_a_6483_;
v_isShared_6490_ = v_isSharedCheck_6497_;
goto v_resetjp_6488_;
}
else
{
lean_inc(v_a_6487_);
lean_dec(v_a_6483_);
v___x_6489_ = lean_box(0);
v_isShared_6490_ = v_isSharedCheck_6497_;
goto v_resetjp_6488_;
}
v_resetjp_6488_:
{
lean_object* v___x_6492_; 
if (v_isShared_6490_ == 0)
{
v___x_6492_ = v___x_6489_;
goto v_reusejp_6491_;
}
else
{
lean_object* v_reuseFailAlloc_6496_; 
v_reuseFailAlloc_6496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_a_6487_);
v___x_6492_ = v_reuseFailAlloc_6496_;
goto v_reusejp_6491_;
}
v_reusejp_6491_:
{
lean_object* v___x_6494_; 
if (v_isShared_6486_ == 0)
{
lean_ctor_set(v___x_6485_, 0, v___x_6492_);
v___x_6494_ = v___x_6485_;
goto v_reusejp_6493_;
}
else
{
lean_object* v_reuseFailAlloc_6495_; 
v_reuseFailAlloc_6495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6495_, 0, v___x_6492_);
v___x_6494_ = v_reuseFailAlloc_6495_;
goto v_reusejp_6493_;
}
v_reusejp_6493_:
{
return v___x_6494_;
}
}
}
}
else
{
lean_object* v___x_6499_; 
lean_dec(v_a_6483_);
if (v_isShared_6486_ == 0)
{
lean_ctor_set(v___x_6485_, 0, v___x_6481_);
v___x_6499_ = v___x_6485_;
goto v_reusejp_6498_;
}
else
{
lean_object* v_reuseFailAlloc_6500_; 
v_reuseFailAlloc_6500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6500_, 0, v___x_6481_);
v___x_6499_ = v_reuseFailAlloc_6500_;
goto v_reusejp_6498_;
}
v_reusejp_6498_:
{
return v___x_6499_;
}
}
}
}
else
{
lean_object* v_a_6502_; lean_object* v___x_6504_; uint8_t v_isShared_6505_; uint8_t v_isSharedCheck_6509_; 
v_a_6502_ = lean_ctor_get(v___x_6482_, 0);
v_isSharedCheck_6509_ = !lean_is_exclusive(v___x_6482_);
if (v_isSharedCheck_6509_ == 0)
{
v___x_6504_ = v___x_6482_;
v_isShared_6505_ = v_isSharedCheck_6509_;
goto v_resetjp_6503_;
}
else
{
lean_inc(v_a_6502_);
lean_dec(v___x_6482_);
v___x_6504_ = lean_box(0);
v_isShared_6505_ = v_isSharedCheck_6509_;
goto v_resetjp_6503_;
}
v_resetjp_6503_:
{
lean_object* v___x_6507_; 
lean_inc(v_a_6502_);
if (v_isShared_6505_ == 0)
{
v___x_6507_ = v___x_6504_;
goto v_reusejp_6506_;
}
else
{
lean_object* v_reuseFailAlloc_6508_; 
v_reuseFailAlloc_6508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6508_, 0, v_a_6502_);
v___x_6507_ = v_reuseFailAlloc_6508_;
goto v_reusejp_6506_;
}
v_reusejp_6506_:
{
v___y_6469_ = v___x_6507_;
v_a_6470_ = v_a_6502_;
goto v___jp_6468_;
}
}
}
}
else
{
lean_object* v_a_6510_; lean_object* v___x_6512_; uint8_t v_isShared_6513_; uint8_t v_isSharedCheck_6517_; 
v_a_6510_ = lean_ctor_get(v___x_6479_, 0);
v_isSharedCheck_6517_ = !lean_is_exclusive(v___x_6479_);
if (v_isSharedCheck_6517_ == 0)
{
v___x_6512_ = v___x_6479_;
v_isShared_6513_ = v_isSharedCheck_6517_;
goto v_resetjp_6511_;
}
else
{
lean_inc(v_a_6510_);
lean_dec(v___x_6479_);
v___x_6512_ = lean_box(0);
v_isShared_6513_ = v_isSharedCheck_6517_;
goto v_resetjp_6511_;
}
v_resetjp_6511_:
{
lean_object* v___x_6515_; 
lean_inc(v_a_6510_);
if (v_isShared_6513_ == 0)
{
v___x_6515_ = v___x_6512_;
goto v_reusejp_6514_;
}
else
{
lean_object* v_reuseFailAlloc_6516_; 
v_reuseFailAlloc_6516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6516_, 0, v_a_6510_);
v___x_6515_ = v_reuseFailAlloc_6516_;
goto v_reusejp_6514_;
}
v_reusejp_6514_:
{
v___y_6469_ = v___x_6515_;
v_a_6470_ = v_a_6510_;
goto v___jp_6468_;
}
}
}
v___jp_6468_:
{
uint8_t v___x_6471_; 
v___x_6471_ = l_Lean_Exception_isInterrupt(v_a_6470_);
if (v___x_6471_ == 0)
{
uint8_t v___x_6472_; 
v___x_6472_ = l_Lean_Exception_isRuntime(v_a_6470_);
if (v___x_6472_ == 0)
{
lean_object* v___x_6473_; lean_object* v___x_6474_; 
lean_dec_ref(v___y_6469_);
v___x_6473_ = lean_box(0);
v___x_6474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6474_, 0, v___x_6473_);
return v___x_6474_;
}
else
{
return v___y_6469_;
}
}
else
{
lean_dec_ref(v_a_6470_);
return v___y_6469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6518_, lean_object* v_a_6519_, lean_object* v_a_6520_, lean_object* v_a_6521_, lean_object* v_a_6522_, lean_object* v_a_6523_){
_start:
{
lean_object* v_res_6524_; 
v_res_6524_ = l_Lean_Meta_isMonad_x3f(v_m_6518_, v_a_6519_, v_a_6520_, v_a_6521_, v_a_6522_);
lean_dec(v_a_6522_);
lean_dec_ref(v_a_6521_);
lean_dec(v_a_6520_);
lean_dec_ref(v_a_6519_);
return v_res_6524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6532_, lean_object* v_n_6533_, lean_object* v_a_6534_, lean_object* v_a_6535_, lean_object* v_a_6536_, lean_object* v_a_6537_){
_start:
{
lean_object* v___x_6539_; 
lean_inc_ref(v_type_6532_);
v___x_6539_ = l_Lean_Meta_getDecLevel(v_type_6532_, v_a_6534_, v_a_6535_, v_a_6536_, v_a_6537_);
if (lean_obj_tag(v___x_6539_) == 0)
{
lean_object* v_a_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; 
v_a_6540_ = lean_ctor_get(v___x_6539_, 0);
lean_inc(v_a_6540_);
lean_dec_ref_known(v___x_6539_, 1);
v___x_6541_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6542_ = lean_box(0);
v___x_6543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6543_, 0, v_a_6540_);
lean_ctor_set(v___x_6543_, 1, v___x_6542_);
lean_inc_ref(v___x_6543_);
v___x_6544_ = l_Lean_mkConst(v___x_6541_, v___x_6543_);
v___x_6545_ = l_Lean_mkRawNatLit(v_n_6533_);
lean_inc_ref(v___x_6545_);
lean_inc_ref(v_type_6532_);
v___x_6546_ = l_Lean_mkAppB(v___x_6544_, v_type_6532_, v___x_6545_);
v___x_6547_ = lean_box(0);
v___x_6548_ = l_Lean_Meta_synthInstance(v___x_6546_, v___x_6547_, v_a_6534_, v_a_6535_, v_a_6536_, v_a_6537_);
if (lean_obj_tag(v___x_6548_) == 0)
{
lean_object* v_a_6549_; lean_object* v___x_6551_; uint8_t v_isShared_6552_; uint8_t v_isSharedCheck_6559_; 
v_a_6549_ = lean_ctor_get(v___x_6548_, 0);
v_isSharedCheck_6559_ = !lean_is_exclusive(v___x_6548_);
if (v_isSharedCheck_6559_ == 0)
{
v___x_6551_ = v___x_6548_;
v_isShared_6552_ = v_isSharedCheck_6559_;
goto v_resetjp_6550_;
}
else
{
lean_inc(v_a_6549_);
lean_dec(v___x_6548_);
v___x_6551_ = lean_box(0);
v_isShared_6552_ = v_isSharedCheck_6559_;
goto v_resetjp_6550_;
}
v_resetjp_6550_:
{
lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___x_6557_; 
v___x_6553_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6554_ = l_Lean_mkConst(v___x_6553_, v___x_6543_);
v___x_6555_ = l_Lean_mkApp3(v___x_6554_, v_type_6532_, v___x_6545_, v_a_6549_);
if (v_isShared_6552_ == 0)
{
lean_ctor_set(v___x_6551_, 0, v___x_6555_);
v___x_6557_ = v___x_6551_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6558_; 
v_reuseFailAlloc_6558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6558_, 0, v___x_6555_);
v___x_6557_ = v_reuseFailAlloc_6558_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
return v___x_6557_;
}
}
}
else
{
lean_dec_ref(v___x_6545_);
lean_dec_ref_known(v___x_6543_, 2);
lean_dec_ref(v_type_6532_);
return v___x_6548_;
}
}
else
{
lean_object* v_a_6560_; lean_object* v___x_6562_; uint8_t v_isShared_6563_; uint8_t v_isSharedCheck_6567_; 
lean_dec(v_n_6533_);
lean_dec_ref(v_type_6532_);
v_a_6560_ = lean_ctor_get(v___x_6539_, 0);
v_isSharedCheck_6567_ = !lean_is_exclusive(v___x_6539_);
if (v_isSharedCheck_6567_ == 0)
{
v___x_6562_ = v___x_6539_;
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
else
{
lean_inc(v_a_6560_);
lean_dec(v___x_6539_);
v___x_6562_ = lean_box(0);
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
v_resetjp_6561_:
{
lean_object* v___x_6565_; 
if (v_isShared_6563_ == 0)
{
v___x_6565_ = v___x_6562_;
goto v_reusejp_6564_;
}
else
{
lean_object* v_reuseFailAlloc_6566_; 
v_reuseFailAlloc_6566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6566_, 0, v_a_6560_);
v___x_6565_ = v_reuseFailAlloc_6566_;
goto v_reusejp_6564_;
}
v_reusejp_6564_:
{
return v___x_6565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6568_, lean_object* v_n_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_){
_start:
{
lean_object* v_res_6575_; 
v_res_6575_ = l_Lean_Meta_mkNumeral(v_type_6568_, v_n_6569_, v_a_6570_, v_a_6571_, v_a_6572_, v_a_6573_);
lean_dec(v_a_6573_);
lean_dec_ref(v_a_6572_);
lean_dec(v_a_6571_);
lean_dec_ref(v_a_6570_);
return v_res_6575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6576_, lean_object* v_opName_6577_, lean_object* v_a_6578_, lean_object* v_b_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_){
_start:
{
lean_object* v___x_6585_; 
lean_inc(v_a_6583_);
lean_inc_ref(v_a_6582_);
lean_inc(v_a_6581_);
lean_inc_ref(v_a_6580_);
lean_inc_ref(v_a_6578_);
v___x_6585_ = lean_infer_type(v_a_6578_, v_a_6580_, v_a_6581_, v_a_6582_, v_a_6583_);
if (lean_obj_tag(v___x_6585_) == 0)
{
lean_object* v_a_6586_; lean_object* v___x_6587_; 
v_a_6586_ = lean_ctor_get(v___x_6585_, 0);
lean_inc_n(v_a_6586_, 2);
lean_dec_ref_known(v___x_6585_, 1);
v___x_6587_ = l_Lean_Meta_getDecLevel(v_a_6586_, v_a_6580_, v_a_6581_, v_a_6582_, v_a_6583_);
if (lean_obj_tag(v___x_6587_) == 0)
{
lean_object* v_a_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; 
v_a_6588_ = lean_ctor_get(v___x_6587_, 0);
lean_inc_n(v_a_6588_, 3);
lean_dec_ref_known(v___x_6587_, 1);
v___x_6589_ = lean_box(0);
v___x_6590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6590_, 0, v_a_6588_);
lean_ctor_set(v___x_6590_, 1, v___x_6589_);
v___x_6591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6591_, 0, v_a_6588_);
lean_ctor_set(v___x_6591_, 1, v___x_6590_);
v___x_6592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6592_, 0, v_a_6588_);
lean_ctor_set(v___x_6592_, 1, v___x_6591_);
lean_inc_ref(v___x_6592_);
v___x_6593_ = l_Lean_mkConst(v_className_6576_, v___x_6592_);
lean_inc_n(v_a_6586_, 3);
v___x_6594_ = l_Lean_mkApp3(v___x_6593_, v_a_6586_, v_a_6586_, v_a_6586_);
v___x_6595_ = lean_box(0);
v___x_6596_ = l_Lean_Meta_synthInstance(v___x_6594_, v___x_6595_, v_a_6580_, v_a_6581_, v_a_6582_, v_a_6583_);
if (lean_obj_tag(v___x_6596_) == 0)
{
lean_object* v_a_6597_; lean_object* v___x_6599_; uint8_t v_isShared_6600_; uint8_t v_isSharedCheck_6606_; 
v_a_6597_ = lean_ctor_get(v___x_6596_, 0);
v_isSharedCheck_6606_ = !lean_is_exclusive(v___x_6596_);
if (v_isSharedCheck_6606_ == 0)
{
v___x_6599_ = v___x_6596_;
v_isShared_6600_ = v_isSharedCheck_6606_;
goto v_resetjp_6598_;
}
else
{
lean_inc(v_a_6597_);
lean_dec(v___x_6596_);
v___x_6599_ = lean_box(0);
v_isShared_6600_ = v_isSharedCheck_6606_;
goto v_resetjp_6598_;
}
v_resetjp_6598_:
{
lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6604_; 
v___x_6601_ = l_Lean_mkConst(v_opName_6577_, v___x_6592_);
lean_inc_n(v_a_6586_, 2);
v___x_6602_ = l_Lean_mkApp6(v___x_6601_, v_a_6586_, v_a_6586_, v_a_6586_, v_a_6597_, v_a_6578_, v_b_6579_);
if (v_isShared_6600_ == 0)
{
lean_ctor_set(v___x_6599_, 0, v___x_6602_);
v___x_6604_ = v___x_6599_;
goto v_reusejp_6603_;
}
else
{
lean_object* v_reuseFailAlloc_6605_; 
v_reuseFailAlloc_6605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6605_, 0, v___x_6602_);
v___x_6604_ = v_reuseFailAlloc_6605_;
goto v_reusejp_6603_;
}
v_reusejp_6603_:
{
return v___x_6604_;
}
}
}
else
{
lean_dec_ref_known(v___x_6592_, 2);
lean_dec(v_a_6586_);
lean_dec_ref(v_b_6579_);
lean_dec_ref(v_a_6578_);
lean_dec(v_opName_6577_);
return v___x_6596_;
}
}
else
{
lean_object* v_a_6607_; lean_object* v___x_6609_; uint8_t v_isShared_6610_; uint8_t v_isSharedCheck_6614_; 
lean_dec(v_a_6586_);
lean_dec_ref(v_b_6579_);
lean_dec_ref(v_a_6578_);
lean_dec(v_opName_6577_);
lean_dec(v_className_6576_);
v_a_6607_ = lean_ctor_get(v___x_6587_, 0);
v_isSharedCheck_6614_ = !lean_is_exclusive(v___x_6587_);
if (v_isSharedCheck_6614_ == 0)
{
v___x_6609_ = v___x_6587_;
v_isShared_6610_ = v_isSharedCheck_6614_;
goto v_resetjp_6608_;
}
else
{
lean_inc(v_a_6607_);
lean_dec(v___x_6587_);
v___x_6609_ = lean_box(0);
v_isShared_6610_ = v_isSharedCheck_6614_;
goto v_resetjp_6608_;
}
v_resetjp_6608_:
{
lean_object* v___x_6612_; 
if (v_isShared_6610_ == 0)
{
v___x_6612_ = v___x_6609_;
goto v_reusejp_6611_;
}
else
{
lean_object* v_reuseFailAlloc_6613_; 
v_reuseFailAlloc_6613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6613_, 0, v_a_6607_);
v___x_6612_ = v_reuseFailAlloc_6613_;
goto v_reusejp_6611_;
}
v_reusejp_6611_:
{
return v___x_6612_;
}
}
}
}
else
{
lean_dec_ref(v_b_6579_);
lean_dec_ref(v_a_6578_);
lean_dec(v_opName_6577_);
lean_dec(v_className_6576_);
return v___x_6585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6615_, lean_object* v_opName_6616_, lean_object* v_a_6617_, lean_object* v_b_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_){
_start:
{
lean_object* v_res_6624_; 
v_res_6624_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6615_, v_opName_6616_, v_a_6617_, v_b_6618_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_);
lean_dec(v_a_6622_);
lean_dec_ref(v_a_6621_);
lean_dec(v_a_6620_);
lean_dec_ref(v_a_6619_);
return v_res_6624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6632_, lean_object* v_b_6633_, lean_object* v_a_6634_, lean_object* v_a_6635_, lean_object* v_a_6636_, lean_object* v_a_6637_){
_start:
{
lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
v___x_6639_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6640_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6641_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6639_, v___x_6640_, v_a_6632_, v_b_6633_, v_a_6634_, v_a_6635_, v_a_6636_, v_a_6637_);
return v___x_6641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6642_, lean_object* v_b_6643_, lean_object* v_a_6644_, lean_object* v_a_6645_, lean_object* v_a_6646_, lean_object* v_a_6647_, lean_object* v_a_6648_){
_start:
{
lean_object* v_res_6649_; 
v_res_6649_ = l_Lean_Meta_mkAdd(v_a_6642_, v_b_6643_, v_a_6644_, v_a_6645_, v_a_6646_, v_a_6647_);
lean_dec(v_a_6647_);
lean_dec_ref(v_a_6646_);
lean_dec(v_a_6645_);
lean_dec_ref(v_a_6644_);
return v_res_6649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6657_, lean_object* v_b_6658_, lean_object* v_a_6659_, lean_object* v_a_6660_, lean_object* v_a_6661_, lean_object* v_a_6662_){
_start:
{
lean_object* v___x_6664_; lean_object* v___x_6665_; lean_object* v___x_6666_; 
v___x_6664_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6665_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6666_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6664_, v___x_6665_, v_a_6657_, v_b_6658_, v_a_6659_, v_a_6660_, v_a_6661_, v_a_6662_);
return v___x_6666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6667_, lean_object* v_b_6668_, lean_object* v_a_6669_, lean_object* v_a_6670_, lean_object* v_a_6671_, lean_object* v_a_6672_, lean_object* v_a_6673_){
_start:
{
lean_object* v_res_6674_; 
v_res_6674_ = l_Lean_Meta_mkSub(v_a_6667_, v_b_6668_, v_a_6669_, v_a_6670_, v_a_6671_, v_a_6672_);
lean_dec(v_a_6672_);
lean_dec_ref(v_a_6671_);
lean_dec(v_a_6670_);
lean_dec_ref(v_a_6669_);
return v_res_6674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6682_, lean_object* v_b_6683_, lean_object* v_a_6684_, lean_object* v_a_6685_, lean_object* v_a_6686_, lean_object* v_a_6687_){
_start:
{
lean_object* v___x_6689_; lean_object* v___x_6690_; lean_object* v___x_6691_; 
v___x_6689_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6690_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6691_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6689_, v___x_6690_, v_a_6682_, v_b_6683_, v_a_6684_, v_a_6685_, v_a_6686_, v_a_6687_);
return v___x_6691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6692_, lean_object* v_b_6693_, lean_object* v_a_6694_, lean_object* v_a_6695_, lean_object* v_a_6696_, lean_object* v_a_6697_, lean_object* v_a_6698_){
_start:
{
lean_object* v_res_6699_; 
v_res_6699_ = l_Lean_Meta_mkMul(v_a_6692_, v_b_6693_, v_a_6694_, v_a_6695_, v_a_6696_, v_a_6697_);
lean_dec(v_a_6697_);
lean_dec_ref(v_a_6696_);
lean_dec(v_a_6695_);
lean_dec_ref(v_a_6694_);
return v_res_6699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6700_, lean_object* v_rName_6701_, lean_object* v_a_6702_, lean_object* v_b_6703_, lean_object* v_a_6704_, lean_object* v_a_6705_, lean_object* v_a_6706_, lean_object* v_a_6707_){
_start:
{
lean_object* v___x_6709_; 
lean_inc(v_a_6707_);
lean_inc_ref(v_a_6706_);
lean_inc(v_a_6705_);
lean_inc_ref(v_a_6704_);
lean_inc_ref(v_a_6702_);
v___x_6709_ = lean_infer_type(v_a_6702_, v_a_6704_, v_a_6705_, v_a_6706_, v_a_6707_);
if (lean_obj_tag(v___x_6709_) == 0)
{
lean_object* v_a_6710_; lean_object* v___x_6711_; 
v_a_6710_ = lean_ctor_get(v___x_6709_, 0);
lean_inc_n(v_a_6710_, 2);
lean_dec_ref_known(v___x_6709_, 1);
v___x_6711_ = l_Lean_Meta_getDecLevel(v_a_6710_, v_a_6704_, v_a_6705_, v_a_6706_, v_a_6707_);
if (lean_obj_tag(v___x_6711_) == 0)
{
lean_object* v_a_6712_; lean_object* v___x_6713_; lean_object* v___x_6714_; lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; lean_object* v___x_6718_; 
v_a_6712_ = lean_ctor_get(v___x_6711_, 0);
lean_inc(v_a_6712_);
lean_dec_ref_known(v___x_6711_, 1);
v___x_6713_ = lean_box(0);
v___x_6714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6714_, 0, v_a_6712_);
lean_ctor_set(v___x_6714_, 1, v___x_6713_);
lean_inc_ref(v___x_6714_);
v___x_6715_ = l_Lean_mkConst(v_className_6700_, v___x_6714_);
lean_inc(v_a_6710_);
v___x_6716_ = l_Lean_Expr_app___override(v___x_6715_, v_a_6710_);
v___x_6717_ = lean_box(0);
v___x_6718_ = l_Lean_Meta_synthInstance(v___x_6716_, v___x_6717_, v_a_6704_, v_a_6705_, v_a_6706_, v_a_6707_);
if (lean_obj_tag(v___x_6718_) == 0)
{
lean_object* v_a_6719_; lean_object* v___x_6721_; uint8_t v_isShared_6722_; uint8_t v_isSharedCheck_6728_; 
v_a_6719_ = lean_ctor_get(v___x_6718_, 0);
v_isSharedCheck_6728_ = !lean_is_exclusive(v___x_6718_);
if (v_isSharedCheck_6728_ == 0)
{
v___x_6721_ = v___x_6718_;
v_isShared_6722_ = v_isSharedCheck_6728_;
goto v_resetjp_6720_;
}
else
{
lean_inc(v_a_6719_);
lean_dec(v___x_6718_);
v___x_6721_ = lean_box(0);
v_isShared_6722_ = v_isSharedCheck_6728_;
goto v_resetjp_6720_;
}
v_resetjp_6720_:
{
lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6726_; 
v___x_6723_ = l_Lean_mkConst(v_rName_6701_, v___x_6714_);
v___x_6724_ = l_Lean_mkApp4(v___x_6723_, v_a_6710_, v_a_6719_, v_a_6702_, v_b_6703_);
if (v_isShared_6722_ == 0)
{
lean_ctor_set(v___x_6721_, 0, v___x_6724_);
v___x_6726_ = v___x_6721_;
goto v_reusejp_6725_;
}
else
{
lean_object* v_reuseFailAlloc_6727_; 
v_reuseFailAlloc_6727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6727_, 0, v___x_6724_);
v___x_6726_ = v_reuseFailAlloc_6727_;
goto v_reusejp_6725_;
}
v_reusejp_6725_:
{
return v___x_6726_;
}
}
}
else
{
lean_dec_ref_known(v___x_6714_, 2);
lean_dec(v_a_6710_);
lean_dec_ref(v_b_6703_);
lean_dec_ref(v_a_6702_);
lean_dec(v_rName_6701_);
return v___x_6718_;
}
}
else
{
lean_object* v_a_6729_; lean_object* v___x_6731_; uint8_t v_isShared_6732_; uint8_t v_isSharedCheck_6736_; 
lean_dec(v_a_6710_);
lean_dec_ref(v_b_6703_);
lean_dec_ref(v_a_6702_);
lean_dec(v_rName_6701_);
lean_dec(v_className_6700_);
v_a_6729_ = lean_ctor_get(v___x_6711_, 0);
v_isSharedCheck_6736_ = !lean_is_exclusive(v___x_6711_);
if (v_isSharedCheck_6736_ == 0)
{
v___x_6731_ = v___x_6711_;
v_isShared_6732_ = v_isSharedCheck_6736_;
goto v_resetjp_6730_;
}
else
{
lean_inc(v_a_6729_);
lean_dec(v___x_6711_);
v___x_6731_ = lean_box(0);
v_isShared_6732_ = v_isSharedCheck_6736_;
goto v_resetjp_6730_;
}
v_resetjp_6730_:
{
lean_object* v___x_6734_; 
if (v_isShared_6732_ == 0)
{
v___x_6734_ = v___x_6731_;
goto v_reusejp_6733_;
}
else
{
lean_object* v_reuseFailAlloc_6735_; 
v_reuseFailAlloc_6735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6735_, 0, v_a_6729_);
v___x_6734_ = v_reuseFailAlloc_6735_;
goto v_reusejp_6733_;
}
v_reusejp_6733_:
{
return v___x_6734_;
}
}
}
}
else
{
lean_dec_ref(v_b_6703_);
lean_dec_ref(v_a_6702_);
lean_dec(v_rName_6701_);
lean_dec(v_className_6700_);
return v___x_6709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6737_, lean_object* v_rName_6738_, lean_object* v_a_6739_, lean_object* v_b_6740_, lean_object* v_a_6741_, lean_object* v_a_6742_, lean_object* v_a_6743_, lean_object* v_a_6744_, lean_object* v_a_6745_){
_start:
{
lean_object* v_res_6746_; 
v_res_6746_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6737_, v_rName_6738_, v_a_6739_, v_b_6740_, v_a_6741_, v_a_6742_, v_a_6743_, v_a_6744_);
lean_dec(v_a_6744_);
lean_dec_ref(v_a_6743_);
lean_dec(v_a_6742_);
lean_dec_ref(v_a_6741_);
return v_res_6746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6749_, lean_object* v_b_6750_, lean_object* v_a_6751_, lean_object* v_a_6752_, lean_object* v_a_6753_, lean_object* v_a_6754_){
_start:
{
lean_object* v___x_6756_; lean_object* v___x_6757_; lean_object* v___x_6758_; 
v___x_6756_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6757_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6758_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6756_, v___x_6757_, v_a_6749_, v_b_6750_, v_a_6751_, v_a_6752_, v_a_6753_, v_a_6754_);
return v___x_6758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6759_, lean_object* v_b_6760_, lean_object* v_a_6761_, lean_object* v_a_6762_, lean_object* v_a_6763_, lean_object* v_a_6764_, lean_object* v_a_6765_){
_start:
{
lean_object* v_res_6766_; 
v_res_6766_ = l_Lean_Meta_mkLE(v_a_6759_, v_b_6760_, v_a_6761_, v_a_6762_, v_a_6763_, v_a_6764_);
lean_dec(v_a_6764_);
lean_dec_ref(v_a_6763_);
lean_dec(v_a_6762_);
lean_dec_ref(v_a_6761_);
return v_res_6766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6769_, lean_object* v_b_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_, lean_object* v_a_6773_, lean_object* v_a_6774_){
_start:
{
lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; 
v___x_6776_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6777_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6778_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6776_, v___x_6777_, v_a_6769_, v_b_6770_, v_a_6771_, v_a_6772_, v_a_6773_, v_a_6774_);
return v___x_6778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6779_, lean_object* v_b_6780_, lean_object* v_a_6781_, lean_object* v_a_6782_, lean_object* v_a_6783_, lean_object* v_a_6784_, lean_object* v_a_6785_){
_start:
{
lean_object* v_res_6786_; 
v_res_6786_ = l_Lean_Meta_mkLT(v_a_6779_, v_b_6780_, v_a_6781_, v_a_6782_, v_a_6783_, v_a_6784_);
lean_dec(v_a_6784_);
lean_dec_ref(v_a_6783_);
lean_dec(v_a_6782_);
lean_dec_ref(v_a_6781_);
return v_res_6786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6792_, lean_object* v_a_6793_, lean_object* v_a_6794_, lean_object* v_a_6795_, lean_object* v_a_6796_){
_start:
{
lean_object* v___x_6798_; lean_object* v___x_6799_; uint8_t v___x_6800_; 
v___x_6798_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6799_ = lean_unsigned_to_nat(3u);
v___x_6800_ = l_Lean_Expr_isAppOfArity(v_h_6792_, v___x_6798_, v___x_6799_);
if (v___x_6800_ == 0)
{
lean_object* v___x_6801_; lean_object* v___x_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; 
v___x_6801_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6802_ = lean_unsigned_to_nat(1u);
v___x_6803_ = lean_mk_empty_array_with_capacity(v___x_6802_);
v___x_6804_ = lean_array_push(v___x_6803_, v_h_6792_);
v___x_6805_ = l_Lean_Meta_mkAppM(v___x_6801_, v___x_6804_, v_a_6793_, v_a_6794_, v_a_6795_, v_a_6796_);
return v___x_6805_;
}
else
{
lean_object* v___x_6806_; lean_object* v___x_6807_; 
v___x_6806_ = l_Lean_Expr_appArg_x21(v_h_6792_);
lean_dec_ref(v_h_6792_);
v___x_6807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6807_, 0, v___x_6806_);
return v___x_6807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6808_, lean_object* v_a_6809_, lean_object* v_a_6810_, lean_object* v_a_6811_, lean_object* v_a_6812_, lean_object* v_a_6813_){
_start:
{
lean_object* v_res_6814_; 
v_res_6814_ = l_Lean_Meta_mkIffOfEq(v_h_6808_, v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_);
lean_dec(v_a_6812_);
lean_dec_ref(v_a_6811_);
lean_dec(v_a_6810_);
lean_dec_ref(v_a_6809_);
return v_res_6814_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6820_; lean_object* v___x_6821_; lean_object* v___x_6822_; 
v___x_6820_ = lean_box(0);
v___x_6821_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6822_ = l_Lean_mkConst(v___x_6821_, v___x_6820_);
return v___x_6822_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6825_; lean_object* v___x_6826_; lean_object* v___x_6827_; 
v___x_6825_ = lean_box(0);
v___x_6826_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6827_ = l_Lean_mkConst(v___x_6826_, v___x_6825_);
return v___x_6827_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6830_; 
v___x_6828_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6829_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6830_, 0, v___x_6829_);
lean_ctor_set(v___x_6830_, 1, v___x_6828_);
return v___x_6830_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6835_; lean_object* v___x_6836_; lean_object* v___x_6837_; 
v___x_6835_ = lean_box(0);
v___x_6836_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6837_ = l_Lean_mkConst(v___x_6836_, v___x_6835_);
return v___x_6837_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6840_; lean_object* v___x_6841_; lean_object* v___x_6842_; 
v___x_6840_ = lean_box(0);
v___x_6841_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6842_ = l_Lean_mkConst(v___x_6841_, v___x_6840_);
return v___x_6842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6843_, lean_object* v_a_6844_, lean_object* v_a_6845_, lean_object* v_a_6846_, lean_object* v_a_6847_){
_start:
{
if (lean_obj_tag(v_a_6843_) == 0)
{
lean_object* v___x_6849_; lean_object* v___x_6850_; 
v___x_6849_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6850_, 0, v___x_6849_);
return v___x_6850_;
}
else
{
lean_object* v_tail_6851_; 
v_tail_6851_ = lean_ctor_get(v_a_6843_, 1);
if (lean_obj_tag(v_tail_6851_) == 0)
{
lean_object* v_head_6852_; lean_object* v___x_6854_; uint8_t v_isShared_6855_; uint8_t v_isSharedCheck_6876_; 
v_head_6852_ = lean_ctor_get(v_a_6843_, 0);
v_isSharedCheck_6876_ = !lean_is_exclusive(v_a_6843_);
if (v_isSharedCheck_6876_ == 0)
{
lean_object* v_unused_6877_; 
v_unused_6877_ = lean_ctor_get(v_a_6843_, 1);
lean_dec(v_unused_6877_);
v___x_6854_ = v_a_6843_;
v_isShared_6855_ = v_isSharedCheck_6876_;
goto v_resetjp_6853_;
}
else
{
lean_inc(v_head_6852_);
lean_dec(v_a_6843_);
v___x_6854_ = lean_box(0);
v_isShared_6855_ = v_isSharedCheck_6876_;
goto v_resetjp_6853_;
}
v_resetjp_6853_:
{
lean_object* v___x_6856_; 
lean_inc(v_a_6847_);
lean_inc_ref(v_a_6846_);
lean_inc(v_a_6845_);
lean_inc_ref(v_a_6844_);
lean_inc(v_head_6852_);
v___x_6856_ = lean_infer_type(v_head_6852_, v_a_6844_, v_a_6845_, v_a_6846_, v_a_6847_);
if (lean_obj_tag(v___x_6856_) == 0)
{
lean_object* v_a_6857_; lean_object* v___x_6859_; uint8_t v_isShared_6860_; uint8_t v_isSharedCheck_6867_; 
v_a_6857_ = lean_ctor_get(v___x_6856_, 0);
v_isSharedCheck_6867_ = !lean_is_exclusive(v___x_6856_);
if (v_isSharedCheck_6867_ == 0)
{
v___x_6859_ = v___x_6856_;
v_isShared_6860_ = v_isSharedCheck_6867_;
goto v_resetjp_6858_;
}
else
{
lean_inc(v_a_6857_);
lean_dec(v___x_6856_);
v___x_6859_ = lean_box(0);
v_isShared_6860_ = v_isSharedCheck_6867_;
goto v_resetjp_6858_;
}
v_resetjp_6858_:
{
lean_object* v___x_6862_; 
if (v_isShared_6855_ == 0)
{
lean_ctor_set_tag(v___x_6854_, 0);
lean_ctor_set(v___x_6854_, 1, v_a_6857_);
v___x_6862_ = v___x_6854_;
goto v_reusejp_6861_;
}
else
{
lean_object* v_reuseFailAlloc_6866_; 
v_reuseFailAlloc_6866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6866_, 0, v_head_6852_);
lean_ctor_set(v_reuseFailAlloc_6866_, 1, v_a_6857_);
v___x_6862_ = v_reuseFailAlloc_6866_;
goto v_reusejp_6861_;
}
v_reusejp_6861_:
{
lean_object* v___x_6864_; 
if (v_isShared_6860_ == 0)
{
lean_ctor_set(v___x_6859_, 0, v___x_6862_);
v___x_6864_ = v___x_6859_;
goto v_reusejp_6863_;
}
else
{
lean_object* v_reuseFailAlloc_6865_; 
v_reuseFailAlloc_6865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6865_, 0, v___x_6862_);
v___x_6864_ = v_reuseFailAlloc_6865_;
goto v_reusejp_6863_;
}
v_reusejp_6863_:
{
return v___x_6864_;
}
}
}
}
else
{
lean_object* v_a_6868_; lean_object* v___x_6870_; uint8_t v_isShared_6871_; uint8_t v_isSharedCheck_6875_; 
lean_del_object(v___x_6854_);
lean_dec(v_head_6852_);
v_a_6868_ = lean_ctor_get(v___x_6856_, 0);
v_isSharedCheck_6875_ = !lean_is_exclusive(v___x_6856_);
if (v_isSharedCheck_6875_ == 0)
{
v___x_6870_ = v___x_6856_;
v_isShared_6871_ = v_isSharedCheck_6875_;
goto v_resetjp_6869_;
}
else
{
lean_inc(v_a_6868_);
lean_dec(v___x_6856_);
v___x_6870_ = lean_box(0);
v_isShared_6871_ = v_isSharedCheck_6875_;
goto v_resetjp_6869_;
}
v_resetjp_6869_:
{
lean_object* v___x_6873_; 
if (v_isShared_6871_ == 0)
{
v___x_6873_ = v___x_6870_;
goto v_reusejp_6872_;
}
else
{
lean_object* v_reuseFailAlloc_6874_; 
v_reuseFailAlloc_6874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6874_, 0, v_a_6868_);
v___x_6873_ = v_reuseFailAlloc_6874_;
goto v_reusejp_6872_;
}
v_reusejp_6872_:
{
return v___x_6873_;
}
}
}
}
}
else
{
lean_object* v_head_6878_; lean_object* v___x_6879_; 
lean_inc(v_tail_6851_);
v_head_6878_ = lean_ctor_get(v_a_6843_, 0);
lean_inc(v_head_6878_);
lean_dec_ref_known(v_a_6843_, 2);
v___x_6879_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6851_, v_a_6844_, v_a_6845_, v_a_6846_, v_a_6847_);
if (lean_obj_tag(v___x_6879_) == 0)
{
lean_object* v_a_6880_; lean_object* v_fst_6881_; lean_object* v_snd_6882_; lean_object* v___x_6884_; uint8_t v_isShared_6885_; uint8_t v_isSharedCheck_6910_; 
v_a_6880_ = lean_ctor_get(v___x_6879_, 0);
lean_inc(v_a_6880_);
lean_dec_ref_known(v___x_6879_, 1);
v_fst_6881_ = lean_ctor_get(v_a_6880_, 0);
v_snd_6882_ = lean_ctor_get(v_a_6880_, 1);
v_isSharedCheck_6910_ = !lean_is_exclusive(v_a_6880_);
if (v_isSharedCheck_6910_ == 0)
{
v___x_6884_ = v_a_6880_;
v_isShared_6885_ = v_isSharedCheck_6910_;
goto v_resetjp_6883_;
}
else
{
lean_inc(v_snd_6882_);
lean_inc(v_fst_6881_);
lean_dec(v_a_6880_);
v___x_6884_ = lean_box(0);
v_isShared_6885_ = v_isSharedCheck_6910_;
goto v_resetjp_6883_;
}
v_resetjp_6883_:
{
lean_object* v___x_6886_; 
lean_inc(v_a_6847_);
lean_inc_ref(v_a_6846_);
lean_inc(v_a_6845_);
lean_inc_ref(v_a_6844_);
lean_inc(v_head_6878_);
v___x_6886_ = lean_infer_type(v_head_6878_, v_a_6844_, v_a_6845_, v_a_6846_, v_a_6847_);
if (lean_obj_tag(v___x_6886_) == 0)
{
lean_object* v_a_6887_; lean_object* v___x_6889_; uint8_t v_isShared_6890_; uint8_t v_isSharedCheck_6901_; 
v_a_6887_ = lean_ctor_get(v___x_6886_, 0);
v_isSharedCheck_6901_ = !lean_is_exclusive(v___x_6886_);
if (v_isSharedCheck_6901_ == 0)
{
v___x_6889_ = v___x_6886_;
v_isShared_6890_ = v_isSharedCheck_6901_;
goto v_resetjp_6888_;
}
else
{
lean_inc(v_a_6887_);
lean_dec(v___x_6886_);
v___x_6889_ = lean_box(0);
v_isShared_6890_ = v_isSharedCheck_6901_;
goto v_resetjp_6888_;
}
v_resetjp_6888_:
{
lean_object* v___x_6891_; lean_object* v___x_6892_; lean_object* v___x_6893_; lean_object* v___x_6894_; lean_object* v___x_6896_; 
v___x_6891_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6882_);
lean_inc(v_a_6887_);
v___x_6892_ = l_Lean_mkApp4(v___x_6891_, v_a_6887_, v_snd_6882_, v_head_6878_, v_fst_6881_);
v___x_6893_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6894_ = l_Lean_mkAppB(v___x_6893_, v_a_6887_, v_snd_6882_);
if (v_isShared_6885_ == 0)
{
lean_ctor_set(v___x_6884_, 1, v___x_6894_);
lean_ctor_set(v___x_6884_, 0, v___x_6892_);
v___x_6896_ = v___x_6884_;
goto v_reusejp_6895_;
}
else
{
lean_object* v_reuseFailAlloc_6900_; 
v_reuseFailAlloc_6900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6900_, 0, v___x_6892_);
lean_ctor_set(v_reuseFailAlloc_6900_, 1, v___x_6894_);
v___x_6896_ = v_reuseFailAlloc_6900_;
goto v_reusejp_6895_;
}
v_reusejp_6895_:
{
lean_object* v___x_6898_; 
if (v_isShared_6890_ == 0)
{
lean_ctor_set(v___x_6889_, 0, v___x_6896_);
v___x_6898_ = v___x_6889_;
goto v_reusejp_6897_;
}
else
{
lean_object* v_reuseFailAlloc_6899_; 
v_reuseFailAlloc_6899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6899_, 0, v___x_6896_);
v___x_6898_ = v_reuseFailAlloc_6899_;
goto v_reusejp_6897_;
}
v_reusejp_6897_:
{
return v___x_6898_;
}
}
}
}
else
{
lean_object* v_a_6902_; lean_object* v___x_6904_; uint8_t v_isShared_6905_; uint8_t v_isSharedCheck_6909_; 
lean_del_object(v___x_6884_);
lean_dec(v_snd_6882_);
lean_dec(v_fst_6881_);
lean_dec(v_head_6878_);
v_a_6902_ = lean_ctor_get(v___x_6886_, 0);
v_isSharedCheck_6909_ = !lean_is_exclusive(v___x_6886_);
if (v_isSharedCheck_6909_ == 0)
{
v___x_6904_ = v___x_6886_;
v_isShared_6905_ = v_isSharedCheck_6909_;
goto v_resetjp_6903_;
}
else
{
lean_inc(v_a_6902_);
lean_dec(v___x_6886_);
v___x_6904_ = lean_box(0);
v_isShared_6905_ = v_isSharedCheck_6909_;
goto v_resetjp_6903_;
}
v_resetjp_6903_:
{
lean_object* v___x_6907_; 
if (v_isShared_6905_ == 0)
{
v___x_6907_ = v___x_6904_;
goto v_reusejp_6906_;
}
else
{
lean_object* v_reuseFailAlloc_6908_; 
v_reuseFailAlloc_6908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6908_, 0, v_a_6902_);
v___x_6907_ = v_reuseFailAlloc_6908_;
goto v_reusejp_6906_;
}
v_reusejp_6906_:
{
return v___x_6907_;
}
}
}
}
}
else
{
lean_dec(v_head_6878_);
return v___x_6879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6911_, lean_object* v_a_6912_, lean_object* v_a_6913_, lean_object* v_a_6914_, lean_object* v_a_6915_, lean_object* v_a_6916_){
_start:
{
lean_object* v_res_6917_; 
v_res_6917_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6911_, v_a_6912_, v_a_6913_, v_a_6914_, v_a_6915_);
lean_dec(v_a_6915_);
lean_dec_ref(v_a_6914_);
lean_dec(v_a_6913_);
lean_dec_ref(v_a_6912_);
return v_res_6917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_6918_, lean_object* v_a_6919_, lean_object* v_a_6920_, lean_object* v_a_6921_, lean_object* v_a_6922_){
_start:
{
lean_object* v___x_6924_; 
v___x_6924_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_6918_, v_a_6919_, v_a_6920_, v_a_6921_, v_a_6922_);
if (lean_obj_tag(v___x_6924_) == 0)
{
lean_object* v_a_6925_; lean_object* v___x_6927_; uint8_t v_isShared_6928_; uint8_t v_isSharedCheck_6933_; 
v_a_6925_ = lean_ctor_get(v___x_6924_, 0);
v_isSharedCheck_6933_ = !lean_is_exclusive(v___x_6924_);
if (v_isSharedCheck_6933_ == 0)
{
v___x_6927_ = v___x_6924_;
v_isShared_6928_ = v_isSharedCheck_6933_;
goto v_resetjp_6926_;
}
else
{
lean_inc(v_a_6925_);
lean_dec(v___x_6924_);
v___x_6927_ = lean_box(0);
v_isShared_6928_ = v_isSharedCheck_6933_;
goto v_resetjp_6926_;
}
v_resetjp_6926_:
{
lean_object* v_fst_6929_; lean_object* v___x_6931_; 
v_fst_6929_ = lean_ctor_get(v_a_6925_, 0);
lean_inc(v_fst_6929_);
lean_dec(v_a_6925_);
if (v_isShared_6928_ == 0)
{
lean_ctor_set(v___x_6927_, 0, v_fst_6929_);
v___x_6931_ = v___x_6927_;
goto v_reusejp_6930_;
}
else
{
lean_object* v_reuseFailAlloc_6932_; 
v_reuseFailAlloc_6932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6932_, 0, v_fst_6929_);
v___x_6931_ = v_reuseFailAlloc_6932_;
goto v_reusejp_6930_;
}
v_reusejp_6930_:
{
return v___x_6931_;
}
}
}
else
{
lean_object* v_a_6934_; lean_object* v___x_6936_; uint8_t v_isShared_6937_; uint8_t v_isSharedCheck_6941_; 
v_a_6934_ = lean_ctor_get(v___x_6924_, 0);
v_isSharedCheck_6941_ = !lean_is_exclusive(v___x_6924_);
if (v_isSharedCheck_6941_ == 0)
{
v___x_6936_ = v___x_6924_;
v_isShared_6937_ = v_isSharedCheck_6941_;
goto v_resetjp_6935_;
}
else
{
lean_inc(v_a_6934_);
lean_dec(v___x_6924_);
v___x_6936_ = lean_box(0);
v_isShared_6937_ = v_isSharedCheck_6941_;
goto v_resetjp_6935_;
}
v_resetjp_6935_:
{
lean_object* v___x_6939_; 
if (v_isShared_6937_ == 0)
{
v___x_6939_ = v___x_6936_;
goto v_reusejp_6938_;
}
else
{
lean_object* v_reuseFailAlloc_6940_; 
v_reuseFailAlloc_6940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6940_, 0, v_a_6934_);
v___x_6939_ = v_reuseFailAlloc_6940_;
goto v_reusejp_6938_;
}
v_reusejp_6938_:
{
return v___x_6939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_6942_, lean_object* v_a_6943_, lean_object* v_a_6944_, lean_object* v_a_6945_, lean_object* v_a_6946_, lean_object* v_a_6947_){
_start:
{
lean_object* v_res_6948_; 
v_res_6948_ = l_Lean_Meta_mkAndIntroN(v_hs_6942_, v_a_6943_, v_a_6944_, v_a_6945_, v_a_6946_);
lean_dec(v_a_6946_);
lean_dec_ref(v_a_6945_);
lean_dec(v_a_6944_);
lean_dec_ref(v_a_6943_);
return v_res_6948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7005_; uint8_t v___x_7006_; lean_object* v___x_7007_; lean_object* v___x_7008_; 
v___x_7005_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7006_ = 0;
v___x_7007_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7008_ = l_Lean_registerTraceClass(v___x_7005_, v___x_7006_, v___x_7007_);
if (lean_obj_tag(v___x_7008_) == 0)
{
lean_object* v___x_7009_; uint8_t v___x_7010_; lean_object* v___x_7011_; 
lean_dec_ref_known(v___x_7008_, 1);
v___x_7009_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7010_ = 1;
v___x_7011_ = l_Lean_registerTraceClass(v___x_7009_, v___x_7010_, v___x_7007_);
if (lean_obj_tag(v___x_7011_) == 0)
{
lean_object* v___x_7012_; lean_object* v___x_7013_; 
lean_dec_ref_known(v___x_7011_, 1);
v___x_7012_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7013_ = l_Lean_registerTraceClass(v___x_7012_, v___x_7010_, v___x_7007_);
return v___x_7013_;
}
else
{
return v___x_7011_;
}
}
else
{
return v___x_7008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7014_){
_start:
{
lean_object* v_res_7015_; 
v_res_7015_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7015_;
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
