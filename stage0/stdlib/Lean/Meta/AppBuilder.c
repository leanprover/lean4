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
lean_inc_ref(v___x_2157_);
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
v___x_2166_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2157_, v_declHint_2148_);
lean_dec_ref(v___x_2157_);
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
lean_object* v_toCold_2248_; lean_object* v_currRecDepth_2249_; lean_object* v_ref_2250_; uint16_t v_optionFlags_2251_; uint8_t v_suppressElabErrors_2252_; uint8_t v_checkDeprecated_2253_; uint8_t v_isRecordingDeps_2254_; lean_object* v_ref_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v_toCold_2248_ = lean_ctor_get(v___y_2245_, 0);
v_currRecDepth_2249_ = lean_ctor_get(v___y_2245_, 1);
v_ref_2250_ = lean_ctor_get(v___y_2245_, 2);
v_optionFlags_2251_ = lean_ctor_get_uint16(v___y_2245_, sizeof(void*)*3);
v_suppressElabErrors_2252_ = lean_ctor_get_uint8(v___y_2245_, sizeof(void*)*3 + 2);
v_checkDeprecated_2253_ = lean_ctor_get_uint8(v___y_2245_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2254_ = lean_ctor_get_uint8(v___y_2245_, sizeof(void*)*3 + 4);
v_ref_2255_ = l_Lean_replaceRef(v_ref_2241_, v_ref_2250_);
lean_inc(v_currRecDepth_2249_);
lean_inc_ref(v_toCold_2248_);
v___x_2256_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2256_, 0, v_toCold_2248_);
lean_ctor_set(v___x_2256_, 1, v_currRecDepth_2249_);
lean_ctor_set(v___x_2256_, 2, v_ref_2255_);
lean_ctor_set_uint16(v___x_2256_, sizeof(void*)*3, v_optionFlags_2251_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3 + 2, v_suppressElabErrors_2252_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3 + 3, v_checkDeprecated_2253_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3 + 4, v_isRecordingDeps_2254_);
v___x_2257_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2242_, v___y_2243_, v___y_2244_, v___x_2256_, v___y_2246_);
lean_dec_ref_known(v___x_2256_, 3);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2258_, lean_object* v_msg_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2258_, v_msg_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v_ref_2258_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2266_, lean_object* v_msg_2267_, lean_object* v_declHint_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; lean_object* v_a_2275_; lean_object* v___x_2276_; 
v___x_2274_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2267_, v_declHint_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2266_, v_a_2275_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2277_, lean_object* v_msg_2278_, lean_object* v_declHint_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2277_, v_msg_2278_, v_declHint_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v_ref_2277_);
return v_res_2285_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2288_ = l_Lean_stringToMessageData(v___x_2287_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2291_ = l_Lean_stringToMessageData(v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2292_, lean_object* v_constName_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2299_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2300_ = 0;
lean_inc(v_constName_2293_);
v___x_2301_ = l_Lean_MessageData_ofConstName(v_constName_2293_, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2299_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2292_, v___x_2304_, v_constName_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2306_, lean_object* v_constName_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2306_, v_constName_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v_ref_2306_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_ref_2320_; lean_object* v___x_2321_; 
v_ref_2320_ = lean_ctor_get(v___y_2317_, 2);
v___x_2321_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2320_, v_constName_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; lean_object* v_env_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; 
v___x_2335_ = lean_st_ref_get(v___y_2333_);
v_env_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc_ref(v_env_2336_);
lean_dec(v___x_2335_);
v___x_2337_ = 0;
lean_inc(v_constName_2329_);
v___x_2338_ = l_Lean_Environment_findConstVal_x3f(v_env_2336_, v_constName_2329_, v___x_2337_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
return v___x_2339_;
}
else
{
lean_object* v_val_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_constName_2329_);
v_val_2340_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2338_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_val_2340_);
lean_dec(v___x_2338_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set_tag(v___x_2342_, 0);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_val_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2361_; 
lean_inc(v_constName_2355_);
v___x_2361_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v_levelParams_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v_levelParams_2363_ = lean_ctor_get(v_a_2362_, 1);
v___x_2364_ = lean_box(0);
lean_inc(v_levelParams_2363_);
v___x_2365_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2363_, v___x_2364_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc_n(v_a_2366_, 2);
lean_dec_ref_known(v___x_2365_, 1);
v___x_2367_ = l_Lean_mkConst(v_constName_2355_, v_a_2366_);
v___x_2368_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2362_, v_a_2366_, v_a_2359_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2377_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2377_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2377_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2367_);
lean_ctor_set(v___x_2373_, 1, v_a_2369_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2373_);
v___x_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec_ref(v___x_2367_);
v_a_2378_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2368_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2368_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_a_2362_);
lean_dec(v_constName_2355_);
v_a_2386_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2365_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2365_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v_constName_2355_);
v_a_2394_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2361_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2361_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2409_, lean_object* v_constName_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2417_, lean_object* v_constName_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2417_, v_constName_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2425_, lean_object* v_ref_2426_, lean_object* v_constName_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2426_, v_constName_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_ref_2435_, lean_object* v_constName_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2434_, v_ref_2435_, v_constName_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v_ref_2435_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2443_, lean_object* v_ref_2444_, lean_object* v_msg_2445_, lean_object* v_declHint_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2444_, v_msg_2445_, v_declHint_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_ref_2454_, lean_object* v_msg_2455_, lean_object* v_declHint_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2453_, v_ref_2454_, v_msg_2455_, v_declHint_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v_ref_2454_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2463_, lean_object* v_declHint_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2463_, v_declHint_2464_, v___y_2468_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2471_, lean_object* v_declHint_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2471_, v_declHint_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2479_, lean_object* v_ref_2480_, lean_object* v_msg_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2480_, v_msg_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2488_, lean_object* v_ref_2489_, lean_object* v_msg_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2488_, v_ref_2489_, v_msg_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v_ref_2489_);
return v_res_2496_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2499_ = l_Lean_stringToMessageData(v___x_2498_);
return v___x_2499_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2502_ = l_Lean_stringToMessageData(v___x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2503_, lean_object* v_f_2504_, lean_object* v_inst_2505_, lean_object* v_xs_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2513_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2514_ = lean_apply_1(v_inst_2503_, v_f_2504_);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_apply_1(v_inst_2505_, v_xs_2506_);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2521_, lean_object* v_f_2522_, lean_object* v_inst_2523_, lean_object* v_xs_2524_, lean_object* v_x_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2521_, v_f_2522_, v_inst_2523_, v_xs_2524_, v_x_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v_x_2525_);
return v_res_2531_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_instMonadEIO___redArg();
return v___x_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2534_ = l_StateRefT_x27_instMonad___redArg(v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2542_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2543_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2542_, v___x_2541_);
return v___x_2543_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2545_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2546_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2545_, v___x_2544_);
return v___x_2546_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2549_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2551_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2552_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2551_, v___x_2550_, v___x_2549_);
return v___x_2552_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___f_2554_; lean_object* v___f_2555_; lean_object* v___x_2556_; 
v___x_2553_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2554_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2555_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2556_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2555_, v___f_2554_, v___x_2553_);
return v___x_2556_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_instMonadExceptOfEIO___redArg();
return v___x_2557_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2559_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2561_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2560_);
return v___x_2561_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2563_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2562_);
return v___x_2563_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2565_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2564_);
return v___x_2565_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2577_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2578_ = l_Lean_Name_append(v___x_2577_, v___x_2576_);
return v___x_2578_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2585_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2586_ = l_Lean_Name_append(v___x_2585_, v___x_2584_);
return v___x_2586_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2587_; double v___x_2588_; 
v___x_2587_ = lean_unsigned_to_nat(1000000000u);
v___x_2588_ = lean_float_of_nat(v___x_2587_);
return v___x_2588_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2595_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2596_ = l_Lean_Name_append(v___x_2595_, v___x_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2597_, lean_object* v_inst_2598_, lean_object* v_f_2599_, lean_object* v_xs_2600_, lean_object* v_k_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2607_; lean_object* v_toApplicative_2608_; lean_object* v_toFunctor_2609_; lean_object* v_toSeq_2610_; lean_object* v_toSeqLeft_2611_; lean_object* v_toSeqRight_2612_; lean_object* v___f_2613_; lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v_toApplicative_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2847_; 
v___x_2607_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2608_ = lean_ctor_get(v___x_2607_, 0);
v_toFunctor_2609_ = lean_ctor_get(v_toApplicative_2608_, 0);
v_toSeq_2610_ = lean_ctor_get(v_toApplicative_2608_, 2);
v_toSeqLeft_2611_ = lean_ctor_get(v_toApplicative_2608_, 3);
v_toSeqRight_2612_ = lean_ctor_get(v_toApplicative_2608_, 4);
v___f_2613_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2614_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2609_, 2);
v___f_2615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2615_, 0, v_toFunctor_2609_);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toFunctor_2609_);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___f_2615_);
lean_ctor_set(v___x_2617_, 1, v___f_2616_);
lean_inc(v_toSeqRight_2612_);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toSeqRight_2612_);
lean_inc(v_toSeqLeft_2611_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toSeqLeft_2611_);
lean_inc(v_toSeq_2610_);
v___f_2620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2620_, 0, v_toSeq_2610_);
v___x_2621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2617_);
lean_ctor_set(v___x_2621_, 1, v___f_2613_);
lean_ctor_set(v___x_2621_, 2, v___f_2620_);
lean_ctor_set(v___x_2621_, 3, v___f_2619_);
lean_ctor_set(v___x_2621_, 4, v___f_2618_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___f_2614_);
v___x_2623_ = l_StateRefT_x27_instMonad___redArg(v___x_2622_);
v_toApplicative_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2623_, 1);
lean_dec(v_unused_2848_);
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2847_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_toApplicative_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2847_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_toFunctor_2628_; lean_object* v_toSeq_2629_; lean_object* v_toSeqLeft_2630_; lean_object* v_toSeqRight_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2845_; 
v_toFunctor_2628_ = lean_ctor_get(v_toApplicative_2624_, 0);
v_toSeq_2629_ = lean_ctor_get(v_toApplicative_2624_, 2);
v_toSeqLeft_2630_ = lean_ctor_get(v_toApplicative_2624_, 3);
v_toSeqRight_2631_ = lean_ctor_get(v_toApplicative_2624_, 4);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_toApplicative_2624_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v_toApplicative_2624_, 1);
lean_dec(v_unused_2846_);
v___x_2633_ = v_toApplicative_2624_;
v_isShared_2634_ = v_isSharedCheck_2845_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_toSeqRight_2631_);
lean_inc(v_toSeqLeft_2630_);
lean_inc(v_toSeq_2629_);
lean_inc(v_toFunctor_2628_);
lean_dec(v_toApplicative_2624_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2845_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___f_2635_; lean_object* v___f_2636_; lean_object* v___f_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___f_2642_; lean_object* v___x_2644_; 
v___f_2635_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2636_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2628_);
v___f_2637_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2637_, 0, v_toFunctor_2628_);
v___f_2638_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2638_, 0, v_toFunctor_2628_);
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___f_2637_);
lean_ctor_set(v___x_2639_, 1, v___f_2638_);
v___f_2640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2640_, 0, v_toSeqRight_2631_);
v___f_2641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2641_, 0, v_toSeqLeft_2630_);
v___f_2642_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2642_, 0, v_toSeq_2629_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 4, v___f_2640_);
lean_ctor_set(v___x_2633_, 3, v___f_2641_);
lean_ctor_set(v___x_2633_, 2, v___f_2642_);
lean_ctor_set(v___x_2633_, 1, v___f_2635_);
lean_ctor_set(v___x_2633_, 0, v___x_2639_);
v___x_2644_ = v___x_2633_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v___f_2635_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v___f_2642_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v___f_2641_);
lean_ctor_set(v_reuseFailAlloc_2844_, 4, v___f_2640_);
v___x_2644_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2646_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 1, v___f_2636_);
lean_ctor_set(v___x_2626_, 0, v___x_2644_);
v___x_2646_ = v___x_2626_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___f_2636_);
v___x_2646_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v_toMonadRef_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v_toCold_2652_; lean_object* v_options_2653_; uint8_t v_hasTrace_2654_; 
v___x_2647_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2648_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2649_ = lean_ctor_get(v___x_2648_, 0);
v___x_2650_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2651_ = l_Lean_KVMap_instValueBool;
v_toCold_2652_ = lean_ctor_get(v_a_2604_, 0);
v_options_2653_ = lean_ctor_get(v_toCold_2652_, 2);
v_hasTrace_2654_ = lean_ctor_get_uint8(v_options_2653_, sizeof(void*)*1);
if (v_hasTrace_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref(v___x_2646_);
lean_dec(v_xs_2600_);
lean_dec(v_f_2599_);
lean_dec_ref(v_inst_2598_);
lean_dec_ref(v_inst_2597_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2655_ = lean_apply_5(v_k_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2655_) == 0)
{
return v___x_2655_;
}
else
{
lean_object* v_a_2656_; uint8_t v___x_2657_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
v___x_2657_ = l_Lean_Exception_isInterrupt(v_a_2656_);
if (v___x_2657_ == 0)
{
uint8_t v___x_2658_; 
lean_inc(v_a_2656_);
v___x_2658_ = l_Lean_Exception_isRuntime(v_a_2656_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2665_ == 0)
{
lean_object* v_unused_2666_; 
v_unused_2666_ = lean_ctor_get(v___x_2655_, 0);
lean_dec(v_unused_2666_);
v___x_2660_ = v___x_2655_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_dec(v___x_2655_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2656_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
else
{
lean_dec(v_a_2656_);
return v___x_2655_;
}
}
else
{
lean_dec(v_a_2656_);
return v___x_2655_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2667_; lean_object* v___x_2668_; lean_object* v___y_2670_; lean_object* v_a_2671_; lean_object* v___f_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v_a_2706_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v_a_2722_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v_a_2727_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v_a_2732_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v_a_2745_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_a_2758_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v_a_2763_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v_a_2768_; 
v_inheritedTraceOptions_2667_ = lean_ctor_get(v_toCold_2652_, 11);
v___x_2668_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2697_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2697_, 0, v_inst_2597_);
lean_closure_set(v___f_2697_, 1, v_f_2599_);
lean_closure_set(v___f_2697_, 2, v_inst_2598_);
lean_closure_set(v___f_2697_, 3, v_xs_2600_);
v___f_2698_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2701_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2667_, v_options_2653_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2815_ = l_Lean_trace_profiler;
v___x_2816_ = l_Lean_Option_get___redArg(v___x_2651_, v_options_2653_, v___x_2815_);
v___x_2817_ = lean_unbox(v___x_2816_);
lean_dec(v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec_ref(v___f_2697_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2818_ = lean_apply_5(v_k_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2821_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2822_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2667_, v_options_2653_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_dec(v_a_2819_);
lean_dec_ref(v___x_2646_);
return v___x_2818_;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_8887__overap_2824_; lean_object* v___x_2825_; 
lean_dec_ref_known(v___x_2818_, 1);
lean_inc(v_a_2819_);
v___x_2823_ = l_Lean_MessageData_ofExpr(v_a_2819_);
lean_inc_ref(v_toMonadRef_2649_);
lean_inc_ref(v___x_2646_);
v___x_8887__overap_2824_ = l_Lean_addTrace___redArg(v___x_2646_, v___x_2647_, v_toMonadRef_2649_, v___x_2668_, v___x_2820_, v___x_2823_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2825_ = lean_apply_5(v___x_8887__overap_2824_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec_ref(v___x_2646_);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v___x_2825_, 0);
lean_dec(v_unused_2833_);
v___x_2827_ = v___x_2825_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_dec(v___x_2825_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v_a_2819_);
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2819_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2819_);
v_a_2834_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2825_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2825_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
lean_inc(v_a_2834_);
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
v___y_2670_ = v___x_2839_;
v_a_2671_ = v_a_2834_;
goto v___jp_2669_;
}
}
}
}
}
else
{
lean_object* v_a_2842_; 
v_a_2842_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2842_);
v___y_2670_ = v___x_2818_;
v_a_2671_ = v_a_2842_;
goto v___jp_2669_;
}
}
else
{
goto v___jp_2778_;
}
}
else
{
goto v___jp_2778_;
}
v___jp_2669_:
{
uint8_t v___x_2672_; 
v___x_2672_ = l_Lean_Exception_isInterrupt(v_a_2671_);
if (v___x_2672_ == 0)
{
uint8_t v___x_2673_; 
lean_inc_ref(v_a_2671_);
v___x_2673_ = l_Lean_Exception_isRuntime(v_a_2671_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
lean_dec_ref(v___y_2670_);
v___x_2674_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2675_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2667_, v_options_2653_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
lean_dec_ref(v___x_2646_);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_a_2671_);
return v___x_2677_;
}
else
{
lean_object* v___x_2678_; lean_object* v___x_8704__overap_2679_; lean_object* v___x_2680_; 
lean_inc_ref(v_a_2671_);
v___x_2678_ = l_Lean_Exception_toMessageData(v_a_2671_);
lean_inc_ref(v_toMonadRef_2649_);
v___x_8704__overap_2679_ = l_Lean_addTrace___redArg(v___x_2646_, v___x_2647_, v_toMonadRef_2649_, v___x_2668_, v___x_2674_, v___x_2678_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2680_ = lean_apply_5(v___x_8704__overap_2679_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v___x_2680_, 0);
lean_dec(v_unused_2688_);
v___x_2682_ = v___x_2680_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v___x_2680_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set_tag(v___x_2682_, 1);
lean_ctor_set(v___x_2682_, 0, v_a_2671_);
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2671_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v_a_2671_);
v_a_2689_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2680_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2680_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_2671_);
lean_dec_ref(v___x_2646_);
return v___y_2670_;
}
}
else
{
lean_dec_ref(v_a_2671_);
lean_dec_ref(v___x_2646_);
return v___y_2670_;
}
}
v___jp_2703_:
{
lean_object* v___x_2707_; double v___x_2708_; double v___x_2709_; double v___x_2710_; double v___x_2711_; double v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_8763__overap_2717_; lean_object* v___x_2718_; 
v___x_2707_ = lean_io_mono_nanos_now();
v___x_2708_ = lean_float_of_nat(v___y_2704_);
v___x_2709_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2710_ = lean_float_div(v___x_2708_, v___x_2709_);
v___x_2711_ = lean_float_of_nat(v___x_2707_);
v___x_2712_ = lean_float_div(v___x_2711_, v___x_2709_);
v___x_2713_ = lean_box_float(v___x_2710_);
v___x_2714_ = lean_box_float(v___x_2712_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_a_2706_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
lean_inc_ref(v_toMonadRef_2649_);
v___x_8763__overap_2717_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2646_, v___x_2647_, v_toMonadRef_2649_, v___x_2668_, lean_box(0), v___x_2650_, v___f_2698_, v___x_2699_, v_hasTrace_2654_, v___x_2700_, v_options_2653_, v___x_2702_, v___y_2705_, v___f_2697_, v___x_2716_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2718_ = lean_apply_5(v___x_8763__overap_2717_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
return v___x_2718_;
}
v___jp_2719_:
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2723_, 0, v_a_2722_);
v___y_2704_ = v___y_2720_;
v___y_2705_ = v___y_2721_;
v_a_2706_ = v___x_2723_;
goto v___jp_2703_;
}
v___jp_2724_:
{
lean_object* v___x_2728_; 
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v_a_2727_);
v___y_2704_ = v___y_2725_;
v___y_2705_ = v___y_2726_;
v_a_2706_ = v___x_2728_;
goto v___jp_2703_;
}
v___jp_2729_:
{
uint8_t v___x_2733_; 
v___x_2733_ = l_Lean_Exception_isInterrupt(v_a_2732_);
if (v___x_2733_ == 0)
{
uint8_t v___x_2734_; 
lean_inc_ref(v_a_2732_);
v___x_2734_ = l_Lean_Exception_isRuntime(v_a_2732_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2735_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2736_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2667_, v_options_2653_, v___x_2736_);
if (v___x_2737_ == 0)
{
v___y_2725_ = v___y_2730_;
v___y_2726_ = v___y_2731_;
v_a_2727_ = v_a_2732_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_8782__overap_2739_; lean_object* v___x_2740_; 
lean_inc_ref(v_a_2732_);
v___x_2738_ = l_Lean_Exception_toMessageData(v_a_2732_);
lean_inc_ref(v_toMonadRef_2649_);
lean_inc_ref(v___x_2646_);
v___x_8782__overap_2739_ = l_Lean_addTrace___redArg(v___x_2646_, v___x_2647_, v_toMonadRef_2649_, v___x_2668_, v___x_2735_, v___x_2738_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2740_ = lean_apply_5(v___x_8782__overap_2739_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_dec_ref_known(v___x_2740_, 1);
v___y_2725_ = v___y_2730_;
v___y_2726_ = v___y_2731_;
v_a_2727_ = v_a_2732_;
goto v___jp_2724_;
}
else
{
lean_object* v_a_2741_; 
lean_dec_ref(v_a_2732_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___y_2725_ = v___y_2730_;
v___y_2726_ = v___y_2731_;
v_a_2727_ = v_a_2741_;
goto v___jp_2724_;
}
}
}
else
{
v___y_2725_ = v___y_2730_;
v___y_2726_ = v___y_2731_;
v_a_2727_ = v_a_2732_;
goto v___jp_2724_;
}
}
else
{
v___y_2725_ = v___y_2730_;
v___y_2726_ = v___y_2731_;
v_a_2727_ = v_a_2732_;
goto v___jp_2724_;
}
}
v___jp_2742_:
{
lean_object* v___x_2746_; double v___x_2747_; double v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_8823__overap_2753_; lean_object* v___x_2754_; 
v___x_2746_ = lean_io_get_num_heartbeats();
v___x_2747_ = lean_float_of_nat(v___y_2743_);
v___x_2748_ = lean_float_of_nat(v___x_2746_);
v___x_2749_ = lean_box_float(v___x_2747_);
v___x_2750_ = lean_box_float(v___x_2748_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v_a_2745_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
lean_inc_ref(v_toMonadRef_2649_);
v___x_8823__overap_2753_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2646_, v___x_2647_, v_toMonadRef_2649_, v___x_2668_, lean_box(0), v___x_2650_, v___f_2698_, v___x_2699_, v_hasTrace_2654_, v___x_2700_, v_options_2653_, v___x_2702_, v___y_2744_, v___f_2697_, v___x_2752_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2754_ = lean_apply_5(v___x_8823__overap_2753_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
return v___x_2754_;
}
v___jp_2755_:
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_a_2758_);
v___y_2743_ = v___y_2756_;
v___y_2744_ = v___y_2757_;
v_a_2745_ = v___x_2759_;
goto v___jp_2742_;
}
v___jp_2760_:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_a_2763_);
v___y_2743_ = v___y_2761_;
v___y_2744_ = v___y_2762_;
v_a_2745_ = v___x_2764_;
goto v___jp_2742_;
}
v___jp_2765_:
{
uint8_t v___x_2769_; 
v___x_2769_ = l_Lean_Exception_isInterrupt(v_a_2768_);
if (v___x_2769_ == 0)
{
uint8_t v___x_2770_; 
lean_inc_ref(v_a_2768_);
v___x_2770_ = l_Lean_Exception_isRuntime(v_a_2768_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2771_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2772_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2773_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2667_, v_options_2653_, v___x_2772_);
if (v___x_2773_ == 0)
{
v___y_2761_ = v___y_2766_;
v___y_2762_ = v___y_2767_;
v_a_2763_ = v_a_2768_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2774_; lean_object* v___x_8842__overap_2775_; lean_object* v___x_2776_; 
lean_inc_ref(v_a_2768_);
v___x_2774_ = l_Lean_Exception_toMessageData(v_a_2768_);
lean_inc_ref(v_toMonadRef_2649_);
lean_inc_ref(v___x_2646_);
v___x_8842__overap_2775_ = l_Lean_addTrace___redArg(v___x_2646_, v___x_2647_, v_toMonadRef_2649_, v___x_2668_, v___x_2771_, v___x_2774_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2776_ = lean_apply_5(v___x_8842__overap_2775_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_dec_ref_known(v___x_2776_, 1);
v___y_2761_ = v___y_2766_;
v___y_2762_ = v___y_2767_;
v_a_2763_ = v_a_2768_;
goto v___jp_2760_;
}
else
{
lean_object* v_a_2777_; 
lean_dec_ref(v_a_2768_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___y_2761_ = v___y_2766_;
v___y_2762_ = v___y_2767_;
v_a_2763_ = v_a_2777_;
goto v___jp_2760_;
}
}
}
else
{
v___y_2761_ = v___y_2766_;
v___y_2762_ = v___y_2767_;
v_a_2763_ = v_a_2768_;
goto v___jp_2760_;
}
}
else
{
v___y_2761_ = v___y_2766_;
v___y_2762_ = v___y_2767_;
v_a_2763_ = v_a_2768_;
goto v___jp_2760_;
}
}
v___jp_2778_:
{
lean_object* v___x_8741__overap_2779_; lean_object* v___x_2780_; 
lean_inc_ref(v___x_2646_);
v___x_8741__overap_2779_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2646_, v___x_2647_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2780_ = lean_apply_5(v___x_8741__overap_2779_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2783_ = l_Lean_Option_get___redArg(v___x_2651_, v_options_2653_, v___x_2782_);
v___x_2784_ = lean_unbox(v___x_2783_);
lean_dec(v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_io_mono_nanos_now();
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2786_ = lean_apply_5(v_k_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2789_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2667_, v_options_2653_, v___x_2789_);
if (v___x_2790_ == 0)
{
v___y_2720_ = v___x_2785_;
v___y_2721_ = v_a_2781_;
v_a_2722_ = v_a_2787_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_8803__overap_2792_; lean_object* v___x_2793_; 
lean_inc(v_a_2787_);
v___x_2791_ = l_Lean_MessageData_ofExpr(v_a_2787_);
lean_inc_ref(v_toMonadRef_2649_);
lean_inc_ref(v___x_2646_);
v___x_8803__overap_2792_ = l_Lean_addTrace___redArg(v___x_2646_, v___x_2647_, v_toMonadRef_2649_, v___x_2668_, v___x_2788_, v___x_2791_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2793_ = lean_apply_5(v___x_8803__overap_2792_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_dec_ref_known(v___x_2793_, 1);
v___y_2720_ = v___x_2785_;
v___y_2721_ = v_a_2781_;
v_a_2722_ = v_a_2787_;
goto v___jp_2719_;
}
else
{
lean_object* v_a_2794_; 
lean_dec(v_a_2787_);
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v___y_2730_ = v___x_2785_;
v___y_2731_ = v_a_2781_;
v_a_2732_ = v_a_2794_;
goto v___jp_2729_;
}
}
}
else
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2786_, 1);
v___y_2730_ = v___x_2785_;
v___y_2731_ = v_a_2781_;
v_a_2732_ = v_a_2795_;
goto v___jp_2729_;
}
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2797_ = lean_apply_5(v_k_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2800_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2801_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2667_, v_options_2653_, v___x_2800_);
if (v___x_2801_ == 0)
{
v___y_2756_ = v___x_2796_;
v___y_2757_ = v_a_2781_;
v_a_2758_ = v_a_2798_;
goto v___jp_2755_;
}
else
{
lean_object* v___x_2802_; lean_object* v___x_8863__overap_2803_; lean_object* v___x_2804_; 
lean_inc(v_a_2798_);
v___x_2802_ = l_Lean_MessageData_ofExpr(v_a_2798_);
lean_inc_ref(v_toMonadRef_2649_);
lean_inc_ref(v___x_2646_);
v___x_8863__overap_2803_ = l_Lean_addTrace___redArg(v___x_2646_, v___x_2647_, v_toMonadRef_2649_, v___x_2668_, v___x_2799_, v___x_2802_);
lean_inc(v_a_2605_);
lean_inc_ref(v_a_2604_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
v___x_2804_ = lean_apply_5(v___x_8863__overap_2803_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, lean_box(0));
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_dec_ref_known(v___x_2804_, 1);
v___y_2756_ = v___x_2796_;
v___y_2757_ = v_a_2781_;
v_a_2758_ = v_a_2798_;
goto v___jp_2755_;
}
else
{
lean_object* v_a_2805_; 
lean_dec(v_a_2798_);
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___y_2766_ = v___x_2796_;
v___y_2767_ = v_a_2781_;
v_a_2768_ = v_a_2805_;
goto v___jp_2765_;
}
}
}
else
{
lean_object* v_a_2806_; 
v_a_2806_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2797_, 1);
v___y_2766_ = v___x_2796_;
v___y_2767_ = v_a_2781_;
v_a_2768_ = v_a_2806_;
goto v___jp_2765_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec_ref(v___f_2697_);
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_k_2601_);
v_a_2807_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2780_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2780_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_f_2851_, lean_object* v_xs_2852_, lean_object* v_k_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2849_, v_inst_2850_, v_f_2851_, v_xs_2852_, v_k_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2860_, lean_object* v_00_u03b2_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_f_2864_, lean_object* v_xs_2865_, lean_object* v_k_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2862_, v_inst_2863_, v_f_2864_, v_xs_2865_, v_k_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2873_, lean_object* v_00_u03b2_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_f_2877_, lean_object* v_xs_2878_, lean_object* v_k_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2873_, v_00_u03b2_2874_, v_inst_2875_, v_inst_2876_, v_f_2877_, v_xs_2878_, v_k_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2886_, uint8_t v_allowLevelAssignments_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2887_, v_k_2886_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_a_2902_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2893_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2893_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2910_, lean_object* v_allowLevelAssignments_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2917_; lean_object* v_res_2918_; 
v_allowLevelAssignments_boxed_2917_ = lean_unbox(v_allowLevelAssignments_2911_);
v_res_2918_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2910_, v_allowLevelAssignments_boxed_2917_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2919_, lean_object* v_k_2920_, uint8_t v_allowLevelAssignments_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2920_, v_allowLevelAssignments_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2928_, lean_object* v_k_2929_, lean_object* v_allowLevelAssignments_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2936_; lean_object* v_res_2937_; 
v_allowLevelAssignments_boxed_2936_ = lean_unbox(v_allowLevelAssignments_2930_);
v_res_2937_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2928_, v_k_2929_, v_allowLevelAssignments_boxed_2936_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2938_, lean_object* v_xs_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2938_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v_fst_2947_; lean_object* v_snd_2948_; lean_object* v___x_2949_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v_fst_2947_ = lean_ctor_get(v_a_2946_, 0);
lean_inc(v_fst_2947_);
v_snd_2948_ = lean_ctor_get(v_a_2946_, 1);
lean_inc(v_snd_2948_);
lean_dec(v_a_2946_);
v___x_2949_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2947_, v_snd_2948_, v_xs_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
return v___x_2949_;
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_a_2950_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2945_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2945_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2958_, lean_object* v_xs_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2958_, v_xs_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v_xs_2959_);
return v_res_2965_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_unsigned_to_nat(32u);
v___x_2967_ = lean_mk_empty_array_with_capacity(v___x_2966_);
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
return v___x_2968_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2969_ = ((size_t)5ULL);
v___x_2970_ = lean_unsigned_to_nat(0u);
v___x_2971_ = lean_unsigned_to_nat(32u);
v___x_2972_ = lean_mk_empty_array_with_capacity(v___x_2971_);
v___x_2973_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2974_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v___x_2972_);
lean_ctor_set(v___x_2974_, 2, v___x_2970_);
lean_ctor_set(v___x_2974_, 3, v___x_2970_);
lean_ctor_set_usize(v___x_2974_, 4, v___x_2969_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2975_){
_start:
{
lean_object* v___x_2977_; lean_object* v_traceState_2978_; lean_object* v_traces_2979_; lean_object* v___x_2980_; lean_object* v_traceState_2981_; lean_object* v_env_2982_; lean_object* v_nextMacroScope_2983_; lean_object* v_ngen_2984_; lean_object* v_auxDeclNGen_2985_; lean_object* v_cache_2986_; lean_object* v_recordedDeps_2987_; lean_object* v_messages_2988_; lean_object* v_infoState_2989_; lean_object* v_snapshotTasks_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3009_; 
v___x_2977_ = lean_st_ref_get(v___y_2975_);
v_traceState_2978_ = lean_ctor_get(v___x_2977_, 4);
lean_inc_ref(v_traceState_2978_);
lean_dec(v___x_2977_);
v_traces_2979_ = lean_ctor_get(v_traceState_2978_, 0);
lean_inc_ref(v_traces_2979_);
lean_dec_ref(v_traceState_2978_);
v___x_2980_ = lean_st_ref_take(v___y_2975_);
v_traceState_2981_ = lean_ctor_get(v___x_2980_, 4);
v_env_2982_ = lean_ctor_get(v___x_2980_, 0);
v_nextMacroScope_2983_ = lean_ctor_get(v___x_2980_, 1);
v_ngen_2984_ = lean_ctor_get(v___x_2980_, 2);
v_auxDeclNGen_2985_ = lean_ctor_get(v___x_2980_, 3);
v_cache_2986_ = lean_ctor_get(v___x_2980_, 5);
v_recordedDeps_2987_ = lean_ctor_get(v___x_2980_, 6);
v_messages_2988_ = lean_ctor_get(v___x_2980_, 7);
v_infoState_2989_ = lean_ctor_get(v___x_2980_, 8);
v_snapshotTasks_2990_ = lean_ctor_get(v___x_2980_, 9);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2992_ = v___x_2980_;
v_isShared_2993_ = v_isSharedCheck_3009_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_snapshotTasks_2990_);
lean_inc(v_infoState_2989_);
lean_inc(v_messages_2988_);
lean_inc(v_recordedDeps_2987_);
lean_inc(v_cache_2986_);
lean_inc(v_traceState_2981_);
lean_inc(v_auxDeclNGen_2985_);
lean_inc(v_ngen_2984_);
lean_inc(v_nextMacroScope_2983_);
lean_inc(v_env_2982_);
lean_dec(v___x_2980_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3009_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
uint64_t v_tid_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3007_; 
v_tid_2994_ = lean_ctor_get_uint64(v_traceState_2981_, sizeof(void*)*1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_traceState_2981_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; 
v_unused_3008_ = lean_ctor_get(v_traceState_2981_, 0);
lean_dec(v_unused_3008_);
v___x_2996_ = v_traceState_2981_;
v_isShared_2997_ = v_isSharedCheck_3007_;
goto v_resetjp_2995_;
}
else
{
lean_dec(v_traceState_2981_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3007_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2998_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v___x_2998_);
v___x_3000_ = v___x_2996_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2998_);
lean_ctor_set_uint64(v_reuseFailAlloc_3006_, sizeof(void*)*1, v_tid_2994_);
v___x_3000_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3002_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 4, v___x_3000_);
v___x_3002_ = v___x_2992_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_env_2982_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_nextMacroScope_2983_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_ngen_2984_);
lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_auxDeclNGen_2985_);
lean_ctor_set(v_reuseFailAlloc_3005_, 4, v___x_3000_);
lean_ctor_set(v_reuseFailAlloc_3005_, 5, v_cache_2986_);
lean_ctor_set(v_reuseFailAlloc_3005_, 6, v_recordedDeps_2987_);
lean_ctor_set(v_reuseFailAlloc_3005_, 7, v_messages_2988_);
lean_ctor_set(v_reuseFailAlloc_3005_, 8, v_infoState_2989_);
lean_ctor_set(v_reuseFailAlloc_3005_, 9, v_snapshotTasks_2990_);
v___x_3002_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_st_ref_put(v___y_2975_, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v_traces_2979_);
return v___x_3004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3010_);
lean_dec(v___y_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3013_, lean_object* v_opt_3014_){
_start:
{
lean_object* v_name_3015_; lean_object* v_defValue_3016_; lean_object* v_map_3017_; lean_object* v___x_3018_; 
v_name_3015_ = lean_ctor_get(v_opt_3014_, 0);
v_defValue_3016_ = lean_ctor_get(v_opt_3014_, 1);
v_map_3017_ = lean_ctor_get(v_opts_3013_, 0);
v___x_3018_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3017_, v_name_3015_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_inc(v_defValue_3016_);
return v_defValue_3016_;
}
else
{
lean_object* v_val_3019_; 
v_val_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_val_3019_);
lean_dec_ref_known(v___x_3018_, 1);
if (lean_obj_tag(v_val_3019_) == 3)
{
lean_object* v_v_3020_; 
v_v_3020_ = lean_ctor_get(v_val_3019_, 0);
lean_inc(v_v_3020_);
lean_dec_ref_known(v_val_3019_, 1);
return v_v_3020_;
}
else
{
lean_dec(v_val_3019_);
lean_inc(v_defValue_3016_);
return v_defValue_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3021_, lean_object* v_opt_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3021_, v_opt_3022_);
lean_dec_ref(v_opt_3022_);
lean_dec_ref(v_opts_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3024_, lean_object* v_opt_3025_){
_start:
{
lean_object* v_name_3026_; lean_object* v_defValue_3027_; lean_object* v_map_3028_; lean_object* v___x_3029_; 
v_name_3026_ = lean_ctor_get(v_opt_3025_, 0);
v_defValue_3027_ = lean_ctor_get(v_opt_3025_, 1);
v_map_3028_ = lean_ctor_get(v_opts_3024_, 0);
v___x_3029_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3028_, v_name_3026_);
if (lean_obj_tag(v___x_3029_) == 0)
{
uint8_t v___x_3030_; 
v___x_3030_ = lean_unbox(v_defValue_3027_);
return v___x_3030_;
}
else
{
lean_object* v_val_3031_; 
v_val_3031_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_val_3031_);
lean_dec_ref_known(v___x_3029_, 1);
if (lean_obj_tag(v_val_3031_) == 1)
{
uint8_t v_v_3032_; 
v_v_3032_ = lean_ctor_get_uint8(v_val_3031_, 0);
lean_dec_ref_known(v_val_3031_, 0);
return v_v_3032_;
}
else
{
uint8_t v___x_3033_; 
lean_dec(v_val_3031_);
v___x_3033_ = lean_unbox(v_defValue_3027_);
return v___x_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3034_, lean_object* v_opt_3035_){
_start:
{
uint8_t v_res_3036_; lean_object* v_r_3037_; 
v_res_3036_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3034_, v_opt_3035_);
lean_dec_ref(v_opt_3035_);
lean_dec_ref(v_opts_3034_);
v_r_3037_ = lean_box(v_res_3036_);
return v_r_3037_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3038_){
_start:
{
if (lean_obj_tag(v_e_3038_) == 0)
{
uint8_t v___x_3039_; 
v___x_3039_ = 2;
return v___x_3039_;
}
else
{
lean_object* v_a_3040_; uint8_t v___x_3041_; 
v_a_3040_ = lean_ctor_get(v_e_3038_, 0);
v___x_3041_ = l_Lean_Expr_hasSyntheticSorry(v_a_3040_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; 
v___x_3042_ = 0;
return v___x_3042_;
}
else
{
uint8_t v___x_3043_; 
v___x_3043_ = 1;
return v___x_3043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3044_){
_start:
{
uint8_t v_res_3045_; lean_object* v_r_3046_; 
v_res_3045_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3044_);
lean_dec_ref(v_e_3044_);
v_r_3046_ = lean_box(v_res_3045_);
return v_r_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3047_, size_t v_i_3048_, lean_object* v_bs_3049_){
_start:
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_usize_dec_lt(v_i_3048_, v_sz_3047_);
if (v___x_3050_ == 0)
{
return v_bs_3049_;
}
else
{
lean_object* v_v_3051_; lean_object* v_msg_3052_; lean_object* v___x_3053_; lean_object* v_bs_x27_3054_; size_t v___x_3055_; size_t v___x_3056_; lean_object* v___x_3057_; 
v_v_3051_ = lean_array_uget_borrowed(v_bs_3049_, v_i_3048_);
v_msg_3052_ = lean_ctor_get(v_v_3051_, 1);
lean_inc_ref(v_msg_3052_);
v___x_3053_ = lean_unsigned_to_nat(0u);
v_bs_x27_3054_ = lean_array_uset(v_bs_3049_, v_i_3048_, v___x_3053_);
v___x_3055_ = ((size_t)1ULL);
v___x_3056_ = lean_usize_add(v_i_3048_, v___x_3055_);
v___x_3057_ = lean_array_uset(v_bs_x27_3054_, v_i_3048_, v_msg_3052_);
v_i_3048_ = v___x_3056_;
v_bs_3049_ = v___x_3057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3059_, lean_object* v_i_3060_, lean_object* v_bs_3061_){
_start:
{
size_t v_sz_boxed_3062_; size_t v_i_boxed_3063_; lean_object* v_res_3064_; 
v_sz_boxed_3062_ = lean_unbox_usize(v_sz_3059_);
lean_dec(v_sz_3059_);
v_i_boxed_3063_ = lean_unbox_usize(v_i_3060_);
lean_dec(v_i_3060_);
v_res_3064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3062_, v_i_boxed_3063_, v_bs_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3065_, lean_object* v_data_3066_, lean_object* v_ref_3067_, lean_object* v_msg_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_toCold_3074_; lean_object* v_currRecDepth_3075_; lean_object* v_ref_3076_; uint16_t v_optionFlags_3077_; uint8_t v_suppressElabErrors_3078_; uint8_t v_checkDeprecated_3079_; uint8_t v_isRecordingDeps_3080_; lean_object* v_ref_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v_traceState_3084_; lean_object* v_traces_3085_; lean_object* v___x_3086_; size_t v_sz_3087_; size_t v___x_3088_; lean_object* v___x_3089_; lean_object* v_msg_3090_; lean_object* v___x_3091_; lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3130_; 
v_toCold_3074_ = lean_ctor_get(v___y_3071_, 0);
v_currRecDepth_3075_ = lean_ctor_get(v___y_3071_, 1);
v_ref_3076_ = lean_ctor_get(v___y_3071_, 2);
v_optionFlags_3077_ = lean_ctor_get_uint16(v___y_3071_, sizeof(void*)*3);
v_suppressElabErrors_3078_ = lean_ctor_get_uint8(v___y_3071_, sizeof(void*)*3 + 2);
v_checkDeprecated_3079_ = lean_ctor_get_uint8(v___y_3071_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3080_ = lean_ctor_get_uint8(v___y_3071_, sizeof(void*)*3 + 4);
v_ref_3081_ = l_Lean_replaceRef(v_ref_3067_, v_ref_3076_);
lean_inc(v_currRecDepth_3075_);
lean_inc_ref(v_toCold_3074_);
v___x_3082_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3082_, 0, v_toCold_3074_);
lean_ctor_set(v___x_3082_, 1, v_currRecDepth_3075_);
lean_ctor_set(v___x_3082_, 2, v_ref_3081_);
lean_ctor_set_uint16(v___x_3082_, sizeof(void*)*3, v_optionFlags_3077_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*3 + 2, v_suppressElabErrors_3078_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*3 + 3, v_checkDeprecated_3079_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*3 + 4, v_isRecordingDeps_3080_);
v___x_3083_ = lean_st_ref_get(v___y_3072_);
v_traceState_3084_ = lean_ctor_get(v___x_3083_, 4);
lean_inc_ref(v_traceState_3084_);
lean_dec(v___x_3083_);
v_traces_3085_ = lean_ctor_get(v_traceState_3084_, 0);
lean_inc_ref(v_traces_3085_);
lean_dec_ref(v_traceState_3084_);
v___x_3086_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3085_);
lean_dec_ref(v_traces_3085_);
v_sz_3087_ = lean_array_size(v___x_3086_);
v___x_3088_ = ((size_t)0ULL);
v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3087_, v___x_3088_, v___x_3086_);
v_msg_3090_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3090_, 0, v_data_3066_);
lean_ctor_set(v_msg_3090_, 1, v_msg_3068_);
lean_ctor_set(v_msg_3090_, 2, v___x_3089_);
v___x_3091_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3090_, v___y_3069_, v___y_3070_, v___x_3082_, v___y_3072_);
lean_dec_ref_known(v___x_3082_, 3);
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3130_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3130_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v_traceState_3097_; lean_object* v_env_3098_; lean_object* v_nextMacroScope_3099_; lean_object* v_ngen_3100_; lean_object* v_auxDeclNGen_3101_; lean_object* v_cache_3102_; lean_object* v_recordedDeps_3103_; lean_object* v_messages_3104_; lean_object* v_infoState_3105_; lean_object* v_snapshotTasks_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3129_; 
v___x_3096_ = lean_st_ref_take(v___y_3072_);
v_traceState_3097_ = lean_ctor_get(v___x_3096_, 4);
v_env_3098_ = lean_ctor_get(v___x_3096_, 0);
v_nextMacroScope_3099_ = lean_ctor_get(v___x_3096_, 1);
v_ngen_3100_ = lean_ctor_get(v___x_3096_, 2);
v_auxDeclNGen_3101_ = lean_ctor_get(v___x_3096_, 3);
v_cache_3102_ = lean_ctor_get(v___x_3096_, 5);
v_recordedDeps_3103_ = lean_ctor_get(v___x_3096_, 6);
v_messages_3104_ = lean_ctor_get(v___x_3096_, 7);
v_infoState_3105_ = lean_ctor_get(v___x_3096_, 8);
v_snapshotTasks_3106_ = lean_ctor_get(v___x_3096_, 9);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3108_ = v___x_3096_;
v_isShared_3109_ = v_isSharedCheck_3129_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_snapshotTasks_3106_);
lean_inc(v_infoState_3105_);
lean_inc(v_messages_3104_);
lean_inc(v_recordedDeps_3103_);
lean_inc(v_cache_3102_);
lean_inc(v_traceState_3097_);
lean_inc(v_auxDeclNGen_3101_);
lean_inc(v_ngen_3100_);
lean_inc(v_nextMacroScope_3099_);
lean_inc(v_env_3098_);
lean_dec(v___x_3096_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3129_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
uint64_t v_tid_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3127_; 
v_tid_3110_ = lean_ctor_get_uint64(v_traceState_3097_, sizeof(void*)*1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_traceState_3097_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v_traceState_3097_, 0);
lean_dec(v_unused_3128_);
v___x_3112_ = v_traceState_3097_;
v_isShared_3113_ = v_isSharedCheck_3127_;
goto v_resetjp_3111_;
}
else
{
lean_dec(v_traceState_3097_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3127_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3114_ = lean_box(0);
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_ref_3067_);
lean_ctor_set(v___x_3115_, 1, v_a_3092_);
v___x_3116_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3065_, v___x_3115_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3116_);
v___x_3118_ = v___x_3112_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3116_);
lean_ctor_set_uint64(v_reuseFailAlloc_3126_, sizeof(void*)*1, v_tid_3110_);
v___x_3118_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3120_; 
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 4, v___x_3118_);
v___x_3120_ = v___x_3108_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_env_3098_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_nextMacroScope_3099_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_ngen_3100_);
lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_auxDeclNGen_3101_);
lean_ctor_set(v_reuseFailAlloc_3125_, 4, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3125_, 5, v_cache_3102_);
lean_ctor_set(v_reuseFailAlloc_3125_, 6, v_recordedDeps_3103_);
lean_ctor_set(v_reuseFailAlloc_3125_, 7, v_messages_3104_);
lean_ctor_set(v_reuseFailAlloc_3125_, 8, v_infoState_3105_);
lean_ctor_set(v_reuseFailAlloc_3125_, 9, v_snapshotTasks_3106_);
v___x_3120_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = lean_st_ref_put(v___y_3072_, v___x_3120_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3114_);
v___x_3123_ = v___x_3094_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3114_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3131_, lean_object* v_data_3132_, lean_object* v_ref_3133_, lean_object* v_msg_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3131_, v_data_3132_, v_ref_3133_, v_msg_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3141_){
_start:
{
if (lean_obj_tag(v_x_3141_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_a_3143_ = lean_ctor_get(v_x_3141_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_x_3141_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v_x_3141_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v_x_3141_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 1);
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
v_a_3151_ = lean_ctor_get(v_x_3141_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_x_3141_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v_x_3141_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v_x_3141_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 0);
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3159_);
return v_res_3161_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3162_; double v___x_3163_; 
v___x_3162_ = lean_unsigned_to_nat(0u);
v___x_3163_ = lean_float_of_nat(v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3166_ = l_Lean_stringToMessageData(v___x_3165_);
return v___x_3166_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3167_; double v___x_3168_; 
v___x_3167_ = lean_unsigned_to_nat(1000u);
v___x_3168_ = lean_float_of_nat(v___x_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3169_, uint8_t v_collapsed_3170_, lean_object* v_tag_3171_, lean_object* v_opts_3172_, uint8_t v_clsEnabled_3173_, lean_object* v_oldTraces_3174_, lean_object* v_msg_3175_, lean_object* v_resStartStop_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_fst_3182_; lean_object* v_snd_3183_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v_data_3187_; lean_object* v_fst_3198_; lean_object* v_snd_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; lean_object* v___y_3203_; lean_object* v_a_3204_; uint8_t v___y_3219_; double v___y_3251_; 
v_fst_3182_ = lean_ctor_get(v_resStartStop_3176_, 0);
lean_inc(v_fst_3182_);
v_snd_3183_ = lean_ctor_get(v_resStartStop_3176_, 1);
lean_inc(v_snd_3183_);
lean_dec_ref(v_resStartStop_3176_);
v_fst_3198_ = lean_ctor_get(v_snd_3183_, 0);
lean_inc(v_fst_3198_);
v_snd_3199_ = lean_ctor_get(v_snd_3183_, 1);
lean_inc(v_snd_3199_);
lean_dec(v_snd_3183_);
v___x_3200_ = l_Lean_trace_profiler;
v___x_3201_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3172_, v___x_3200_);
if (v___x_3201_ == 0)
{
v___y_3219_ = v___x_3201_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3256_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3257_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3172_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; double v___x_3260_; double v___x_3261_; double v___x_3262_; 
v___x_3258_ = l_Lean_trace_profiler_threshold;
v___x_3259_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3172_, v___x_3258_);
v___x_3260_ = lean_float_of_nat(v___x_3259_);
v___x_3261_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3262_ = lean_float_div(v___x_3260_, v___x_3261_);
v___y_3251_ = v___x_3262_;
goto v___jp_3250_;
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3264_; double v___x_3265_; 
v___x_3263_ = l_Lean_trace_profiler_threshold;
v___x_3264_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3172_, v___x_3263_);
v___x_3265_ = lean_float_of_nat(v___x_3264_);
v___y_3251_ = v___x_3265_;
goto v___jp_3250_;
}
}
v___jp_3184_:
{
lean_object* v___x_3188_; 
lean_inc(v___y_3186_);
v___x_3188_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3174_, v_data_3187_, v___y_3186_, v___y_3185_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v___x_3189_; 
lean_dec_ref_known(v___x_3188_, 1);
v___x_3189_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3182_);
return v___x_3189_;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_fst_3182_);
v_a_3190_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3188_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3188_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
v___jp_3202_:
{
uint8_t v_result_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; double v___x_3208_; lean_object* v_data_3209_; 
v_result_3205_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3182_);
v___x_3206_ = lean_box(v_result_3205_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
v___x_3208_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3171_);
lean_inc_ref(v___x_3207_);
lean_inc(v_cls_3169_);
v_data_3209_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3209_, 0, v_cls_3169_);
lean_ctor_set(v_data_3209_, 1, v___x_3207_);
lean_ctor_set(v_data_3209_, 2, v_tag_3171_);
lean_ctor_set_float(v_data_3209_, sizeof(void*)*3, v___x_3208_);
lean_ctor_set_float(v_data_3209_, sizeof(void*)*3 + 8, v___x_3208_);
lean_ctor_set_uint8(v_data_3209_, sizeof(void*)*3 + 16, v_collapsed_3170_);
if (v___x_3201_ == 0)
{
lean_dec_ref_known(v___x_3207_, 1);
lean_dec(v_snd_3199_);
lean_dec(v_fst_3198_);
lean_dec_ref(v_tag_3171_);
lean_dec(v_cls_3169_);
v___y_3185_ = v_a_3204_;
v___y_3186_ = v___y_3203_;
v_data_3187_ = v_data_3209_;
goto v___jp_3184_;
}
else
{
lean_object* v_data_3210_; double v___x_3211_; double v___x_3212_; 
lean_dec_ref_known(v_data_3209_, 3);
v_data_3210_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3210_, 0, v_cls_3169_);
lean_ctor_set(v_data_3210_, 1, v___x_3207_);
lean_ctor_set(v_data_3210_, 2, v_tag_3171_);
v___x_3211_ = lean_unbox_float(v_fst_3198_);
lean_dec(v_fst_3198_);
lean_ctor_set_float(v_data_3210_, sizeof(void*)*3, v___x_3211_);
v___x_3212_ = lean_unbox_float(v_snd_3199_);
lean_dec(v_snd_3199_);
lean_ctor_set_float(v_data_3210_, sizeof(void*)*3 + 8, v___x_3212_);
lean_ctor_set_uint8(v_data_3210_, sizeof(void*)*3 + 16, v_collapsed_3170_);
v___y_3185_ = v_a_3204_;
v___y_3186_ = v___y_3203_;
v_data_3187_ = v_data_3210_;
goto v___jp_3184_;
}
}
v___jp_3213_:
{
lean_object* v_ref_3214_; lean_object* v___x_3215_; 
v_ref_3214_ = lean_ctor_get(v___y_3179_, 2);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v_fst_3182_);
v___x_3215_ = lean_apply_6(v_msg_3175_, v_fst_3182_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, lean_box(0));
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v___y_3203_ = v_ref_3214_;
v_a_3204_ = v_a_3216_;
goto v___jp_3202_;
}
else
{
lean_object* v___x_3217_; 
lean_dec_ref_known(v___x_3215_, 1);
v___x_3217_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3203_ = v_ref_3214_;
v_a_3204_ = v___x_3217_;
goto v___jp_3202_;
}
}
v___jp_3218_:
{
if (v_clsEnabled_3173_ == 0)
{
if (v___y_3219_ == 0)
{
lean_object* v___x_3220_; lean_object* v_traceState_3221_; lean_object* v_env_3222_; lean_object* v_nextMacroScope_3223_; lean_object* v_ngen_3224_; lean_object* v_auxDeclNGen_3225_; lean_object* v_cache_3226_; lean_object* v_recordedDeps_3227_; lean_object* v_messages_3228_; lean_object* v_infoState_3229_; lean_object* v_snapshotTasks_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v_snd_3199_);
lean_dec(v_fst_3198_);
lean_dec_ref(v_msg_3175_);
lean_dec_ref(v_tag_3171_);
lean_dec(v_cls_3169_);
v___x_3220_ = lean_st_ref_take(v___y_3180_);
v_traceState_3221_ = lean_ctor_get(v___x_3220_, 4);
v_env_3222_ = lean_ctor_get(v___x_3220_, 0);
v_nextMacroScope_3223_ = lean_ctor_get(v___x_3220_, 1);
v_ngen_3224_ = lean_ctor_get(v___x_3220_, 2);
v_auxDeclNGen_3225_ = lean_ctor_get(v___x_3220_, 3);
v_cache_3226_ = lean_ctor_get(v___x_3220_, 5);
v_recordedDeps_3227_ = lean_ctor_get(v___x_3220_, 6);
v_messages_3228_ = lean_ctor_get(v___x_3220_, 7);
v_infoState_3229_ = lean_ctor_get(v___x_3220_, 8);
v_snapshotTasks_3230_ = lean_ctor_get(v___x_3220_, 9);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3232_ = v___x_3220_;
v_isShared_3233_ = v_isSharedCheck_3249_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_snapshotTasks_3230_);
lean_inc(v_infoState_3229_);
lean_inc(v_messages_3228_);
lean_inc(v_recordedDeps_3227_);
lean_inc(v_cache_3226_);
lean_inc(v_traceState_3221_);
lean_inc(v_auxDeclNGen_3225_);
lean_inc(v_ngen_3224_);
lean_inc(v_nextMacroScope_3223_);
lean_inc(v_env_3222_);
lean_dec(v___x_3220_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3249_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
uint64_t v_tid_3234_; lean_object* v_traces_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3248_; 
v_tid_3234_ = lean_ctor_get_uint64(v_traceState_3221_, sizeof(void*)*1);
v_traces_3235_ = lean_ctor_get(v_traceState_3221_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_traceState_3221_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3237_ = v_traceState_3221_;
v_isShared_3238_ = v_isSharedCheck_3248_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_traces_3235_);
lean_dec(v_traceState_3221_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3248_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3239_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3174_, v_traces_3235_);
lean_dec_ref(v_traces_3235_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3239_);
v___x_3241_ = v___x_3237_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3239_);
lean_ctor_set_uint64(v_reuseFailAlloc_3247_, sizeof(void*)*1, v_tid_3234_);
v___x_3241_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3243_; 
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 4, v___x_3241_);
v___x_3243_ = v___x_3232_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_env_3222_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_nextMacroScope_3223_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_ngen_3224_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_auxDeclNGen_3225_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3246_, 5, v_cache_3226_);
lean_ctor_set(v_reuseFailAlloc_3246_, 6, v_recordedDeps_3227_);
lean_ctor_set(v_reuseFailAlloc_3246_, 7, v_messages_3228_);
lean_ctor_set(v_reuseFailAlloc_3246_, 8, v_infoState_3229_);
lean_ctor_set(v_reuseFailAlloc_3246_, 9, v_snapshotTasks_3230_);
v___x_3243_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = lean_st_ref_put(v___y_3180_, v___x_3243_);
v___x_3245_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3182_);
return v___x_3245_;
}
}
}
}
}
else
{
goto v___jp_3213_;
}
}
else
{
goto v___jp_3213_;
}
}
v___jp_3250_:
{
double v___x_3252_; double v___x_3253_; double v___x_3254_; uint8_t v___x_3255_; 
v___x_3252_ = lean_unbox_float(v_snd_3199_);
v___x_3253_ = lean_unbox_float(v_fst_3198_);
v___x_3254_ = lean_float_sub(v___x_3252_, v___x_3253_);
v___x_3255_ = lean_float_decLt(v___y_3251_, v___x_3254_);
v___y_3219_ = v___x_3255_;
goto v___jp_3218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3266_, lean_object* v_collapsed_3267_, lean_object* v_tag_3268_, lean_object* v_opts_3269_, lean_object* v_clsEnabled_3270_, lean_object* v_oldTraces_3271_, lean_object* v_msg_3272_, lean_object* v_resStartStop_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
uint8_t v_collapsed_boxed_3279_; uint8_t v_clsEnabled_boxed_3280_; lean_object* v_res_3281_; 
v_collapsed_boxed_3279_ = lean_unbox(v_collapsed_3267_);
v_clsEnabled_boxed_3280_ = lean_unbox(v_clsEnabled_3270_);
v_res_3281_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3266_, v_collapsed_boxed_3279_, v_tag_3268_, v_opts_3269_, v_clsEnabled_boxed_3280_, v_oldTraces_3271_, v_msg_3272_, v_resStartStop_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec_ref(v_opts_3269_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
if (lean_obj_tag(v_a_3282_) == 0)
{
lean_object* v___x_3284_; 
v___x_3284_ = l_List_reverse___redArg(v_a_3283_);
return v___x_3284_;
}
else
{
lean_object* v_head_3285_; lean_object* v_tail_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3295_; 
v_head_3285_ = lean_ctor_get(v_a_3282_, 0);
v_tail_3286_ = lean_ctor_get(v_a_3282_, 1);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_a_3282_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3288_ = v_a_3282_;
v_isShared_3289_ = v_isSharedCheck_3295_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_tail_3286_);
lean_inc(v_head_3285_);
lean_dec(v_a_3282_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3295_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3290_ = l_Lean_MessageData_ofExpr(v_head_3285_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 1, v_a_3283_);
lean_ctor_set(v___x_3288_, 0, v___x_3290_);
v___x_3292_ = v___x_3288_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_a_3283_);
v___x_3292_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
v_a_3282_ = v_tail_3286_;
v_a_3283_ = v___x_3292_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3296_, lean_object* v_xs_3297_, lean_object* v_x_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3305_ = l_Lean_MessageData_ofName(v_f_3296_);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_array_to_list(v_xs_3297_);
v___x_3310_ = lean_box(0);
v___x_3311_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3309_, v___x_3310_);
v___x_3312_ = l_Lean_MessageData_ofList(v___x_3311_);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3308_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3315_, lean_object* v_xs_3316_, lean_object* v_x_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3315_, v_xs_3316_, v_x_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec_ref(v_x_3317_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3326_, lean_object* v_msg_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_ref_3333_; lean_object* v___x_3334_; lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3380_; 
v_ref_3333_ = lean_ctor_get(v___y_3330_, 2);
v___x_3334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3380_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3380_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v_traceState_3340_; lean_object* v_env_3341_; lean_object* v_nextMacroScope_3342_; lean_object* v_ngen_3343_; lean_object* v_auxDeclNGen_3344_; lean_object* v_cache_3345_; lean_object* v_recordedDeps_3346_; lean_object* v_messages_3347_; lean_object* v_infoState_3348_; lean_object* v_snapshotTasks_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3379_; 
v___x_3339_ = lean_st_ref_take(v___y_3331_);
v_traceState_3340_ = lean_ctor_get(v___x_3339_, 4);
v_env_3341_ = lean_ctor_get(v___x_3339_, 0);
v_nextMacroScope_3342_ = lean_ctor_get(v___x_3339_, 1);
v_ngen_3343_ = lean_ctor_get(v___x_3339_, 2);
v_auxDeclNGen_3344_ = lean_ctor_get(v___x_3339_, 3);
v_cache_3345_ = lean_ctor_get(v___x_3339_, 5);
v_recordedDeps_3346_ = lean_ctor_get(v___x_3339_, 6);
v_messages_3347_ = lean_ctor_get(v___x_3339_, 7);
v_infoState_3348_ = lean_ctor_get(v___x_3339_, 8);
v_snapshotTasks_3349_ = lean_ctor_get(v___x_3339_, 9);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3351_ = v___x_3339_;
v_isShared_3352_ = v_isSharedCheck_3379_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_snapshotTasks_3349_);
lean_inc(v_infoState_3348_);
lean_inc(v_messages_3347_);
lean_inc(v_recordedDeps_3346_);
lean_inc(v_cache_3345_);
lean_inc(v_traceState_3340_);
lean_inc(v_auxDeclNGen_3344_);
lean_inc(v_ngen_3343_);
lean_inc(v_nextMacroScope_3342_);
lean_inc(v_env_3341_);
lean_dec(v___x_3339_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3379_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
uint64_t v_tid_3353_; lean_object* v_traces_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3378_; 
v_tid_3353_ = lean_ctor_get_uint64(v_traceState_3340_, sizeof(void*)*1);
v_traces_3354_ = lean_ctor_get(v_traceState_3340_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_traceState_3340_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3356_ = v_traceState_3340_;
v_isShared_3357_ = v_isSharedCheck_3378_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_traces_3354_);
lean_dec(v_traceState_3340_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3378_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; double v___x_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3358_ = lean_box(0);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3361_ = 0;
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3363_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3363_, 0, v_cls_3326_);
lean_ctor_set(v___x_3363_, 1, v___x_3359_);
lean_ctor_set(v___x_3363_, 2, v___x_3362_);
lean_ctor_set_float(v___x_3363_, sizeof(void*)*3, v___x_3360_);
lean_ctor_set_float(v___x_3363_, sizeof(void*)*3 + 8, v___x_3360_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*3 + 16, v___x_3361_);
v___x_3364_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3365_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v_a_3335_);
lean_ctor_set(v___x_3365_, 2, v___x_3364_);
lean_inc(v_ref_3333_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_ref_3333_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_PersistentArray_push___redArg(v_traces_3354_, v___x_3366_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3367_);
v___x_3369_ = v___x_3356_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3367_);
lean_ctor_set_uint64(v_reuseFailAlloc_3377_, sizeof(void*)*1, v_tid_3353_);
v___x_3369_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 4, v___x_3369_);
v___x_3371_ = v___x_3351_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_env_3341_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_nextMacroScope_3342_);
lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_ngen_3343_);
lean_ctor_set(v_reuseFailAlloc_3376_, 3, v_auxDeclNGen_3344_);
lean_ctor_set(v_reuseFailAlloc_3376_, 4, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3376_, 5, v_cache_3345_);
lean_ctor_set(v_reuseFailAlloc_3376_, 6, v_recordedDeps_3346_);
lean_ctor_set(v_reuseFailAlloc_3376_, 7, v_messages_3347_);
lean_ctor_set(v_reuseFailAlloc_3376_, 8, v_infoState_3348_);
lean_ctor_set(v_reuseFailAlloc_3376_, 9, v_snapshotTasks_3349_);
v___x_3371_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = lean_st_ref_put(v___y_3331_, v___x_3371_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3358_);
v___x_3374_ = v___x_3337_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3358_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3381_, lean_object* v_msg_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3381_, v_msg_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3389_, lean_object* v_xs_3390_, lean_object* v_k_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_toCold_3397_; lean_object* v_options_3398_; uint8_t v_hasTrace_3399_; 
v_toCold_3397_ = lean_ctor_get(v_a_3394_, 0);
v_options_3398_ = lean_ctor_get(v_toCold_3397_, 2);
v_hasTrace_3399_ = lean_ctor_get_uint8(v_options_3398_, sizeof(void*)*1);
if (v_hasTrace_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec_ref(v_xs_3390_);
lean_dec(v_f_3389_);
lean_inc(v_a_3395_);
lean_inc_ref(v_a_3394_);
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
v___x_3400_ = lean_apply_5(v_k_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, lean_box(0));
return v___x_3400_;
}
else
{
lean_object* v_inheritedTraceOptions_3401_; lean_object* v___f_3402_; lean_object* v___y_3404_; lean_object* v_a_3405_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v_a_3437_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v_a_3452_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v_a_3457_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v_a_3462_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v_a_3474_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v_a_3486_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v_a_3491_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v_a_3496_; 
v_inheritedTraceOptions_3401_ = lean_ctor_get(v_toCold_3397_, 11);
v___f_3402_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3402_, 0, v_f_3389_);
lean_closure_set(v___f_3402_, 1, v_xs_3390_);
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3431_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3432_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3433_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3401_, v_options_3398_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3530_ = l_Lean_trace_profiler;
v___x_3531_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3398_, v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; 
lean_dec_ref(v___f_3402_);
lean_inc(v_a_3395_);
lean_inc_ref(v_a_3394_);
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
v___x_3532_ = lean_apply_5(v_k_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, lean_box(0));
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
v___x_3534_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3535_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3536_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3401_, v_options_3398_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_dec(v_a_3533_);
return v___x_3532_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3532_, 1);
lean_inc(v_a_3533_);
v___x_3537_ = l_Lean_MessageData_ofExpr(v_a_3533_);
v___x_3538_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3534_, v___x_3537_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v___x_3538_, 0);
lean_dec(v_unused_3546_);
v___x_3540_ = v___x_3538_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_dec(v___x_3538_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v_a_3533_);
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3533_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v_a_3533_);
v_a_3547_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3538_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3538_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
lean_inc(v_a_3547_);
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
v___y_3404_ = v___x_3552_;
v_a_3405_ = v_a_3547_;
goto v___jp_3403_;
}
}
}
}
}
else
{
lean_object* v_a_3555_; 
v_a_3555_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3555_);
v___y_3404_ = v___x_3532_;
v_a_3405_ = v_a_3555_;
goto v___jp_3403_;
}
}
else
{
goto v___jp_3505_;
}
}
else
{
goto v___jp_3505_;
}
v___jp_3403_:
{
uint8_t v___x_3406_; 
v___x_3406_ = l_Lean_Exception_isInterrupt(v_a_3405_);
if (v___x_3406_ == 0)
{
uint8_t v___x_3407_; 
lean_inc_ref(v_a_3405_);
v___x_3407_ = l_Lean_Exception_isRuntime(v_a_3405_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
lean_dec_ref(v___y_3404_);
v___x_3408_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3409_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3410_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3401_, v_options_3398_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3411_, 0, v_a_3405_);
return v___x_3411_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_inc_ref(v_a_3405_);
v___x_3412_ = l_Lean_Exception_toMessageData(v_a_3405_);
v___x_3413_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3408_, v___x_3412_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; 
v_unused_3421_ = lean_ctor_get(v___x_3413_, 0);
lean_dec(v_unused_3421_);
v___x_3415_ = v___x_3413_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_dec(v___x_3413_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set_tag(v___x_3415_, 1);
lean_ctor_set(v___x_3415_, 0, v_a_3405_);
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3405_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec_ref(v_a_3405_);
v_a_3422_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3413_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3413_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3405_);
return v___y_3404_;
}
}
else
{
lean_dec_ref(v_a_3405_);
return v___y_3404_;
}
}
v___jp_3434_:
{
lean_object* v___x_3438_; double v___x_3439_; double v___x_3440_; double v___x_3441_; double v___x_3442_; double v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3438_ = lean_io_mono_nanos_now();
v___x_3439_ = lean_float_of_nat(v___y_3435_);
v___x_3440_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3441_ = lean_float_div(v___x_3439_, v___x_3440_);
v___x_3442_ = lean_float_of_nat(v___x_3438_);
v___x_3443_ = lean_float_div(v___x_3442_, v___x_3440_);
v___x_3444_ = lean_box_float(v___x_3441_);
v___x_3445_ = lean_box_float(v___x_3443_);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3444_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_a_3437_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3430_, v_hasTrace_3399_, v___x_3431_, v_options_3398_, v___x_3433_, v___y_3436_, v___f_3402_, v___x_3447_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
return v___x_3448_;
}
v___jp_3449_:
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v_a_3452_);
v___y_3435_ = v___y_3450_;
v___y_3436_ = v___y_3451_;
v_a_3437_ = v___x_3453_;
goto v___jp_3434_;
}
v___jp_3454_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v_a_3457_);
v___y_3435_ = v___y_3455_;
v___y_3436_ = v___y_3456_;
v_a_3437_ = v___x_3458_;
goto v___jp_3434_;
}
v___jp_3459_:
{
uint8_t v___x_3463_; 
v___x_3463_ = l_Lean_Exception_isInterrupt(v_a_3462_);
if (v___x_3463_ == 0)
{
uint8_t v___x_3464_; 
lean_inc_ref(v_a_3462_);
v___x_3464_ = l_Lean_Exception_isRuntime(v_a_3462_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v___x_3465_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3466_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3467_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3401_, v_options_3398_, v___x_3466_);
if (v___x_3467_ == 0)
{
v___y_3455_ = v___y_3460_;
v___y_3456_ = v___y_3461_;
v_a_3457_ = v_a_3462_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
lean_inc_ref(v_a_3462_);
v___x_3468_ = l_Lean_Exception_toMessageData(v_a_3462_);
v___x_3469_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3465_, v___x_3468_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_dec_ref_known(v___x_3469_, 1);
v___y_3455_ = v___y_3460_;
v___y_3456_ = v___y_3461_;
v_a_3457_ = v_a_3462_;
goto v___jp_3454_;
}
else
{
lean_object* v_a_3470_; 
lean_dec_ref(v_a_3462_);
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v___y_3455_ = v___y_3460_;
v___y_3456_ = v___y_3461_;
v_a_3457_ = v_a_3470_;
goto v___jp_3454_;
}
}
}
else
{
v___y_3455_ = v___y_3460_;
v___y_3456_ = v___y_3461_;
v_a_3457_ = v_a_3462_;
goto v___jp_3454_;
}
}
else
{
v___y_3455_ = v___y_3460_;
v___y_3456_ = v___y_3461_;
v_a_3457_ = v_a_3462_;
goto v___jp_3454_;
}
}
v___jp_3471_:
{
lean_object* v___x_3475_; double v___x_3476_; double v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3475_ = lean_io_get_num_heartbeats();
v___x_3476_ = lean_float_of_nat(v___y_3473_);
v___x_3477_ = lean_float_of_nat(v___x_3475_);
v___x_3478_ = lean_box_float(v___x_3476_);
v___x_3479_ = lean_box_float(v___x_3477_);
v___x_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v_a_3474_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3430_, v_hasTrace_3399_, v___x_3431_, v_options_3398_, v___x_3433_, v___y_3472_, v___f_3402_, v___x_3481_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
return v___x_3482_;
}
v___jp_3483_:
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_a_3486_);
v___y_3472_ = v___y_3484_;
v___y_3473_ = v___y_3485_;
v_a_3474_ = v___x_3487_;
goto v___jp_3471_;
}
v___jp_3488_:
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v_a_3491_);
v___y_3472_ = v___y_3489_;
v___y_3473_ = v___y_3490_;
v_a_3474_ = v___x_3492_;
goto v___jp_3471_;
}
v___jp_3493_:
{
uint8_t v___x_3497_; 
v___x_3497_ = l_Lean_Exception_isInterrupt(v_a_3496_);
if (v___x_3497_ == 0)
{
uint8_t v___x_3498_; 
lean_inc_ref(v_a_3496_);
v___x_3498_ = l_Lean_Exception_isRuntime(v_a_3496_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v___x_3499_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3500_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3401_, v_options_3398_, v___x_3500_);
if (v___x_3501_ == 0)
{
v___y_3489_ = v___y_3494_;
v___y_3490_ = v___y_3495_;
v_a_3491_ = v_a_3496_;
goto v___jp_3488_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
lean_inc_ref(v_a_3496_);
v___x_3502_ = l_Lean_Exception_toMessageData(v_a_3496_);
v___x_3503_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3499_, v___x_3502_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_dec_ref_known(v___x_3503_, 1);
v___y_3489_ = v___y_3494_;
v___y_3490_ = v___y_3495_;
v_a_3491_ = v_a_3496_;
goto v___jp_3488_;
}
else
{
lean_object* v_a_3504_; 
lean_dec_ref(v_a_3496_);
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___y_3489_ = v___y_3494_;
v___y_3490_ = v___y_3495_;
v_a_3491_ = v_a_3504_;
goto v___jp_3488_;
}
}
}
else
{
v___y_3489_ = v___y_3494_;
v___y_3490_ = v___y_3495_;
v_a_3491_ = v_a_3496_;
goto v___jp_3488_;
}
}
else
{
v___y_3489_ = v___y_3494_;
v___y_3490_ = v___y_3495_;
v_a_3491_ = v_a_3496_;
goto v___jp_3488_;
}
}
v___jp_3505_:
{
lean_object* v___x_3506_; lean_object* v_a_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3506_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3395_);
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
lean_dec_ref(v___x_3506_);
v___x_3508_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3509_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3398_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = lean_io_mono_nanos_now();
lean_inc(v_a_3395_);
lean_inc_ref(v_a_3394_);
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
v___x_3511_ = lean_apply_5(v_k_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, lean_box(0));
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3514_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3515_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3401_, v_options_3398_, v___x_3514_);
if (v___x_3515_ == 0)
{
v___y_3450_ = v___x_3510_;
v___y_3451_ = v_a_3507_;
v_a_3452_ = v_a_3512_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_inc(v_a_3512_);
v___x_3516_ = l_Lean_MessageData_ofExpr(v_a_3512_);
v___x_3517_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3513_, v___x_3516_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_dec_ref_known(v___x_3517_, 1);
v___y_3450_ = v___x_3510_;
v___y_3451_ = v_a_3507_;
v_a_3452_ = v_a_3512_;
goto v___jp_3449_;
}
else
{
lean_object* v_a_3518_; 
lean_dec(v_a_3512_);
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___y_3460_ = v___x_3510_;
v___y_3461_ = v_a_3507_;
v_a_3462_ = v_a_3518_;
goto v___jp_3459_;
}
}
}
else
{
lean_object* v_a_3519_; 
v_a_3519_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3511_, 1);
v___y_3460_ = v___x_3510_;
v___y_3461_ = v_a_3507_;
v_a_3462_ = v_a_3519_;
goto v___jp_3459_;
}
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3395_);
lean_inc_ref(v_a_3394_);
lean_inc(v_a_3393_);
lean_inc_ref(v_a_3392_);
v___x_3521_ = lean_apply_5(v_k_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, lean_box(0));
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3524_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3525_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3401_, v_options_3398_, v___x_3524_);
if (v___x_3525_ == 0)
{
v___y_3484_ = v_a_3507_;
v___y_3485_ = v___x_3520_;
v_a_3486_ = v_a_3522_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_inc(v_a_3522_);
v___x_3526_ = l_Lean_MessageData_ofExpr(v_a_3522_);
v___x_3527_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3523_, v___x_3526_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_dec_ref_known(v___x_3527_, 1);
v___y_3484_ = v_a_3507_;
v___y_3485_ = v___x_3520_;
v_a_3486_ = v_a_3522_;
goto v___jp_3483_;
}
else
{
lean_object* v_a_3528_; 
lean_dec(v_a_3522_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref_known(v___x_3527_, 1);
v___y_3494_ = v_a_3507_;
v___y_3495_ = v___x_3520_;
v_a_3496_ = v_a_3528_;
goto v___jp_3493_;
}
}
}
else
{
lean_object* v_a_3529_; 
v_a_3529_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3521_, 1);
v___y_3494_ = v_a_3507_;
v___y_3495_ = v___x_3520_;
v_a_3496_ = v_a_3529_;
goto v___jp_3493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3556_, lean_object* v_xs_3557_, lean_object* v_k_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3556_, v_xs_3557_, v_k_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3565_, lean_object* v_xs_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v___f_3572_; uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
lean_inc_ref(v_xs_3566_);
lean_inc(v_constName_3565_);
v___f_3572_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3572_, 0, v_constName_3565_);
lean_closure_set(v___f_3572_, 1, v_xs_3566_);
v___x_3573_ = 0;
v___x_3574_ = lean_box(v___x_3573_);
v___x_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3575_, 0, lean_box(0));
lean_closure_set(v___x_3575_, 1, v___f_3572_);
lean_closure_set(v___x_3575_, 2, v___x_3574_);
v___x_3576_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3565_, v_xs_3566_, v___x_3575_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3577_, lean_object* v_xs_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_Meta_mkAppM(v_constName_3577_, v_xs_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3588_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3597_, lean_object* v_x_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3598_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3605_, lean_object* v_x_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3605_, v_x_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3613_, lean_object* v_xs_3614_, lean_object* v_x_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3621_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3622_ = l_Lean_MessageData_ofExpr(v_f_3613_);
v___x_3623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3621_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3623_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = lean_array_to_list(v_xs_3614_);
v___x_3627_ = lean_box(0);
v___x_3628_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3626_, v___x_3627_);
v___x_3629_ = l_Lean_MessageData_ofList(v___x_3628_);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3625_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3632_, lean_object* v_xs_3633_, lean_object* v_x_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3632_, v_xs_3633_, v_x_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v_x_3634_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3641_, lean_object* v_xs_3642_, lean_object* v_k_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_toCold_3649_; lean_object* v_options_3650_; uint8_t v_hasTrace_3651_; 
v_toCold_3649_ = lean_ctor_get(v_a_3646_, 0);
v_options_3650_ = lean_ctor_get(v_toCold_3649_, 2);
v_hasTrace_3651_ = lean_ctor_get_uint8(v_options_3650_, sizeof(void*)*1);
if (v_hasTrace_3651_ == 0)
{
lean_object* v___x_3652_; 
lean_dec_ref(v_xs_3642_);
lean_dec_ref(v_f_3641_);
lean_inc(v_a_3647_);
lean_inc_ref(v_a_3646_);
lean_inc(v_a_3645_);
lean_inc_ref(v_a_3644_);
v___x_3652_ = lean_apply_5(v_k_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, lean_box(0));
return v___x_3652_;
}
else
{
lean_object* v_inheritedTraceOptions_3653_; lean_object* v___f_3654_; lean_object* v___y_3656_; lean_object* v_a_3657_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v_a_3689_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v_a_3704_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v_a_3709_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v_a_3714_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v_a_3726_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v_a_3738_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v_a_3743_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v_a_3748_; 
v_inheritedTraceOptions_3653_ = lean_ctor_get(v_toCold_3649_, 11);
v___f_3654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3654_, 0, v_f_3641_);
lean_closure_set(v___f_3654_, 1, v_xs_3642_);
v___x_3682_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3683_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3684_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3685_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3653_, v_options_3650_, v___x_3684_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3782_ = l_Lean_trace_profiler;
v___x_3783_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3650_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
lean_dec_ref(v___f_3654_);
lean_inc(v_a_3647_);
lean_inc_ref(v_a_3646_);
lean_inc(v_a_3645_);
lean_inc_ref(v_a_3644_);
v___x_3784_ = lean_apply_5(v_k_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, lean_box(0));
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
v___x_3786_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3787_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3788_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3653_, v_options_3650_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_dec(v_a_3785_);
return v___x_3784_;
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_dec_ref_known(v___x_3784_, 1);
lean_inc(v_a_3785_);
v___x_3789_ = l_Lean_MessageData_ofExpr(v_a_3785_);
v___x_3790_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3786_, v___x_3789_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; 
v_unused_3798_ = lean_ctor_get(v___x_3790_, 0);
lean_dec(v_unused_3798_);
v___x_3792_ = v___x_3790_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v___x_3790_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v_a_3785_);
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3785_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec(v_a_3785_);
v_a_3799_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3790_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3790_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
lean_inc(v_a_3799_);
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
v___y_3656_ = v___x_3804_;
v_a_3657_ = v_a_3799_;
goto v___jp_3655_;
}
}
}
}
}
else
{
lean_object* v_a_3807_; 
v_a_3807_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3807_);
v___y_3656_ = v___x_3784_;
v_a_3657_ = v_a_3807_;
goto v___jp_3655_;
}
}
else
{
goto v___jp_3757_;
}
}
else
{
goto v___jp_3757_;
}
v___jp_3655_:
{
uint8_t v___x_3658_; 
v___x_3658_ = l_Lean_Exception_isInterrupt(v_a_3657_);
if (v___x_3658_ == 0)
{
uint8_t v___x_3659_; 
lean_inc_ref(v_a_3657_);
v___x_3659_ = l_Lean_Exception_isRuntime(v_a_3657_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
lean_dec_ref(v___y_3656_);
v___x_3660_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3661_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3662_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3653_, v_options_3650_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3663_, 0, v_a_3657_);
return v___x_3663_;
}
else
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
lean_inc_ref(v_a_3657_);
v___x_3664_ = l_Lean_Exception_toMessageData(v_a_3657_);
v___x_3665_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3660_, v___x_3664_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3672_ == 0)
{
lean_object* v_unused_3673_; 
v_unused_3673_ = lean_ctor_get(v___x_3665_, 0);
lean_dec(v_unused_3673_);
v___x_3667_ = v___x_3665_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_dec(v___x_3665_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 1);
lean_ctor_set(v___x_3667_, 0, v_a_3657_);
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3657_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref(v_a_3657_);
v_a_3674_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3665_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3665_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3657_);
return v___y_3656_;
}
}
else
{
lean_dec_ref(v_a_3657_);
return v___y_3656_;
}
}
v___jp_3686_:
{
lean_object* v___x_3690_; double v___x_3691_; double v___x_3692_; double v___x_3693_; double v___x_3694_; double v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3690_ = lean_io_mono_nanos_now();
v___x_3691_ = lean_float_of_nat(v___y_3688_);
v___x_3692_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3693_ = lean_float_div(v___x_3691_, v___x_3692_);
v___x_3694_ = lean_float_of_nat(v___x_3690_);
v___x_3695_ = lean_float_div(v___x_3694_, v___x_3692_);
v___x_3696_ = lean_box_float(v___x_3693_);
v___x_3697_ = lean_box_float(v___x_3695_);
v___x_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3696_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v_a_3689_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3682_, v_hasTrace_3651_, v___x_3683_, v_options_3650_, v___x_3685_, v___y_3687_, v___f_3654_, v___x_3699_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
return v___x_3700_;
}
v___jp_3701_:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_a_3704_);
v___y_3687_ = v___y_3702_;
v___y_3688_ = v___y_3703_;
v_a_3689_ = v___x_3705_;
goto v___jp_3686_;
}
v___jp_3706_:
{
lean_object* v___x_3710_; 
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v_a_3709_);
v___y_3687_ = v___y_3707_;
v___y_3688_ = v___y_3708_;
v_a_3689_ = v___x_3710_;
goto v___jp_3686_;
}
v___jp_3711_:
{
uint8_t v___x_3715_; 
v___x_3715_ = l_Lean_Exception_isInterrupt(v_a_3714_);
if (v___x_3715_ == 0)
{
uint8_t v___x_3716_; 
lean_inc_ref(v_a_3714_);
v___x_3716_ = l_Lean_Exception_isRuntime(v_a_3714_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3718_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3653_, v_options_3650_, v___x_3718_);
if (v___x_3719_ == 0)
{
v___y_3707_ = v___y_3712_;
v___y_3708_ = v___y_3713_;
v_a_3709_ = v_a_3714_;
goto v___jp_3706_;
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
lean_inc_ref(v_a_3714_);
v___x_3720_ = l_Lean_Exception_toMessageData(v_a_3714_);
v___x_3721_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3717_, v___x_3720_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_dec_ref_known(v___x_3721_, 1);
v___y_3707_ = v___y_3712_;
v___y_3708_ = v___y_3713_;
v_a_3709_ = v_a_3714_;
goto v___jp_3706_;
}
else
{
lean_object* v_a_3722_; 
lean_dec_ref(v_a_3714_);
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v___y_3707_ = v___y_3712_;
v___y_3708_ = v___y_3713_;
v_a_3709_ = v_a_3722_;
goto v___jp_3706_;
}
}
}
else
{
v___y_3707_ = v___y_3712_;
v___y_3708_ = v___y_3713_;
v_a_3709_ = v_a_3714_;
goto v___jp_3706_;
}
}
else
{
v___y_3707_ = v___y_3712_;
v___y_3708_ = v___y_3713_;
v_a_3709_ = v_a_3714_;
goto v___jp_3706_;
}
}
v___jp_3723_:
{
lean_object* v___x_3727_; double v___x_3728_; double v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3727_ = lean_io_get_num_heartbeats();
v___x_3728_ = lean_float_of_nat(v___y_3725_);
v___x_3729_ = lean_float_of_nat(v___x_3727_);
v___x_3730_ = lean_box_float(v___x_3728_);
v___x_3731_ = lean_box_float(v___x_3729_);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_a_3726_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3682_, v_hasTrace_3651_, v___x_3683_, v_options_3650_, v___x_3685_, v___y_3724_, v___f_3654_, v___x_3733_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
return v___x_3734_;
}
v___jp_3735_:
{
lean_object* v___x_3739_; 
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v_a_3738_);
v___y_3724_ = v___y_3736_;
v___y_3725_ = v___y_3737_;
v_a_3726_ = v___x_3739_;
goto v___jp_3723_;
}
v___jp_3740_:
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_a_3743_);
v___y_3724_ = v___y_3741_;
v___y_3725_ = v___y_3742_;
v_a_3726_ = v___x_3744_;
goto v___jp_3723_;
}
v___jp_3745_:
{
uint8_t v___x_3749_; 
v___x_3749_ = l_Lean_Exception_isInterrupt(v_a_3748_);
if (v___x_3749_ == 0)
{
uint8_t v___x_3750_; 
lean_inc_ref(v_a_3748_);
v___x_3750_ = l_Lean_Exception_isRuntime(v_a_3748_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
v___x_3751_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3752_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3753_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3653_, v_options_3650_, v___x_3752_);
if (v___x_3753_ == 0)
{
v___y_3741_ = v___y_3746_;
v___y_3742_ = v___y_3747_;
v_a_3743_ = v_a_3748_;
goto v___jp_3740_;
}
else
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
lean_inc_ref(v_a_3748_);
v___x_3754_ = l_Lean_Exception_toMessageData(v_a_3748_);
v___x_3755_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3751_, v___x_3754_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_dec_ref_known(v___x_3755_, 1);
v___y_3741_ = v___y_3746_;
v___y_3742_ = v___y_3747_;
v_a_3743_ = v_a_3748_;
goto v___jp_3740_;
}
else
{
lean_object* v_a_3756_; 
lean_dec_ref(v_a_3748_);
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v___y_3741_ = v___y_3746_;
v___y_3742_ = v___y_3747_;
v_a_3743_ = v_a_3756_;
goto v___jp_3740_;
}
}
}
else
{
v___y_3741_ = v___y_3746_;
v___y_3742_ = v___y_3747_;
v_a_3743_ = v_a_3748_;
goto v___jp_3740_;
}
}
else
{
v___y_3741_ = v___y_3746_;
v___y_3742_ = v___y_3747_;
v_a_3743_ = v_a_3748_;
goto v___jp_3740_;
}
}
v___jp_3757_:
{
lean_object* v___x_3758_; lean_object* v_a_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3758_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3647_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v___x_3758_);
v___x_3760_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3761_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3650_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_io_mono_nanos_now();
lean_inc(v_a_3647_);
lean_inc_ref(v_a_3646_);
lean_inc(v_a_3645_);
lean_inc_ref(v_a_3644_);
v___x_3763_ = lean_apply_5(v_k_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, lean_box(0));
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v___x_3765_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3766_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3767_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3653_, v_options_3650_, v___x_3766_);
if (v___x_3767_ == 0)
{
v___y_3702_ = v_a_3759_;
v___y_3703_ = v___x_3762_;
v_a_3704_ = v_a_3764_;
goto v___jp_3701_;
}
else
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
lean_inc(v_a_3764_);
v___x_3768_ = l_Lean_MessageData_ofExpr(v_a_3764_);
v___x_3769_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3765_, v___x_3768_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_dec_ref_known(v___x_3769_, 1);
v___y_3702_ = v_a_3759_;
v___y_3703_ = v___x_3762_;
v_a_3704_ = v_a_3764_;
goto v___jp_3701_;
}
else
{
lean_object* v_a_3770_; 
lean_dec(v_a_3764_);
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___x_3769_, 1);
v___y_3712_ = v_a_3759_;
v___y_3713_ = v___x_3762_;
v_a_3714_ = v_a_3770_;
goto v___jp_3711_;
}
}
}
else
{
lean_object* v_a_3771_; 
v_a_3771_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3763_, 1);
v___y_3712_ = v_a_3759_;
v___y_3713_ = v___x_3762_;
v_a_3714_ = v_a_3771_;
goto v___jp_3711_;
}
}
else
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3647_);
lean_inc_ref(v_a_3646_);
lean_inc(v_a_3645_);
lean_inc_ref(v_a_3644_);
v___x_3773_ = lean_apply_5(v_k_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, lean_box(0));
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
v___x_3775_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3776_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3653_, v_options_3650_, v___x_3776_);
if (v___x_3777_ == 0)
{
v___y_3736_ = v_a_3759_;
v___y_3737_ = v___x_3772_;
v_a_3738_ = v_a_3774_;
goto v___jp_3735_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_inc(v_a_3774_);
v___x_3778_ = l_Lean_MessageData_ofExpr(v_a_3774_);
v___x_3779_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3775_, v___x_3778_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_dec_ref_known(v___x_3779_, 1);
v___y_3736_ = v_a_3759_;
v___y_3737_ = v___x_3772_;
v_a_3738_ = v_a_3774_;
goto v___jp_3735_;
}
else
{
lean_object* v_a_3780_; 
lean_dec(v_a_3774_);
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___y_3746_ = v_a_3759_;
v___y_3747_ = v___x_3772_;
v_a_3748_ = v_a_3780_;
goto v___jp_3745_;
}
}
}
else
{
lean_object* v_a_3781_; 
v_a_3781_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3773_, 1);
v___y_3746_ = v_a_3759_;
v___y_3747_ = v___x_3772_;
v_a_3748_ = v_a_3781_;
goto v___jp_3745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3808_, lean_object* v_xs_3809_, lean_object* v_k_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3808_, v_xs_3809_, v_k_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3817_, lean_object* v_xs_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v___x_3824_; 
lean_inc(v_a_3822_);
lean_inc_ref(v_a_3821_);
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc_ref(v_f_3817_);
v___x_3824_ = lean_infer_type(v_f_3817_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
lean_inc_ref(v_xs_3818_);
lean_inc_ref(v_f_3817_);
v___x_3826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3826_, 0, v_f_3817_);
lean_closure_set(v___x_3826_, 1, v_a_3825_);
lean_closure_set(v___x_3826_, 2, v_xs_3818_);
v___x_3827_ = 0;
v___x_3828_ = lean_box(v___x_3827_);
v___x_3829_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3829_, 0, lean_box(0));
lean_closure_set(v___x_3829_, 1, v___x_3826_);
lean_closure_set(v___x_3829_, 2, v___x_3828_);
v___x_3830_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3817_, v_xs_3818_, v___x_3829_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
return v___x_3830_;
}
else
{
lean_dec_ref(v_xs_3818_);
lean_dec_ref(v_f_3817_);
return v___x_3824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3831_, lean_object* v_xs_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Meta_mkAppM_x27(v_f_3831_, v_xs_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3839_, size_t v_i_3840_, size_t v_stop_3841_, lean_object* v_b_3842_){
_start:
{
lean_object* v___y_3844_; uint8_t v___x_3848_; 
v___x_3848_ = lean_usize_dec_eq(v_i_3840_, v_stop_3841_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
v___x_3849_ = lean_array_uget_borrowed(v_as_3839_, v_i_3840_);
if (lean_obj_tag(v___x_3849_) == 0)
{
v___y_3844_ = v_b_3842_;
goto v___jp_3843_;
}
else
{
lean_object* v_val_3850_; lean_object* v___x_3851_; 
v_val_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_val_3850_);
v___x_3851_ = lean_array_push(v_b_3842_, v_val_3850_);
v___y_3844_ = v___x_3851_;
goto v___jp_3843_;
}
}
else
{
return v_b_3842_;
}
v___jp_3843_:
{
size_t v___x_3845_; size_t v___x_3846_; 
v___x_3845_ = ((size_t)1ULL);
v___x_3846_ = lean_usize_add(v_i_3840_, v___x_3845_);
v_i_3840_ = v___x_3846_;
v_b_3842_ = v___y_3844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3852_, lean_object* v_i_3853_, lean_object* v_stop_3854_, lean_object* v_b_3855_){
_start:
{
size_t v_i_boxed_3856_; size_t v_stop_boxed_3857_; lean_object* v_res_3858_; 
v_i_boxed_3856_ = lean_unbox_usize(v_i_3853_);
lean_dec(v_i_3853_);
v_stop_boxed_3857_ = lean_unbox_usize(v_stop_3854_);
lean_dec(v_stop_3854_);
v_res_3858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3852_, v_i_boxed_3856_, v_stop_boxed_3857_, v_b_3855_);
lean_dec_ref(v_as_3852_);
return v_res_3858_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3866_ = l_Lean_MessageData_ofFormat(v___x_3865_);
return v___x_3866_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_box(1);
v___x_3868_ = l_Lean_MessageData_ofFormat(v___x_3867_);
return v___x_3868_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3873_ = l_Lean_MessageData_ofFormat(v___x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3874_, lean_object* v_xs_3875_, lean_object* v_x_3876_, lean_object* v_x_3877_, lean_object* v_x_3878_, lean_object* v_x_3879_, lean_object* v_x_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
if (lean_obj_tag(v_x_3880_) == 7)
{
lean_object* v_binderName_3886_; lean_object* v_binderType_3887_; lean_object* v_body_3888_; uint8_t v_binderInfo_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; 
v_binderName_3886_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_binderName_3886_);
v_binderType_3887_ = lean_ctor_get(v_x_3880_, 1);
lean_inc_ref(v_binderType_3887_);
v_body_3888_ = lean_ctor_get(v_x_3880_, 2);
lean_inc_ref(v_body_3888_);
v_binderInfo_3889_ = lean_ctor_get_uint8(v_x_3880_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3880_, 3);
v___x_3890_ = lean_array_get_size(v_xs_3875_);
v___x_3891_ = lean_nat_dec_lt(v_x_3876_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec_ref(v_body_3888_);
lean_dec_ref(v_binderType_3887_);
lean_dec(v_binderName_3886_);
lean_dec(v_x_3878_);
lean_dec(v_x_3876_);
v___x_3892_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3893_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3892_, v_f_3874_, v_x_3877_, v_x_3879_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec_ref(v_x_3879_);
lean_dec_ref(v_x_3877_);
return v___x_3893_;
}
else
{
lean_object* v___x_3894_; lean_object* v_d_3895_; lean_object* v___x_3896_; 
v___x_3894_ = lean_array_get_size(v_x_3877_);
v_d_3895_ = lean_expr_instantiate_rev_range(v_binderType_3887_, v_x_3878_, v___x_3894_, v_x_3877_);
lean_dec_ref(v_binderType_3887_);
v___x_3896_ = lean_array_fget_borrowed(v_xs_3875_, v_x_3876_);
if (lean_obj_tag(v___x_3896_) == 0)
{
if (v_binderInfo_3889_ == 3)
{
lean_object* v___x_3897_; uint8_t v___x_3898_; lean_object* v___x_3899_; 
v___x_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3897_, 0, v_d_3895_);
v___x_3898_ = 1;
v___x_3899_ = l_Lean_Meta_mkFreshExprMVar(v___x_3897_, v___x_3898_, v_binderName_3886_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc_n(v_a_3900_, 2);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = lean_unsigned_to_nat(1u);
v___x_3902_ = lean_nat_add(v_x_3876_, v___x_3901_);
lean_dec(v_x_3876_);
v___x_3903_ = lean_array_push(v_x_3877_, v_a_3900_);
v___x_3904_ = l_Lean_Expr_mvarId_x21(v_a_3900_);
lean_dec(v_a_3900_);
v___x_3905_ = lean_array_push(v_x_3879_, v___x_3904_);
v_x_3876_ = v___x_3902_;
v_x_3877_ = v___x_3903_;
v_x_3879_ = v___x_3905_;
v_x_3880_ = v_body_3888_;
goto _start;
}
else
{
lean_dec_ref(v_body_3888_);
lean_dec_ref(v_x_3879_);
lean_dec(v_x_3878_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_f_3874_);
return v___x_3899_;
}
}
else
{
lean_object* v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v_d_3895_);
v___x_3908_ = 0;
v___x_3909_ = l_Lean_Meta_mkFreshExprMVar(v___x_3907_, v___x_3908_, v_binderName_3886_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = lean_unsigned_to_nat(1u);
v___x_3912_ = lean_nat_add(v_x_3876_, v___x_3911_);
lean_dec(v_x_3876_);
v___x_3913_ = lean_array_push(v_x_3877_, v_a_3910_);
v_x_3876_ = v___x_3912_;
v_x_3877_ = v___x_3913_;
v_x_3880_ = v_body_3888_;
goto _start;
}
else
{
lean_dec_ref(v_body_3888_);
lean_dec_ref(v_x_3879_);
lean_dec(v_x_3878_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_f_3874_);
return v___x_3909_;
}
}
}
else
{
lean_object* v_val_3915_; lean_object* v___x_3916_; 
lean_dec(v_binderName_3886_);
v_val_3915_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3884_);
lean_inc_ref(v_a_3883_);
lean_inc(v_a_3882_);
lean_inc_ref(v_a_3881_);
lean_inc(v_val_3915_);
v___x_3916_ = lean_infer_type(v_val_3915_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = l_Lean_Meta_isExprDefEq(v_d_3895_, v_a_3917_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; uint8_t v___x_3920_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = lean_unbox(v_a_3919_);
lean_dec(v_a_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_dec_ref(v_body_3888_);
lean_dec_ref(v_x_3879_);
lean_dec(v_x_3878_);
lean_dec(v_x_3876_);
v___x_3921_ = l_Lean_mkAppN(v_f_3874_, v_x_3877_);
lean_dec_ref(v_x_3877_);
lean_inc(v_val_3915_);
v___x_3922_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3921_, v_val_3915_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
return v___x_3922_;
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_nat_add(v_x_3876_, v___x_3923_);
lean_dec(v_x_3876_);
lean_inc(v_val_3915_);
v___x_3925_ = lean_array_push(v_x_3877_, v_val_3915_);
v_x_3876_ = v___x_3924_;
v_x_3877_ = v___x_3925_;
v_x_3880_ = v_body_3888_;
goto _start;
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v_body_3888_);
lean_dec_ref(v_x_3879_);
lean_dec(v_x_3878_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_f_3874_);
v_a_3927_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3918_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3918_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
else
{
lean_dec_ref(v_d_3895_);
lean_dec_ref(v_body_3888_);
lean_dec_ref(v_x_3879_);
lean_dec(v_x_3878_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_f_3874_);
return v___x_3916_;
}
}
}
}
else
{
lean_object* v___x_3935_; lean_object* v_type_3936_; lean_object* v___x_3937_; 
v___x_3935_ = lean_array_get_size(v_x_3877_);
v_type_3936_ = lean_expr_instantiate_rev_range(v_x_3880_, v_x_3878_, v___x_3935_, v_x_3877_);
lean_dec(v_x_3878_);
lean_dec_ref(v_x_3880_);
v___x_3937_ = l_Lean_Meta_whnfD(v_type_3936_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; uint8_t v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3939_ = l_Lean_Expr_isForall(v_a_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; uint8_t v___x_3941_; 
lean_dec(v_a_3938_);
v___x_3940_ = lean_array_get_size(v_xs_3875_);
v___x_3941_ = lean_nat_dec_eq(v_x_3876_, v___x_3940_);
lean_dec(v_x_3876_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v___y_3944_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
lean_dec_ref(v_x_3879_);
lean_dec_ref(v_x_3877_);
v___x_3942_ = lean_unsigned_to_nat(0u);
v___x_3957_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3958_ = lean_nat_dec_lt(v___x_3942_, v___x_3940_);
if (v___x_3958_ == 0)
{
v___y_3944_ = v___x_3957_;
goto v___jp_3943_;
}
else
{
size_t v___x_3959_; size_t v___x_3960_; lean_object* v___x_3961_; 
v___x_3959_ = ((size_t)0ULL);
v___x_3960_ = lean_usize_of_nat(v___x_3940_);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3875_, v___x_3959_, v___x_3960_, v___x_3957_);
v___y_3944_ = v___x_3961_;
goto v___jp_3943_;
}
v___jp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3945_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3946_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3947_ = l_Lean_indentExpr(v_f_3874_);
v___x_3948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
v___x_3949_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3950_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3954_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3944_, v___x_3942_, v___x_3953_);
lean_dec_ref(v___y_3944_);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3952_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3945_, v___x_3955_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
return v___x_3956_;
}
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3963_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3962_, v_f_3874_, v_x_3877_, v_x_3879_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec_ref(v_x_3879_);
lean_dec_ref(v_x_3877_);
return v___x_3963_;
}
}
else
{
v_x_3878_ = v___x_3935_;
v_x_3880_ = v_a_3938_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3879_);
lean_dec_ref(v_x_3877_);
lean_dec(v_x_3876_);
lean_dec_ref(v_f_3874_);
return v___x_3937_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_3965_, lean_object* v_xs_3966_, lean_object* v_x_3967_, lean_object* v_x_3968_, lean_object* v_x_3969_, lean_object* v_x_3970_, lean_object* v_x_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_3965_, v_xs_3966_, v_x_3967_, v_x_3968_, v_x_3969_, v_x_3970_, v_x_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec_ref(v_xs_3966_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_3978_, lean_object* v_xs_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_3978_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v_fst_3987_; lean_object* v_snd_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v_fst_3987_ = lean_ctor_get(v_a_3986_, 0);
lean_inc(v_fst_3987_);
v_snd_3988_ = lean_ctor_get(v_a_3986_, 1);
lean_inc(v_snd_3988_);
lean_dec(v_a_3986_);
v___x_3989_ = lean_unsigned_to_nat(0u);
v___x_3990_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3991_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_3987_, v_xs_3979_, v___x_3989_, v___x_3990_, v___x_3989_, v___x_3990_, v_snd_3988_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
return v___x_3991_;
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
v_a_3992_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3985_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3985_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4000_, lean_object* v_xs_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4000_, v_xs_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec_ref(v_xs_4001_);
return v_res_4007_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4012_ = l_Lean_MessageData_ofFormat(v___x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
if (lean_obj_tag(v_a_4013_) == 0)
{
lean_object* v___x_4015_; 
v___x_4015_ = l_List_reverse___redArg(v_a_4014_);
return v___x_4015_;
}
else
{
lean_object* v_head_4016_; lean_object* v_tail_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4030_; 
v_head_4016_ = lean_ctor_get(v_a_4013_, 0);
v_tail_4017_ = lean_ctor_get(v_a_4013_, 1);
v_isSharedCheck_4030_ = !lean_is_exclusive(v_a_4013_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4019_ = v_a_4013_;
v_isShared_4020_ = v_isSharedCheck_4030_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_tail_4017_);
lean_inc(v_head_4016_);
lean_dec(v_a_4013_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4030_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___y_4022_; 
if (lean_obj_tag(v_head_4016_) == 0)
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4022_ = v___x_4027_;
goto v___jp_4021_;
}
else
{
lean_object* v_val_4028_; lean_object* v___x_4029_; 
v_val_4028_ = lean_ctor_get(v_head_4016_, 0);
lean_inc(v_val_4028_);
lean_dec_ref_known(v_head_4016_, 1);
v___x_4029_ = l_Lean_MessageData_ofExpr(v_val_4028_);
v___y_4022_ = v___x_4029_;
goto v___jp_4021_;
}
v___jp_4021_:
{
lean_object* v___x_4024_; 
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 1, v_a_4014_);
lean_ctor_set(v___x_4019_, 0, v___y_4022_);
v___x_4024_ = v___x_4019_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___y_4022_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v_a_4014_);
v___x_4024_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
v_a_4013_ = v_tail_4017_;
v_a_4014_ = v___x_4024_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4031_, lean_object* v_xs_4032_, lean_object* v_x_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4039_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4040_ = l_Lean_MessageData_ofName(v_f_4031_);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4039_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4041_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = lean_array_to_list(v_xs_4032_);
v___x_4045_ = lean_box(0);
v___x_4046_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4044_, v___x_4045_);
v___x_4047_ = l_Lean_MessageData_ofList(v___x_4046_);
v___x_4048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4043_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
v___x_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4050_, lean_object* v_xs_4051_, lean_object* v_x_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4050_, v_xs_4051_, v_x_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec_ref(v_x_4052_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4059_, lean_object* v_xs_4060_, lean_object* v_k_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_toCold_4067_; lean_object* v_options_4068_; uint8_t v_hasTrace_4069_; 
v_toCold_4067_ = lean_ctor_get(v_a_4064_, 0);
v_options_4068_ = lean_ctor_get(v_toCold_4067_, 2);
v_hasTrace_4069_ = lean_ctor_get_uint8(v_options_4068_, sizeof(void*)*1);
if (v_hasTrace_4069_ == 0)
{
lean_object* v___x_4070_; 
lean_dec_ref(v_xs_4060_);
lean_dec(v_f_4059_);
lean_inc(v_a_4065_);
lean_inc_ref(v_a_4064_);
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
v___x_4070_ = lean_apply_5(v_k_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, lean_box(0));
return v___x_4070_;
}
else
{
lean_object* v_inheritedTraceOptions_4071_; lean_object* v___f_4072_; lean_object* v___y_4074_; lean_object* v_a_4075_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v_a_4107_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v_a_4122_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v_a_4127_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v_a_4132_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v_a_4144_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v_a_4156_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v_a_4161_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v_a_4166_; 
v_inheritedTraceOptions_4071_ = lean_ctor_get(v_toCold_4067_, 11);
v___f_4072_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4072_, 0, v_f_4059_);
lean_closure_set(v___f_4072_, 1, v_xs_4060_);
v___x_4100_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4101_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4102_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4103_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4068_, v___x_4102_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4200_; uint8_t v___x_4201_; 
v___x_4200_ = l_Lean_trace_profiler;
v___x_4201_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4068_, v___x_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; 
lean_dec_ref(v___f_4072_);
lean_inc(v_a_4065_);
lean_inc_ref(v_a_4064_);
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
v___x_4202_ = lean_apply_5(v_k_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, lean_box(0));
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
v___x_4204_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4205_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4206_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4068_, v___x_4205_);
if (v___x_4206_ == 0)
{
lean_dec(v_a_4203_);
return v___x_4202_;
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_dec_ref_known(v___x_4202_, 1);
lean_inc(v_a_4203_);
v___x_4207_ = l_Lean_MessageData_ofExpr(v_a_4203_);
v___x_4208_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4204_, v___x_4207_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4215_ == 0)
{
lean_object* v_unused_4216_; 
v_unused_4216_ = lean_ctor_get(v___x_4208_, 0);
lean_dec(v_unused_4216_);
v___x_4210_ = v___x_4208_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_dec(v___x_4208_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v_a_4203_);
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4203_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v_a_4203_);
v_a_4217_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4208_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4208_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
lean_inc(v_a_4217_);
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
v___y_4074_ = v___x_4222_;
v_a_4075_ = v_a_4217_;
goto v___jp_4073_;
}
}
}
}
}
else
{
lean_object* v_a_4225_; 
v_a_4225_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4225_);
v___y_4074_ = v___x_4202_;
v_a_4075_ = v_a_4225_;
goto v___jp_4073_;
}
}
else
{
goto v___jp_4175_;
}
}
else
{
goto v___jp_4175_;
}
v___jp_4073_:
{
uint8_t v___x_4076_; 
v___x_4076_ = l_Lean_Exception_isInterrupt(v_a_4075_);
if (v___x_4076_ == 0)
{
uint8_t v___x_4077_; 
lean_inc_ref(v_a_4075_);
v___x_4077_ = l_Lean_Exception_isRuntime(v_a_4075_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
lean_dec_ref(v___y_4074_);
v___x_4078_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4079_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4068_, v___x_4079_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4081_, 0, v_a_4075_);
return v___x_4081_;
}
else
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
lean_inc_ref(v_a_4075_);
v___x_4082_ = l_Lean_Exception_toMessageData(v_a_4075_);
v___x_4083_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4078_, v___x_4082_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v___x_4083_, 0);
lean_dec(v_unused_4091_);
v___x_4085_ = v___x_4083_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_dec(v___x_4083_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
lean_ctor_set_tag(v___x_4085_, 1);
lean_ctor_set(v___x_4085_, 0, v_a_4075_);
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4075_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref(v_a_4075_);
v_a_4092_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4083_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4083_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_4075_);
return v___y_4074_;
}
}
else
{
lean_dec_ref(v_a_4075_);
return v___y_4074_;
}
}
v___jp_4104_:
{
lean_object* v___x_4108_; double v___x_4109_; double v___x_4110_; double v___x_4111_; double v___x_4112_; double v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4108_ = lean_io_mono_nanos_now();
v___x_4109_ = lean_float_of_nat(v___y_4105_);
v___x_4110_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4111_ = lean_float_div(v___x_4109_, v___x_4110_);
v___x_4112_ = lean_float_of_nat(v___x_4108_);
v___x_4113_ = lean_float_div(v___x_4112_, v___x_4110_);
v___x_4114_ = lean_box_float(v___x_4111_);
v___x_4115_ = lean_box_float(v___x_4113_);
v___x_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4114_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4117_, 0, v_a_4107_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4100_, v_hasTrace_4069_, v___x_4101_, v_options_4068_, v___x_4103_, v___y_4106_, v___f_4072_, v___x_4117_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
return v___x_4118_;
}
v___jp_4119_:
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_a_4122_);
v___y_4105_ = v___y_4120_;
v___y_4106_ = v___y_4121_;
v_a_4107_ = v___x_4123_;
goto v___jp_4104_;
}
v___jp_4124_:
{
lean_object* v___x_4128_; 
v___x_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4128_, 0, v_a_4127_);
v___y_4105_ = v___y_4125_;
v___y_4106_ = v___y_4126_;
v_a_4107_ = v___x_4128_;
goto v___jp_4104_;
}
v___jp_4129_:
{
uint8_t v___x_4133_; 
v___x_4133_ = l_Lean_Exception_isInterrupt(v_a_4132_);
if (v___x_4133_ == 0)
{
uint8_t v___x_4134_; 
lean_inc_ref(v_a_4132_);
v___x_4134_ = l_Lean_Exception_isRuntime(v_a_4132_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; 
v___x_4135_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4136_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4137_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4068_, v___x_4136_);
if (v___x_4137_ == 0)
{
v___y_4125_ = v___y_4130_;
v___y_4126_ = v___y_4131_;
v_a_4127_ = v_a_4132_;
goto v___jp_4124_;
}
else
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
lean_inc_ref(v_a_4132_);
v___x_4138_ = l_Lean_Exception_toMessageData(v_a_4132_);
v___x_4139_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4135_, v___x_4138_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_dec_ref_known(v___x_4139_, 1);
v___y_4125_ = v___y_4130_;
v___y_4126_ = v___y_4131_;
v_a_4127_ = v_a_4132_;
goto v___jp_4124_;
}
else
{
lean_object* v_a_4140_; 
lean_dec_ref(v_a_4132_);
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v___y_4125_ = v___y_4130_;
v___y_4126_ = v___y_4131_;
v_a_4127_ = v_a_4140_;
goto v___jp_4124_;
}
}
}
else
{
v___y_4125_ = v___y_4130_;
v___y_4126_ = v___y_4131_;
v_a_4127_ = v_a_4132_;
goto v___jp_4124_;
}
}
else
{
v___y_4125_ = v___y_4130_;
v___y_4126_ = v___y_4131_;
v_a_4127_ = v_a_4132_;
goto v___jp_4124_;
}
}
v___jp_4141_:
{
lean_object* v___x_4145_; double v___x_4146_; double v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4145_ = lean_io_get_num_heartbeats();
v___x_4146_ = lean_float_of_nat(v___y_4143_);
v___x_4147_ = lean_float_of_nat(v___x_4145_);
v___x_4148_ = lean_box_float(v___x_4146_);
v___x_4149_ = lean_box_float(v___x_4147_);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4148_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4151_, 0, v_a_4144_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
v___x_4152_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4100_, v_hasTrace_4069_, v___x_4101_, v_options_4068_, v___x_4103_, v___y_4142_, v___f_4072_, v___x_4151_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
return v___x_4152_;
}
v___jp_4153_:
{
lean_object* v___x_4157_; 
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_a_4156_);
v___y_4142_ = v___y_4154_;
v___y_4143_ = v___y_4155_;
v_a_4144_ = v___x_4157_;
goto v___jp_4141_;
}
v___jp_4158_:
{
lean_object* v___x_4162_; 
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v_a_4161_);
v___y_4142_ = v___y_4159_;
v___y_4143_ = v___y_4160_;
v_a_4144_ = v___x_4162_;
goto v___jp_4141_;
}
v___jp_4163_:
{
uint8_t v___x_4167_; 
v___x_4167_ = l_Lean_Exception_isInterrupt(v_a_4166_);
if (v___x_4167_ == 0)
{
uint8_t v___x_4168_; 
lean_inc_ref(v_a_4166_);
v___x_4168_ = l_Lean_Exception_isRuntime(v_a_4166_);
if (v___x_4168_ == 0)
{
lean_object* v___x_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4169_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4170_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4171_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4068_, v___x_4170_);
if (v___x_4171_ == 0)
{
v___y_4159_ = v___y_4164_;
v___y_4160_ = v___y_4165_;
v_a_4161_ = v_a_4166_;
goto v___jp_4158_;
}
else
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_inc_ref(v_a_4166_);
v___x_4172_ = l_Lean_Exception_toMessageData(v_a_4166_);
v___x_4173_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4169_, v___x_4172_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_dec_ref_known(v___x_4173_, 1);
v___y_4159_ = v___y_4164_;
v___y_4160_ = v___y_4165_;
v_a_4161_ = v_a_4166_;
goto v___jp_4158_;
}
else
{
lean_object* v_a_4174_; 
lean_dec_ref(v_a_4166_);
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4173_, 1);
v___y_4159_ = v___y_4164_;
v___y_4160_ = v___y_4165_;
v_a_4161_ = v_a_4174_;
goto v___jp_4158_;
}
}
}
else
{
v___y_4159_ = v___y_4164_;
v___y_4160_ = v___y_4165_;
v_a_4161_ = v_a_4166_;
goto v___jp_4158_;
}
}
else
{
v___y_4159_ = v___y_4164_;
v___y_4160_ = v___y_4165_;
v_a_4161_ = v_a_4166_;
goto v___jp_4158_;
}
}
v___jp_4175_:
{
lean_object* v___x_4176_; lean_object* v_a_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; 
v___x_4176_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4065_);
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4179_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4068_, v___x_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4180_ = lean_io_mono_nanos_now();
lean_inc(v_a_4065_);
lean_inc_ref(v_a_4064_);
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
v___x_4181_ = lean_apply_5(v_k_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, lean_box(0));
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4181_, 1);
v___x_4183_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4184_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4185_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4068_, v___x_4184_);
if (v___x_4185_ == 0)
{
v___y_4120_ = v___x_4180_;
v___y_4121_ = v_a_4177_;
v_a_4122_ = v_a_4182_;
goto v___jp_4119_;
}
else
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_inc(v_a_4182_);
v___x_4186_ = l_Lean_MessageData_ofExpr(v_a_4182_);
v___x_4187_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4183_, v___x_4186_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_dec_ref_known(v___x_4187_, 1);
v___y_4120_ = v___x_4180_;
v___y_4121_ = v_a_4177_;
v_a_4122_ = v_a_4182_;
goto v___jp_4119_;
}
else
{
lean_object* v_a_4188_; 
lean_dec(v_a_4182_);
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v___x_4187_, 1);
v___y_4130_ = v___x_4180_;
v___y_4131_ = v_a_4177_;
v_a_4132_ = v_a_4188_;
goto v___jp_4129_;
}
}
}
else
{
lean_object* v_a_4189_; 
v_a_4189_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4181_, 1);
v___y_4130_ = v___x_4180_;
v___y_4131_ = v_a_4177_;
v_a_4132_ = v_a_4189_;
goto v___jp_4129_;
}
}
else
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4065_);
lean_inc_ref(v_a_4064_);
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
v___x_4191_ = lean_apply_5(v_k_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, lean_box(0));
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; uint8_t v___x_4195_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___x_4191_, 1);
v___x_4193_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4194_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4195_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4068_, v___x_4194_);
if (v___x_4195_ == 0)
{
v___y_4154_ = v_a_4177_;
v___y_4155_ = v___x_4190_;
v_a_4156_ = v_a_4192_;
goto v___jp_4153_;
}
else
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
lean_inc(v_a_4192_);
v___x_4196_ = l_Lean_MessageData_ofExpr(v_a_4192_);
v___x_4197_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4193_, v___x_4196_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_dec_ref_known(v___x_4197_, 1);
v___y_4154_ = v_a_4177_;
v___y_4155_ = v___x_4190_;
v_a_4156_ = v_a_4192_;
goto v___jp_4153_;
}
else
{
lean_object* v_a_4198_; 
lean_dec(v_a_4192_);
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
v___y_4164_ = v_a_4177_;
v___y_4165_ = v___x_4190_;
v_a_4166_ = v_a_4198_;
goto v___jp_4163_;
}
}
}
else
{
lean_object* v_a_4199_; 
v_a_4199_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4191_, 1);
v___y_4164_ = v_a_4177_;
v___y_4165_ = v___x_4190_;
v_a_4166_ = v_a_4199_;
goto v___jp_4163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4226_, lean_object* v_xs_4227_, lean_object* v_k_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4226_, v_xs_4227_, v_k_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
lean_dec(v_a_4230_);
lean_dec_ref(v_a_4229_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4235_, lean_object* v_xs_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v___f_4242_; uint8_t v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_inc_ref(v_xs_4236_);
lean_inc(v_constName_4235_);
v___f_4242_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4242_, 0, v_constName_4235_);
lean_closure_set(v___f_4242_, 1, v_xs_4236_);
v___x_4243_ = 0;
v___x_4244_ = lean_box(v___x_4243_);
v___x_4245_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4245_, 0, lean_box(0));
lean_closure_set(v___x_4245_, 1, v___f_4242_);
lean_closure_set(v___x_4245_, 2, v___x_4244_);
v___x_4246_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4235_, v_xs_4236_, v___x_4245_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4247_, lean_object* v_xs_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_Meta_mkAppOptM(v_constName_4247_, v_xs_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4255_, lean_object* v_xs_4256_, lean_object* v_x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4263_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4264_ = l_Lean_MessageData_ofExpr(v_f_4255_);
v___x_4265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4265_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = lean_array_to_list(v_xs_4256_);
v___x_4269_ = lean_box(0);
v___x_4270_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4268_, v___x_4269_);
v___x_4271_ = l_Lean_MessageData_ofList(v___x_4270_);
v___x_4272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4267_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4274_, lean_object* v_xs_4275_, lean_object* v_x_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4274_, v_xs_4275_, v_x_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec_ref(v_x_4276_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4283_, lean_object* v_xs_4284_, lean_object* v_k_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_toCold_4291_; lean_object* v_options_4292_; uint8_t v_hasTrace_4293_; 
v_toCold_4291_ = lean_ctor_get(v_a_4288_, 0);
v_options_4292_ = lean_ctor_get(v_toCold_4291_, 2);
v_hasTrace_4293_ = lean_ctor_get_uint8(v_options_4292_, sizeof(void*)*1);
if (v_hasTrace_4293_ == 0)
{
lean_object* v___x_4294_; 
lean_dec_ref(v_xs_4284_);
lean_dec_ref(v_f_4283_);
lean_inc(v_a_4289_);
lean_inc_ref(v_a_4288_);
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
v___x_4294_ = lean_apply_5(v_k_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, lean_box(0));
return v___x_4294_;
}
else
{
lean_object* v_inheritedTraceOptions_4295_; lean_object* v___f_4296_; lean_object* v___y_4298_; lean_object* v_a_4299_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v_a_4331_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v_a_4346_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v_a_4351_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v_a_4356_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v_a_4368_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v_a_4380_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v_a_4385_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v_a_4390_; 
v_inheritedTraceOptions_4295_ = lean_ctor_get(v_toCold_4291_, 11);
v___f_4296_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4296_, 0, v_f_4283_);
lean_closure_set(v___f_4296_, 1, v_xs_4284_);
v___x_4324_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4325_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4326_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4327_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4292_, v___x_4326_);
if (v___x_4327_ == 0)
{
lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4424_ = l_Lean_trace_profiler;
v___x_4425_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4292_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; 
lean_dec_ref(v___f_4296_);
lean_inc(v_a_4289_);
lean_inc_ref(v_a_4288_);
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
v___x_4426_ = lean_apply_5(v_k_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, lean_box(0));
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; uint8_t v___x_4430_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
v___x_4428_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4429_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4430_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4292_, v___x_4429_);
if (v___x_4430_ == 0)
{
lean_dec(v_a_4427_);
return v___x_4426_;
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
lean_dec_ref_known(v___x_4426_, 1);
lean_inc(v_a_4427_);
v___x_4431_ = l_Lean_MessageData_ofExpr(v_a_4427_);
v___x_4432_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4428_, v___x_4431_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4439_ == 0)
{
lean_object* v_unused_4440_; 
v_unused_4440_ = lean_ctor_get(v___x_4432_, 0);
lean_dec(v_unused_4440_);
v___x_4434_ = v___x_4432_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_dec(v___x_4432_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v_a_4427_);
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4427_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_a_4427_);
v_a_4441_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4432_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4432_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
lean_inc(v_a_4441_);
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
v___y_4298_ = v___x_4446_;
v_a_4299_ = v_a_4441_;
goto v___jp_4297_;
}
}
}
}
}
else
{
lean_object* v_a_4449_; 
v_a_4449_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4449_);
v___y_4298_ = v___x_4426_;
v_a_4299_ = v_a_4449_;
goto v___jp_4297_;
}
}
else
{
goto v___jp_4399_;
}
}
else
{
goto v___jp_4399_;
}
v___jp_4297_:
{
uint8_t v___x_4300_; 
v___x_4300_ = l_Lean_Exception_isInterrupt(v_a_4299_);
if (v___x_4300_ == 0)
{
uint8_t v___x_4301_; 
lean_inc_ref(v_a_4299_);
v___x_4301_ = l_Lean_Exception_isRuntime(v_a_4299_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; 
lean_dec_ref(v___y_4298_);
v___x_4302_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4303_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4304_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4292_, v___x_4303_);
if (v___x_4304_ == 0)
{
lean_object* v___x_4305_; 
v___x_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4305_, 0, v_a_4299_);
return v___x_4305_;
}
else
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
lean_inc_ref(v_a_4299_);
v___x_4306_ = l_Lean_Exception_toMessageData(v_a_4299_);
v___x_4307_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4302_, v___x_4306_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4314_ == 0)
{
lean_object* v_unused_4315_; 
v_unused_4315_ = lean_ctor_get(v___x_4307_, 0);
lean_dec(v_unused_4315_);
v___x_4309_ = v___x_4307_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_dec(v___x_4307_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set_tag(v___x_4309_, 1);
lean_ctor_set(v___x_4309_, 0, v_a_4299_);
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4299_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec_ref(v_a_4299_);
v_a_4316_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4307_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4307_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_4299_);
return v___y_4298_;
}
}
else
{
lean_dec_ref(v_a_4299_);
return v___y_4298_;
}
}
v___jp_4328_:
{
lean_object* v___x_4332_; double v___x_4333_; double v___x_4334_; double v___x_4335_; double v___x_4336_; double v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4332_ = lean_io_mono_nanos_now();
v___x_4333_ = lean_float_of_nat(v___y_4330_);
v___x_4334_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4335_ = lean_float_div(v___x_4333_, v___x_4334_);
v___x_4336_ = lean_float_of_nat(v___x_4332_);
v___x_4337_ = lean_float_div(v___x_4336_, v___x_4334_);
v___x_4338_ = lean_box_float(v___x_4335_);
v___x_4339_ = lean_box_float(v___x_4337_);
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4341_, 0, v_a_4331_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4324_, v_hasTrace_4293_, v___x_4325_, v_options_4292_, v___x_4327_, v___y_4329_, v___f_4296_, v___x_4341_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
return v___x_4342_;
}
v___jp_4343_:
{
lean_object* v___x_4347_; 
v___x_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4347_, 0, v_a_4346_);
v___y_4329_ = v___y_4344_;
v___y_4330_ = v___y_4345_;
v_a_4331_ = v___x_4347_;
goto v___jp_4328_;
}
v___jp_4348_:
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v_a_4351_);
v___y_4329_ = v___y_4349_;
v___y_4330_ = v___y_4350_;
v_a_4331_ = v___x_4352_;
goto v___jp_4328_;
}
v___jp_4353_:
{
uint8_t v___x_4357_; 
v___x_4357_ = l_Lean_Exception_isInterrupt(v_a_4356_);
if (v___x_4357_ == 0)
{
uint8_t v___x_4358_; 
lean_inc_ref(v_a_4356_);
v___x_4358_ = l_Lean_Exception_isRuntime(v_a_4356_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4360_; uint8_t v___x_4361_; 
v___x_4359_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4360_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4361_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4292_, v___x_4360_);
if (v___x_4361_ == 0)
{
v___y_4349_ = v___y_4354_;
v___y_4350_ = v___y_4355_;
v_a_4351_ = v_a_4356_;
goto v___jp_4348_;
}
else
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
lean_inc_ref(v_a_4356_);
v___x_4362_ = l_Lean_Exception_toMessageData(v_a_4356_);
v___x_4363_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4359_, v___x_4362_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_dec_ref_known(v___x_4363_, 1);
v___y_4349_ = v___y_4354_;
v___y_4350_ = v___y_4355_;
v_a_4351_ = v_a_4356_;
goto v___jp_4348_;
}
else
{
lean_object* v_a_4364_; 
lean_dec_ref(v_a_4356_);
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
v___y_4349_ = v___y_4354_;
v___y_4350_ = v___y_4355_;
v_a_4351_ = v_a_4364_;
goto v___jp_4348_;
}
}
}
else
{
v___y_4349_ = v___y_4354_;
v___y_4350_ = v___y_4355_;
v_a_4351_ = v_a_4356_;
goto v___jp_4348_;
}
}
else
{
v___y_4349_ = v___y_4354_;
v___y_4350_ = v___y_4355_;
v_a_4351_ = v_a_4356_;
goto v___jp_4348_;
}
}
v___jp_4365_:
{
lean_object* v___x_4369_; double v___x_4370_; double v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4369_ = lean_io_get_num_heartbeats();
v___x_4370_ = lean_float_of_nat(v___y_4367_);
v___x_4371_ = lean_float_of_nat(v___x_4369_);
v___x_4372_ = lean_box_float(v___x_4370_);
v___x_4373_ = lean_box_float(v___x_4371_);
v___x_4374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4372_);
lean_ctor_set(v___x_4374_, 1, v___x_4373_);
v___x_4375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4375_, 0, v_a_4368_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
v___x_4376_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4324_, v_hasTrace_4293_, v___x_4325_, v_options_4292_, v___x_4327_, v___y_4366_, v___f_4296_, v___x_4375_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
return v___x_4376_;
}
v___jp_4377_:
{
lean_object* v___x_4381_; 
v___x_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4381_, 0, v_a_4380_);
v___y_4366_ = v___y_4378_;
v___y_4367_ = v___y_4379_;
v_a_4368_ = v___x_4381_;
goto v___jp_4365_;
}
v___jp_4382_:
{
lean_object* v___x_4386_; 
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v_a_4385_);
v___y_4366_ = v___y_4383_;
v___y_4367_ = v___y_4384_;
v_a_4368_ = v___x_4386_;
goto v___jp_4365_;
}
v___jp_4387_:
{
uint8_t v___x_4391_; 
v___x_4391_ = l_Lean_Exception_isInterrupt(v_a_4390_);
if (v___x_4391_ == 0)
{
uint8_t v___x_4392_; 
lean_inc_ref(v_a_4390_);
v___x_4392_ = l_Lean_Exception_isRuntime(v_a_4390_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4393_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4394_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4395_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4292_, v___x_4394_);
if (v___x_4395_ == 0)
{
v___y_4383_ = v___y_4388_;
v___y_4384_ = v___y_4389_;
v_a_4385_ = v_a_4390_;
goto v___jp_4382_;
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
lean_inc_ref(v_a_4390_);
v___x_4396_ = l_Lean_Exception_toMessageData(v_a_4390_);
v___x_4397_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4393_, v___x_4396_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_dec_ref_known(v___x_4397_, 1);
v___y_4383_ = v___y_4388_;
v___y_4384_ = v___y_4389_;
v_a_4385_ = v_a_4390_;
goto v___jp_4382_;
}
else
{
lean_object* v_a_4398_; 
lean_dec_ref(v_a_4390_);
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
v___y_4383_ = v___y_4388_;
v___y_4384_ = v___y_4389_;
v_a_4385_ = v_a_4398_;
goto v___jp_4382_;
}
}
}
else
{
v___y_4383_ = v___y_4388_;
v___y_4384_ = v___y_4389_;
v_a_4385_ = v_a_4390_;
goto v___jp_4382_;
}
}
else
{
v___y_4383_ = v___y_4388_;
v___y_4384_ = v___y_4389_;
v_a_4385_ = v_a_4390_;
goto v___jp_4382_;
}
}
v___jp_4399_:
{
lean_object* v___x_4400_; lean_object* v_a_4401_; lean_object* v___x_4402_; uint8_t v___x_4403_; 
v___x_4400_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4289_);
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc(v_a_4401_);
lean_dec_ref(v___x_4400_);
v___x_4402_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4403_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4292_, v___x_4402_);
if (v___x_4403_ == 0)
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = lean_io_mono_nanos_now();
lean_inc(v_a_4289_);
lean_inc_ref(v_a_4288_);
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
v___x_4405_ = lean_apply_5(v_k_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, lean_box(0));
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; uint8_t v___x_4409_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v___x_4407_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4408_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4409_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4292_, v___x_4408_);
if (v___x_4409_ == 0)
{
v___y_4344_ = v_a_4401_;
v___y_4345_ = v___x_4404_;
v_a_4346_ = v_a_4406_;
goto v___jp_4343_;
}
else
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_inc(v_a_4406_);
v___x_4410_ = l_Lean_MessageData_ofExpr(v_a_4406_);
v___x_4411_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4407_, v___x_4410_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_dec_ref_known(v___x_4411_, 1);
v___y_4344_ = v_a_4401_;
v___y_4345_ = v___x_4404_;
v_a_4346_ = v_a_4406_;
goto v___jp_4343_;
}
else
{
lean_object* v_a_4412_; 
lean_dec(v_a_4406_);
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v___y_4354_ = v_a_4401_;
v___y_4355_ = v___x_4404_;
v_a_4356_ = v_a_4412_;
goto v___jp_4353_;
}
}
}
else
{
lean_object* v_a_4413_; 
v_a_4413_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4405_, 1);
v___y_4354_ = v_a_4401_;
v___y_4355_ = v___x_4404_;
v_a_4356_ = v_a_4413_;
goto v___jp_4353_;
}
}
else
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4289_);
lean_inc_ref(v_a_4288_);
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
v___x_4415_ = lean_apply_5(v_k_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, lean_box(0));
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; uint8_t v___x_4419_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4415_, 1);
v___x_4417_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4418_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4419_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4292_, v___x_4418_);
if (v___x_4419_ == 0)
{
v___y_4378_ = v_a_4401_;
v___y_4379_ = v___x_4414_;
v_a_4380_ = v_a_4416_;
goto v___jp_4377_;
}
else
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
lean_inc(v_a_4416_);
v___x_4420_ = l_Lean_MessageData_ofExpr(v_a_4416_);
v___x_4421_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4417_, v___x_4420_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_dec_ref_known(v___x_4421_, 1);
v___y_4378_ = v_a_4401_;
v___y_4379_ = v___x_4414_;
v_a_4380_ = v_a_4416_;
goto v___jp_4377_;
}
else
{
lean_object* v_a_4422_; 
lean_dec(v_a_4416_);
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
v___y_4388_ = v_a_4401_;
v___y_4389_ = v___x_4414_;
v_a_4390_ = v_a_4422_;
goto v___jp_4387_;
}
}
}
else
{
lean_object* v_a_4423_; 
v_a_4423_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4423_);
lean_dec_ref_known(v___x_4415_, 1);
v___y_4388_ = v_a_4401_;
v___y_4389_ = v___x_4414_;
v_a_4390_ = v_a_4423_;
goto v___jp_4387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4450_, lean_object* v_xs_4451_, lean_object* v_k_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4450_, v_xs_4451_, v_k_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4459_, lean_object* v_xs_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v___x_4466_; 
lean_inc(v_a_4464_);
lean_inc_ref(v_a_4463_);
lean_inc(v_a_4462_);
lean_inc_ref(v_a_4461_);
lean_inc_ref(v_f_4459_);
v___x_4466_ = lean_infer_type(v_f_4459_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; uint8_t v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4466_, 1);
v___x_4468_ = lean_unsigned_to_nat(0u);
v___x_4469_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4460_);
lean_inc_ref(v_f_4459_);
v___x_4470_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4470_, 0, v_f_4459_);
lean_closure_set(v___x_4470_, 1, v_xs_4460_);
lean_closure_set(v___x_4470_, 2, v___x_4468_);
lean_closure_set(v___x_4470_, 3, v___x_4469_);
lean_closure_set(v___x_4470_, 4, v___x_4468_);
lean_closure_set(v___x_4470_, 5, v___x_4469_);
lean_closure_set(v___x_4470_, 6, v_a_4467_);
v___x_4471_ = 0;
v___x_4472_ = lean_box(v___x_4471_);
v___x_4473_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4473_, 0, lean_box(0));
lean_closure_set(v___x_4473_, 1, v___x_4470_);
lean_closure_set(v___x_4473_, 2, v___x_4472_);
v___x_4474_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4459_, v_xs_4460_, v___x_4473_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
return v___x_4474_;
}
else
{
lean_dec_ref(v_xs_4460_);
lean_dec_ref(v_f_4459_);
return v___x_4466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4475_, lean_object* v_xs_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lean_Meta_mkAppOptM_x27(v_f_4475_, v_xs_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
lean_dec(v_a_4480_);
lean_dec_ref(v_a_4479_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
return v_res_4482_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4491_ = l_Lean_MessageData_ofFormat(v___x_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4492_, lean_object* v_h1_4493_, lean_object* v_h2_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4510_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4511_ = l_Lean_Expr_isAppOf(v_h2_4494_, v___x_4510_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; 
lean_inc_ref(v_h2_4494_);
v___x_4512_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; uint8_t v___x_4516_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v___x_4512_, 1);
v___x_4514_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4515_ = lean_unsigned_to_nat(3u);
v___x_4516_ = l_Lean_Expr_isAppOfArity(v_a_4513_, v___x_4514_, v___x_4515_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
lean_dec_ref(v_h1_4493_);
lean_dec_ref(v_motive_4492_);
v___x_4517_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4518_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4519_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4494_, v_a_4513_);
v___x_4520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4518_);
lean_ctor_set(v___x_4520_, 1, v___x_4519_);
v___x_4521_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4517_, v___x_4520_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
return v___x_4521_;
}
else
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4522_ = l_Lean_Expr_appFn_x21(v_a_4513_);
v___x_4523_ = l_Lean_Expr_appFn_x21(v___x_4522_);
v___x_4524_ = l_Lean_Expr_appArg_x21(v___x_4523_);
lean_dec_ref(v___x_4523_);
v___x_4525_ = l_Lean_Expr_appArg_x21(v___x_4522_);
lean_dec_ref(v___x_4522_);
v___x_4526_ = l_Lean_Expr_appArg_x21(v_a_4513_);
lean_dec(v_a_4513_);
lean_inc_ref(v___x_4524_);
v___x_4527_ = l_Lean_Meta_getLevel(v___x_4524_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4529_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v___x_4527_, 1);
lean_inc_ref(v_motive_4492_);
v___x_4529_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4492_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4553_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4532_ = v___x_4529_;
v_isShared_4533_ = v_isSharedCheck_4553_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4529_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4553_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
if (lean_obj_tag(v_a_4530_) == 7)
{
lean_object* v_body_4534_; 
v_body_4534_ = lean_ctor_get(v_a_4530_, 2);
lean_inc_ref(v_body_4534_);
lean_dec_ref_known(v_a_4530_, 3);
if (lean_obj_tag(v_body_4534_) == 3)
{
lean_object* v_u_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; 
v_u_4535_ = lean_ctor_get(v_body_4534_, 0);
lean_inc(v_u_4535_);
lean_dec_ref_known(v_body_4534_, 1);
v___x_4536_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4537_ = lean_box(0);
v___x_4538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4538_, 0, v_a_4528_);
lean_ctor_set(v___x_4538_, 1, v___x_4537_);
v___x_4539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4539_, 0, v_u_4535_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
v___x_4540_ = l_Lean_mkConst(v___x_4536_, v___x_4539_);
v___x_4541_ = lean_unsigned_to_nat(6u);
v___x_4542_ = lean_mk_empty_array_with_capacity(v___x_4541_);
v___x_4543_ = lean_array_push(v___x_4542_, v___x_4524_);
v___x_4544_ = lean_array_push(v___x_4543_, v___x_4525_);
v___x_4545_ = lean_array_push(v___x_4544_, v_motive_4492_);
v___x_4546_ = lean_array_push(v___x_4545_, v_h1_4493_);
v___x_4547_ = lean_array_push(v___x_4546_, v___x_4526_);
v___x_4548_ = lean_array_push(v___x_4547_, v_h2_4494_);
v___x_4549_ = l_Lean_mkAppN(v___x_4540_, v___x_4548_);
lean_dec_ref(v___x_4548_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4549_);
v___x_4551_ = v___x_4532_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
else
{
lean_dec_ref(v_body_4534_);
lean_del_object(v___x_4532_);
lean_dec(v_a_4528_);
lean_dec_ref(v___x_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v_h2_4494_);
lean_dec_ref(v_h1_4493_);
v___y_4501_ = v_a_4495_;
v___y_4502_ = v_a_4496_;
v___y_4503_ = v_a_4497_;
v___y_4504_ = v_a_4498_;
goto v___jp_4500_;
}
}
else
{
lean_del_object(v___x_4532_);
lean_dec(v_a_4530_);
lean_dec(v_a_4528_);
lean_dec_ref(v___x_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v_h2_4494_);
lean_dec_ref(v_h1_4493_);
v___y_4501_ = v_a_4495_;
v___y_4502_ = v_a_4496_;
v___y_4503_ = v_a_4497_;
v___y_4504_ = v_a_4498_;
goto v___jp_4500_;
}
}
}
else
{
lean_dec(v_a_4528_);
lean_dec_ref(v___x_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v_h2_4494_);
lean_dec_ref(v_h1_4493_);
lean_dec_ref(v_motive_4492_);
return v___x_4529_;
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec_ref(v___x_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v_h2_4494_);
lean_dec_ref(v_h1_4493_);
lean_dec_ref(v_motive_4492_);
v_a_4554_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4527_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4527_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4494_);
lean_dec_ref(v_h1_4493_);
lean_dec_ref(v_motive_4492_);
return v___x_4512_;
}
}
else
{
lean_object* v___x_4562_; 
lean_dec_ref(v_h2_4494_);
lean_dec_ref(v_motive_4492_);
v___x_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4562_, 0, v_h1_4493_);
return v___x_4562_;
}
v___jp_4500_:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4505_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4506_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4507_ = l_Lean_indentExpr(v_motive_4492_);
v___x_4508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4506_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
v___x_4509_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4505_, v___x_4508_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4563_, lean_object* v_h1_4564_, lean_object* v_h2_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_Meta_mkEqNDRec(v_motive_4563_, v_h1_4564_, v_h2_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4576_, lean_object* v_h1_4577_, lean_object* v_h2_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_){
_start:
{
lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___x_4594_; uint8_t v___x_4595_; 
v___x_4594_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4595_ = l_Lean_Expr_isAppOf(v_h2_4578_, v___x_4594_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; 
lean_inc_ref(v_h2_4578_);
v___x_4596_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; uint8_t v___x_4600_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref_known(v___x_4596_, 1);
v___x_4598_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4599_ = lean_unsigned_to_nat(3u);
v___x_4600_ = l_Lean_Expr_isAppOfArity(v_a_4597_, v___x_4598_, v___x_4599_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
lean_dec(v_a_4597_);
lean_dec_ref(v_h1_4577_);
lean_dec_ref(v_motive_4576_);
v___x_4601_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4602_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4603_ = l_Lean_indentExpr(v_h2_4578_);
v___x_4604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4604_, 0, v___x_4602_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4601_, v___x_4604_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
return v___x_4605_;
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4606_ = l_Lean_Expr_appFn_x21(v_a_4597_);
v___x_4607_ = l_Lean_Expr_appFn_x21(v___x_4606_);
v___x_4608_ = l_Lean_Expr_appArg_x21(v___x_4607_);
lean_dec_ref(v___x_4607_);
v___x_4609_ = l_Lean_Expr_appArg_x21(v___x_4606_);
lean_dec_ref(v___x_4606_);
v___x_4610_ = l_Lean_Expr_appArg_x21(v_a_4597_);
lean_dec(v_a_4597_);
lean_inc_ref(v___x_4608_);
v___x_4611_ = l_Lean_Meta_getLevel(v___x_4608_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4613_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
lean_inc(v_a_4612_);
lean_dec_ref_known(v___x_4611_, 1);
lean_inc_ref(v_motive_4576_);
v___x_4613_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4576_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4638_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4638_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4638_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
if (lean_obj_tag(v_a_4614_) == 7)
{
lean_object* v_body_4618_; 
v_body_4618_ = lean_ctor_get(v_a_4614_, 2);
lean_inc_ref(v_body_4618_);
lean_dec_ref_known(v_a_4614_, 3);
if (lean_obj_tag(v_body_4618_) == 7)
{
lean_object* v_body_4619_; 
v_body_4619_ = lean_ctor_get(v_body_4618_, 2);
lean_inc_ref(v_body_4619_);
lean_dec_ref_known(v_body_4618_, 3);
if (lean_obj_tag(v_body_4619_) == 3)
{
lean_object* v_u_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; 
v_u_4620_ = lean_ctor_get(v_body_4619_, 0);
lean_inc(v_u_4620_);
lean_dec_ref_known(v_body_4619_, 1);
v___x_4621_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4622_ = lean_box(0);
v___x_4623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4623_, 0, v_a_4612_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
v___x_4624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4624_, 0, v_u_4620_);
lean_ctor_set(v___x_4624_, 1, v___x_4623_);
v___x_4625_ = l_Lean_mkConst(v___x_4621_, v___x_4624_);
v___x_4626_ = lean_unsigned_to_nat(6u);
v___x_4627_ = lean_mk_empty_array_with_capacity(v___x_4626_);
v___x_4628_ = lean_array_push(v___x_4627_, v___x_4608_);
v___x_4629_ = lean_array_push(v___x_4628_, v___x_4609_);
v___x_4630_ = lean_array_push(v___x_4629_, v_motive_4576_);
v___x_4631_ = lean_array_push(v___x_4630_, v_h1_4577_);
v___x_4632_ = lean_array_push(v___x_4631_, v___x_4610_);
v___x_4633_ = lean_array_push(v___x_4632_, v_h2_4578_);
v___x_4634_ = l_Lean_mkAppN(v___x_4625_, v___x_4633_);
lean_dec_ref(v___x_4633_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4634_);
v___x_4636_ = v___x_4616_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
else
{
lean_dec_ref(v_body_4619_);
lean_del_object(v___x_4616_);
lean_dec(v_a_4612_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v_h2_4578_);
lean_dec_ref(v_h1_4577_);
v___y_4585_ = v_a_4579_;
v___y_4586_ = v_a_4580_;
v___y_4587_ = v_a_4581_;
v___y_4588_ = v_a_4582_;
goto v___jp_4584_;
}
}
else
{
lean_dec_ref(v_body_4618_);
lean_del_object(v___x_4616_);
lean_dec(v_a_4612_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v_h2_4578_);
lean_dec_ref(v_h1_4577_);
v___y_4585_ = v_a_4579_;
v___y_4586_ = v_a_4580_;
v___y_4587_ = v_a_4581_;
v___y_4588_ = v_a_4582_;
goto v___jp_4584_;
}
}
else
{
lean_del_object(v___x_4616_);
lean_dec(v_a_4614_);
lean_dec(v_a_4612_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v_h2_4578_);
lean_dec_ref(v_h1_4577_);
v___y_4585_ = v_a_4579_;
v___y_4586_ = v_a_4580_;
v___y_4587_ = v_a_4581_;
v___y_4588_ = v_a_4582_;
goto v___jp_4584_;
}
}
}
else
{
lean_dec(v_a_4612_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v_h2_4578_);
lean_dec_ref(v_h1_4577_);
lean_dec_ref(v_motive_4576_);
return v___x_4613_;
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v_h2_4578_);
lean_dec_ref(v_h1_4577_);
lean_dec_ref(v_motive_4576_);
v_a_4639_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4611_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4611_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4578_);
lean_dec_ref(v_h1_4577_);
lean_dec_ref(v_motive_4576_);
return v___x_4596_;
}
}
else
{
lean_object* v___x_4647_; 
lean_dec_ref(v_h2_4578_);
lean_dec_ref(v_motive_4576_);
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v_h1_4577_);
return v___x_4647_;
}
v___jp_4584_:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4589_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4590_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4591_ = l_Lean_indentExpr(v_motive_4576_);
v___x_4592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4590_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
v___x_4593_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4589_, v___x_4592_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
return v___x_4593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4648_, lean_object* v_h1_4649_, lean_object* v_h2_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_Meta_mkEqRec(v_motive_4648_, v_h1_4649_, v_h2_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_);
lean_dec(v_a_4654_);
lean_dec_ref(v_a_4653_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore(lean_object* v_00_u03b1_4661_, lean_object* v_00_u03b2_4662_, lean_object* v_h_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v___x_4670_; 
lean_inc_ref(v_00_u03b1_4661_);
v___x_4670_ = l_Lean_Meta_getLevel(v_00_u03b1_4661_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4683_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4683_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4683_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4675_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4676_ = lean_box(0);
v___x_4677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4677_, 0, v_a_4671_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
v___x_4678_ = l_Lean_mkConst(v___x_4675_, v___x_4677_);
v___x_4679_ = l_Lean_mkApp4(v___x_4678_, v_00_u03b1_4661_, v_00_u03b2_4662_, v_h_4663_, v_a_4664_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4679_);
v___x_4681_ = v___x_4673_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4679_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_dec_ref(v_a_4664_);
lean_dec_ref(v_h_4663_);
lean_dec_ref(v_00_u03b2_4662_);
lean_dec_ref(v_00_u03b1_4661_);
v_a_4684_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4670_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4670_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore___boxed(lean_object* v_00_u03b1_4692_, lean_object* v_00_u03b2_4693_, lean_object* v_h_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_Meta_mkEqMPCore(v_00_u03b1_4692_, v_00_u03b2_4693_, v_h_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4702_, lean_object* v_pr_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v___x_4709_; 
lean_inc_ref(v_eqProof_4702_);
v___x_4709_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_eqProof_4702_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
lean_inc(v_a_4710_);
lean_dec_ref_known(v___x_4709_, 1);
v___x_4711_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4712_ = lean_unsigned_to_nat(3u);
v___x_4713_ = l_Lean_Expr_isAppOfArity(v_a_4710_, v___x_4711_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
lean_dec_ref(v_pr_4703_);
v___x_4714_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4715_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4716_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_eqProof_4702_, v_a_4710_);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4714_, v___x_4717_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_);
return v___x_4718_;
}
else
{
lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4719_ = l_Lean_Expr_appFn_x21(v_a_4710_);
v___x_4720_ = l_Lean_Expr_appArg_x21(v___x_4719_);
lean_dec_ref(v___x_4719_);
v___x_4721_ = l_Lean_Expr_appArg_x21(v_a_4710_);
lean_dec(v_a_4710_);
v___x_4722_ = l_Lean_Meta_mkEqMPCore(v___x_4720_, v___x_4721_, v_eqProof_4702_, v_pr_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_);
return v___x_4722_;
}
}
else
{
lean_dec_ref(v_pr_4703_);
lean_dec_ref(v_eqProof_4702_);
return v___x_4709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4723_, lean_object* v_pr_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Lean_Meta_mkEqMP(v_eqProof_4723_, v_pr_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_);
lean_dec(v_a_4728_);
lean_dec_ref(v_a_4727_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4735_, lean_object* v_pr_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4742_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4743_ = lean_unsigned_to_nat(2u);
v___x_4744_ = lean_mk_empty_array_with_capacity(v___x_4743_);
v___x_4745_ = lean_array_push(v___x_4744_, v_eqProof_4735_);
v___x_4746_ = lean_array_push(v___x_4745_, v_pr_4736_);
v___x_4747_ = l_Lean_Meta_mkAppM(v___x_4742_, v___x_4746_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4748_, lean_object* v_pr_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Lean_Meta_mkEqMPR(v_eqProof_4748_, v_pr_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v___f_4762_; lean_object* v___x_12332__overap_4763_; lean_object* v___x_4764_; 
v___f_4762_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12332__overap_4763_ = lean_panic_fn_borrowed(v___f_4762_, v_msg_4756_);
lean_inc(v___y_4760_);
lean_inc_ref(v___y_4759_);
lean_inc(v___y_4758_);
lean_inc_ref(v___y_4757_);
v___x_4764_ = lean_apply_5(v___x_12332__overap_4763_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, lean_box(0));
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4772_, uint8_t v_skipRealize_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v___x_4776_; lean_object* v_env_4777_; uint8_t v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4776_ = lean_st_ref_get(v___y_4774_);
v_env_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc_ref(v_env_4777_);
lean_dec(v___x_4776_);
v___x_4778_ = l_Lean_Environment_contains(v_env_4777_, v_constName_4772_, v_skipRealize_4773_);
v___x_4779_ = lean_box(v___x_4778_);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4781_, lean_object* v_skipRealize_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
uint8_t v_skipRealize_boxed_4785_; lean_object* v_res_4786_; 
v_skipRealize_boxed_4785_ = lean_unbox(v_skipRealize_4782_);
v_res_4786_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4781_, v_skipRealize_boxed_4785_, v___y_4783_);
lean_dec(v___y_4783_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4787_, uint8_t v_skipRealize_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4787_, v_skipRealize_4788_, v___y_4792_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4795_, lean_object* v_skipRealize_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
uint8_t v_skipRealize_boxed_4802_; lean_object* v_res_4803_; 
v_skipRealize_boxed_4802_ = lean_unbox(v_skipRealize_4796_);
v_res_4803_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4795_, v_skipRealize_boxed_4802_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
lean_dec(v___y_4800_);
lean_dec_ref(v___y_4799_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___x_4804_, uint8_t v___x_4805_, lean_object* v_P_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; lean_object* v___x_4816_; 
v___x_4812_ = lean_unsigned_to_nat(1u);
v___x_4813_ = lean_mk_empty_array_with_capacity(v___x_4812_);
lean_inc_ref(v_P_4806_);
v___x_4814_ = lean_array_push(v___x_4813_, v_P_4806_);
v___x_4815_ = 1;
v___x_4816_ = l_Lean_Meta_mkLambdaFVars(v___x_4814_, v_P_4806_, v___x_4804_, v___x_4805_, v___x_4804_, v___x_4805_, v___x_4815_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec_ref(v___x_4814_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___x_4817_, lean_object* v___x_4818_, lean_object* v_P_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
uint8_t v___x_13775__boxed_4825_; uint8_t v___x_13776__boxed_4826_; lean_object* v_res_4827_; 
v___x_13775__boxed_4825_ = lean_unbox(v___x_4817_);
v___x_13776__boxed_4826_ = lean_unbox(v___x_4818_);
v_res_4827_ = l_Lean_Meta_mkNoConfusion___lam__0(v___x_13775__boxed_4825_, v___x_13776__boxed_4826_, v_P_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
return v_res_4827_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4829_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4830_ = l_Lean_stringToMessageData(v___x_4829_);
return v___x_4830_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4832_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4833_ = l_Lean_stringToMessageData(v___x_4832_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4834_, lean_object* v_b_4835_, lean_object* v_i_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_stop_4842_; lean_object* v_step_4843_; lean_object* v_a_4845_; uint8_t v___x_4848_; 
v_stop_4842_ = lean_ctor_get(v_range_4834_, 1);
v_step_4843_ = lean_ctor_get(v_range_4834_, 2);
v___x_4848_ = lean_nat_dec_lt(v_i_4836_, v_stop_4842_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; 
lean_dec(v_i_4836_);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v_b_4835_);
return v___x_4849_;
}
else
{
lean_object* v___x_4850_; 
lean_inc(v___y_4840_);
lean_inc_ref(v___y_4839_);
lean_inc(v___y_4838_);
lean_inc_ref(v___y_4837_);
lean_inc_ref(v_b_4835_);
v___x_4850_ = lean_infer_type(v_b_4835_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4852_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref_known(v___x_4850_, 1);
v___x_4852_ = l_Lean_Meta_whnfForall(v_a_4851_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref_known(v___x_4852_, 1);
v___x_4854_ = l_Lean_Expr_bindingDomain_x21(v_a_4853_);
lean_dec(v_a_4853_);
lean_inc(v___y_4840_);
lean_inc_ref(v___y_4839_);
lean_inc(v___y_4838_);
lean_inc_ref(v___y_4837_);
v___x_4855_ = lean_whnf(v___x_4854_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_a_4856_);
lean_dec_ref_known(v___x_4855_, 1);
v___x_4857_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4858_ = lean_unsigned_to_nat(4u);
v___x_4859_ = l_Lean_Expr_isAppOfArity(v_a_4856_, v___x_4857_, v___x_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; 
v___x_4860_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4861_ = lean_unsigned_to_nat(3u);
v___x_4862_ = l_Lean_Expr_isAppOfArity(v_a_4856_, v___x_4860_, v___x_4861_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; 
lean_dec(v_i_4836_);
lean_inc(v___y_4840_);
lean_inc_ref(v___y_4839_);
lean_inc(v___y_4838_);
lean_inc_ref(v___y_4837_);
v___x_4863_ = lean_infer_type(v_b_4835_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4865_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4866_ = l_Lean_MessageData_ofExpr(v_a_4856_);
v___x_4867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4865_);
lean_ctor_set(v___x_4867_, 1, v___x_4866_);
v___x_4868_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4867_);
lean_ctor_set(v___x_4869_, 1, v___x_4868_);
v___x_4870_ = lean_unsigned_to_nat(30u);
v___x_4871_ = l_Lean_inlineExpr(v_a_4864_, v___x_4870_);
v___x_4872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4869_);
lean_ctor_set(v___x_4872_, 1, v___x_4871_);
v___x_4873_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4872_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
else
{
lean_dec(v_a_4856_);
return v___x_4863_;
}
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4882_ = l_Lean_Expr_appFn_x21(v_a_4856_);
lean_dec(v_a_4856_);
v___x_4883_ = l_Lean_Expr_appArg_x21(v___x_4882_);
lean_dec_ref(v___x_4882_);
v___x_4884_ = l_Lean_Meta_mkEqRefl(v___x_4883_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v___x_4886_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
lean_inc(v_a_4885_);
lean_dec_ref_known(v___x_4884_, 1);
v___x_4886_ = l_Lean_Expr_app___override(v_b_4835_, v_a_4885_);
v_a_4845_ = v___x_4886_;
goto v___jp_4844_;
}
else
{
lean_dec(v_i_4836_);
lean_dec_ref(v_b_4835_);
return v___x_4884_;
}
}
}
else
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4887_ = l_Lean_Expr_appFn_x21(v_a_4856_);
lean_dec(v_a_4856_);
v___x_4888_ = l_Lean_Expr_appFn_x21(v___x_4887_);
lean_dec_ref(v___x_4887_);
v___x_4889_ = l_Lean_Expr_appArg_x21(v___x_4888_);
lean_dec_ref(v___x_4888_);
v___x_4890_ = l_Lean_Meta_mkHEqRefl(v___x_4889_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4892_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref_known(v___x_4890_, 1);
v___x_4892_ = l_Lean_Expr_app___override(v_b_4835_, v_a_4891_);
v_a_4845_ = v___x_4892_;
goto v___jp_4844_;
}
else
{
lean_dec(v_i_4836_);
lean_dec_ref(v_b_4835_);
return v___x_4890_;
}
}
}
else
{
lean_dec(v_i_4836_);
lean_dec_ref(v_b_4835_);
return v___x_4855_;
}
}
else
{
lean_dec(v_i_4836_);
lean_dec_ref(v_b_4835_);
return v___x_4852_;
}
}
else
{
lean_dec(v_i_4836_);
lean_dec_ref(v_b_4835_);
return v___x_4850_;
}
}
v___jp_4844_:
{
lean_object* v___x_4846_; 
v___x_4846_ = lean_nat_add(v_i_4836_, v_step_4843_);
lean_dec(v_i_4836_);
v_b_4835_ = v_a_4845_;
v_i_4836_ = v___x_4846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4893_, lean_object* v_b_4894_, lean_object* v_i_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4893_, v_b_4894_, v_i_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
lean_dec_ref(v_range_4893_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4902_, lean_object* v_b_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v___x_4909_; 
lean_inc(v___y_4907_);
lean_inc_ref(v___y_4906_);
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
v___x_4909_ = lean_apply_6(v_k_4902_, v_b_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, lean_box(0));
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4910_, lean_object* v_b_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v_res_4917_; 
v_res_4917_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4910_, v_b_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4918_, uint8_t v_bi_4919_, lean_object* v_type_4920_, lean_object* v_k_4921_, uint8_t v_kind_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v___f_4928_; lean_object* v___x_4929_; 
v___f_4928_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4928_, 0, v_k_4921_);
v___x_4929_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4918_, v_bi_4919_, v_type_4920_, v___f_4928_, v_kind_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4929_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4929_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
v_a_4938_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4929_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4929_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_4946_, lean_object* v_bi_4947_, lean_object* v_type_4948_, lean_object* v_k_4949_, lean_object* v_kind_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
uint8_t v_bi_boxed_4956_; uint8_t v_kind_boxed_4957_; lean_object* v_res_4958_; 
v_bi_boxed_4956_ = lean_unbox(v_bi_4947_);
v_kind_boxed_4957_ = lean_unbox(v_kind_4950_);
v_res_4958_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4946_, v_bi_boxed_4956_, v_type_4948_, v_k_4949_, v_kind_boxed_4957_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_4959_, lean_object* v_type_4960_, lean_object* v_k_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
uint8_t v___x_4967_; uint8_t v___x_4968_; lean_object* v___x_4969_; 
v___x_4967_ = 0;
v___x_4968_ = 0;
v___x_4969_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4959_, v___x_4967_, v_type_4960_, v_k_4961_, v___x_4968_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_4970_, lean_object* v_type_4971_, lean_object* v_k_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_4970_, v_type_4971_, v_k_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
return v_res_4978_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4985_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_4986_ = l_Lean_MessageData_ofFormat(v___x_4985_);
return v___x_4986_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6(void){
_start:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__5));
v___x_4989_ = l_Lean_stringToMessageData(v___x_4988_);
return v___x_4989_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4991_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__7));
v___x_4992_ = l_Lean_stringToMessageData(v___x_4991_);
return v___x_4992_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4996_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_4997_ = l_Lean_MessageData_ofFormat(v___x_4996_);
return v___x_4997_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5003_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5004_ = l_Lean_stringToMessageData(v___x_5003_);
return v___x_5004_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__18(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5006_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__17));
v___x_5007_ = l_Lean_stringToMessageData(v___x_5006_);
return v___x_5007_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__19(void){
_start:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__14));
v___x_5009_ = l_Lean_MessageData_ofName(v___x_5008_);
return v___x_5009_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__22(void){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5012_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5013_ = lean_unsigned_to_nat(10u);
v___x_5014_ = lean_unsigned_to_nat(511u);
v___x_5015_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__20));
v___x_5016_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5017_ = l_mkPanicMessageWithDecl(v___x_5016_, v___x_5015_, v___x_5014_, v___x_5013_, v___x_5012_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5021_, lean_object* v_h_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_){
_start:
{
lean_object* v___x_5028_; 
lean_inc(v_a_5026_);
lean_inc_ref(v_a_5025_);
lean_inc(v_a_5024_);
lean_inc_ref(v_a_5023_);
lean_inc_ref(v_h_5022_);
v___x_5028_ = lean_infer_type(v_h_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5030_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref_known(v___x_5028_, 1);
lean_inc(v_a_5026_);
lean_inc_ref(v_a_5025_);
lean_inc(v_a_5024_);
lean_inc_ref(v_a_5023_);
v___x_5030_ = lean_whnf(v_a_5029_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; uint8_t v___x_5034_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref_known(v___x_5030_, 1);
v___x_5032_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5033_ = lean_unsigned_to_nat(3u);
v___x_5034_ = l_Lean_Expr_isAppOfArity(v_a_5031_, v___x_5032_, v___x_5033_);
if (v___x_5034_ == 0)
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
lean_dec_ref(v_target_5021_);
v___x_5035_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5036_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5037_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5022_, v_a_5031_);
v___x_5038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5036_);
lean_ctor_set(v___x_5038_, 1, v___x_5037_);
v___x_5039_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5035_, v___x_5038_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
return v___x_5039_;
}
else
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___x_5058_; 
v___x_5040_ = l_Lean_Expr_appFn_x21(v_a_5031_);
v___x_5041_ = l_Lean_Expr_appFn_x21(v___x_5040_);
v___x_5042_ = l_Lean_Expr_appArg_x21(v___x_5041_);
lean_dec_ref(v___x_5041_);
v___x_5043_ = l_Lean_Expr_appArg_x21(v___x_5040_);
lean_dec_ref(v___x_5040_);
v___x_5044_ = l_Lean_Expr_appArg_x21(v_a_5031_);
lean_dec(v_a_5031_);
v___x_5058_ = l_Lean_Meta_whnfD(v___x_5042_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5059_; lean_object* v___y_5061_; lean_object* v___y_5062_; lean_object* v___y_5063_; lean_object* v___y_5064_; lean_object* v___x_5070_; 
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_a_5059_);
lean_dec_ref_known(v___x_5058_, 1);
v___x_5070_ = l_Lean_Expr_getAppFn(v_a_5059_);
if (lean_obj_tag(v___x_5070_) == 4)
{
lean_object* v_declName_5071_; lean_object* v_us_5072_; lean_object* v___x_5073_; lean_object* v_env_5074_; uint8_t v___x_5075_; lean_object* v___x_5076_; 
v_declName_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc(v_declName_5071_);
v_us_5072_ = lean_ctor_get(v___x_5070_, 1);
lean_inc(v_us_5072_);
lean_dec_ref_known(v___x_5070_, 2);
v___x_5073_ = lean_st_ref_get(v_a_5026_);
v_env_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc_ref(v_env_5074_);
lean_dec(v___x_5073_);
v___x_5075_ = 0;
v___x_5076_ = l_Lean_Environment_find_x3f(v_env_5074_, v_declName_5071_, v___x_5075_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_dec(v_us_5072_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v___y_5061_ = v_a_5023_;
v___y_5062_ = v_a_5024_;
v___y_5063_ = v_a_5025_;
v___y_5064_ = v_a_5026_;
goto v___jp_5060_;
}
else
{
lean_object* v_val_5077_; 
v_val_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_val_5077_);
lean_dec_ref_known(v___x_5076_, 1);
if (lean_obj_tag(v_val_5077_) == 5)
{
lean_object* v_val_5078_; lean_object* v___x_5079_; 
v_val_5078_ = lean_ctor_get(v_val_5077_, 0);
lean_inc_ref(v_val_5078_);
lean_dec_ref_known(v_val_5077_, 1);
lean_inc_ref(v_target_5021_);
v___x_5079_ = l_Lean_Meta_getLevel(v_target_5021_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v___x_5081_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref_known(v___x_5079_, 1);
lean_inc_ref(v___x_5043_);
v___x_5081_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5043_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v_a_5082_; 
v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_a_5082_);
lean_dec_ref_known(v___x_5081_, 1);
if (lean_obj_tag(v_a_5082_) == 1)
{
lean_object* v_val_5083_; lean_object* v_fst_5084_; lean_object* v_snd_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5299_; 
v_val_5083_ = lean_ctor_get(v_a_5082_, 0);
lean_inc(v_val_5083_);
lean_dec_ref_known(v_a_5082_, 1);
v_fst_5084_ = lean_ctor_get(v_val_5083_, 0);
v_snd_5085_ = lean_ctor_get(v_val_5083_, 1);
v_isSharedCheck_5299_ = !lean_is_exclusive(v_val_5083_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5087_ = v_val_5083_;
v_isShared_5088_ = v_isSharedCheck_5299_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_snd_5085_);
lean_inc(v_fst_5084_);
lean_dec(v_val_5083_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5299_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5089_; 
lean_inc_ref(v___x_5044_);
v___x_5089_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5044_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_object* v_a_5090_; 
v_a_5090_ = lean_ctor_get(v___x_5089_, 0);
lean_inc(v_a_5090_);
lean_dec_ref_known(v___x_5089_, 1);
if (lean_obj_tag(v_a_5090_) == 1)
{
lean_object* v_val_5091_; lean_object* v_fst_5092_; lean_object* v_snd_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5290_; 
v_val_5091_ = lean_ctor_get(v_a_5090_, 0);
lean_inc(v_val_5091_);
lean_dec_ref_known(v_a_5090_, 1);
v_fst_5092_ = lean_ctor_get(v_val_5091_, 0);
v_snd_5093_ = lean_ctor_get(v_val_5091_, 1);
v_isSharedCheck_5290_ = !lean_is_exclusive(v_val_5091_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5095_ = v_val_5091_;
v_isShared_5096_ = v_isSharedCheck_5290_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_snd_5093_);
lean_inc(v_fst_5092_);
lean_dec(v_val_5091_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5290_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v_toConstantVal_5097_; lean_object* v_cidx_5098_; lean_object* v_numParams_5099_; lean_object* v_numFields_5100_; lean_object* v_cidx_5101_; uint8_t v___x_5102_; 
v_toConstantVal_5097_ = lean_ctor_get(v_fst_5084_, 0);
lean_inc_ref(v_toConstantVal_5097_);
v_cidx_5098_ = lean_ctor_get(v_fst_5084_, 2);
lean_inc(v_cidx_5098_);
v_numParams_5099_ = lean_ctor_get(v_fst_5084_, 3);
lean_inc(v_numParams_5099_);
v_numFields_5100_ = lean_ctor_get(v_fst_5084_, 4);
lean_inc(v_numFields_5100_);
lean_dec(v_fst_5084_);
v_cidx_5101_ = lean_ctor_get(v_fst_5092_, 2);
lean_inc(v_cidx_5101_);
lean_dec(v_fst_5092_);
v___x_5102_ = lean_nat_dec_eq(v_cidx_5098_, v_cidx_5101_);
lean_dec(v_cidx_5101_);
lean_dec(v_cidx_5098_);
if (v___x_5102_ == 0)
{
lean_object* v_toConstantVal_5103_; lean_object* v_name_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v_a_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v_a_5111_; uint8_t v___x_5133_; 
lean_dec(v_numFields_5100_);
lean_dec(v_numParams_5099_);
lean_dec_ref(v_toConstantVal_5097_);
lean_dec(v_snd_5093_);
lean_dec(v_snd_5085_);
v_toConstantVal_5103_ = lean_ctor_get(v_val_5078_, 0);
lean_inc_ref(v_toConstantVal_5103_);
lean_dec_ref(v_val_5078_);
v_name_5104_ = lean_ctor_get(v_toConstantVal_5103_, 0);
lean_inc(v_name_5104_);
lean_dec_ref(v_toConstantVal_5103_);
v___x_5105_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5106_ = l_Lean_Name_str___override(v_name_5104_, v___x_5105_);
lean_inc(v___x_5106_);
v___x_5107_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5106_, v___x_5034_, v_a_5026_);
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_a_5108_);
lean_dec_ref(v___x_5107_);
v___x_5109_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__14));
v___x_5110_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5109_, v___x_5034_, v_a_5026_);
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5111_);
lean_dec_ref(v___x_5110_);
v___x_5133_ = lean_unbox(v_a_5108_);
lean_dec(v_a_5108_);
if (v___x_5133_ == 0)
{
lean_dec(v_a_5111_);
lean_dec(v_a_5080_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
goto v___jp_5112_;
}
else
{
uint8_t v___x_5134_; 
v___x_5134_ = lean_unbox(v_a_5111_);
lean_dec(v_a_5111_);
if (v___x_5134_ == 0)
{
lean_dec(v_a_5080_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
goto v___jp_5112_;
}
else
{
lean_object* v___x_5135_; lean_object* v_dummy_5136_; lean_object* v_nargs_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
lean_del_object(v___x_5095_);
lean_del_object(v___x_5087_);
v___x_5135_ = l_Lean_mkConst(v___x_5106_, v_us_5072_);
v_dummy_5136_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5137_ = l_Lean_Expr_getAppNumArgs(v_a_5059_);
lean_inc(v_nargs_5137_);
v___x_5138_ = lean_mk_array(v_nargs_5137_, v_dummy_5136_);
v___x_5139_ = lean_unsigned_to_nat(1u);
v___x_5140_ = lean_nat_sub(v_nargs_5137_, v___x_5139_);
lean_dec(v_nargs_5137_);
lean_inc_n(v_a_5059_, 2);
v___x_5141_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5059_, v___x_5138_, v___x_5140_);
v___x_5142_ = l_Lean_mkAppN(v___x_5135_, v___x_5141_);
lean_dec_ref(v___x_5141_);
v___x_5143_ = l_Lean_Meta_getLevel(v_a_5059_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5166_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5146_ = v___x_5143_;
v_isShared_5147_ = v_isSharedCheck_5166_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5143_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5166_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5164_; 
v___x_5148_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5149_ = lean_box(0);
v___x_5150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5150_, 0, v_a_5080_);
lean_ctor_set(v___x_5150_, 1, v___x_5149_);
v___x_5151_ = l_Lean_mkConst(v___x_5148_, v___x_5150_);
v___x_5152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5152_, 0, v_a_5144_);
lean_ctor_set(v___x_5152_, 1, v___x_5149_);
v___x_5153_ = l_Lean_mkConst(v___x_5109_, v___x_5152_);
v___x_5154_ = lean_unsigned_to_nat(5u);
v___x_5155_ = lean_mk_empty_array_with_capacity(v___x_5154_);
v___x_5156_ = lean_array_push(v___x_5155_, v_a_5059_);
v___x_5157_ = lean_array_push(v___x_5156_, v___x_5142_);
v___x_5158_ = lean_array_push(v___x_5157_, v___x_5043_);
v___x_5159_ = lean_array_push(v___x_5158_, v___x_5044_);
v___x_5160_ = lean_array_push(v___x_5159_, v_h_5022_);
v___x_5161_ = l_Lean_mkAppN(v___x_5153_, v___x_5160_);
lean_dec_ref(v___x_5160_);
v___x_5162_ = l_Lean_mkAppB(v___x_5151_, v_target_5021_, v___x_5161_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 0, v___x_5162_);
v___x_5164_ = v___x_5146_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v___x_5162_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
else
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
lean_dec_ref(v___x_5142_);
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v_a_5167_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___x_5143_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5143_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
v___x_5172_ = v___x_5169_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
}
v___jp_5112_:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5116_; 
v___x_5113_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5114_ = l_Lean_MessageData_ofName(v___x_5106_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set_tag(v___x_5095_, 7);
lean_ctor_set(v___x_5095_, 1, v___x_5114_);
lean_ctor_set(v___x_5095_, 0, v___x_5113_);
v___x_5116_ = v___x_5095_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v___x_5113_);
lean_ctor_set(v_reuseFailAlloc_5132_, 1, v___x_5114_);
v___x_5116_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
lean_object* v___x_5117_; lean_object* v___x_5119_; 
v___x_5117_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__18, &l_Lean_Meta_mkNoConfusion___closed__18_once, _init_l_Lean_Meta_mkNoConfusion___closed__18);
if (v_isShared_5088_ == 0)
{
lean_ctor_set_tag(v___x_5087_, 7);
lean_ctor_set(v___x_5087_, 1, v___x_5117_);
lean_ctor_set(v___x_5087_, 0, v___x_5116_);
v___x_5119_ = v___x_5087_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5116_);
lean_ctor_set(v_reuseFailAlloc_5131_, 1, v___x_5117_);
v___x_5119_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5130_; 
v___x_5120_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__19, &l_Lean_Meta_mkNoConfusion___closed__19_once, _init_l_Lean_Meta_mkNoConfusion___closed__19);
v___x_5121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5121_, 0, v___x_5119_);
lean_ctor_set(v___x_5121_, 1, v___x_5120_);
v___x_5122_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5121_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5125_ = v___x_5122_;
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5122_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
}
else
{
lean_object* v___x_5175_; uint8_t v___x_5176_; 
lean_dec_ref(v_val_5078_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
v___x_5175_ = lean_unsigned_to_nat(0u);
v___x_5176_ = lean_nat_dec_eq(v_numFields_5100_, v___x_5175_);
lean_dec(v_numFields_5100_);
if (v___x_5176_ == 0)
{
lean_object* v_name_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___y_5184_; lean_object* v___x_5268_; lean_object* v_a_5269_; uint8_t v___x_5270_; 
v_name_5177_ = lean_ctor_get(v_toConstantVal_5097_, 0);
lean_inc(v_name_5177_);
lean_dec_ref(v_toConstantVal_5097_);
v___x_5178_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5179_ = l_Lean_Name_str___override(v_name_5177_, v___x_5178_);
lean_inc(v___x_5179_);
v___x_5268_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5179_, v___x_5034_, v_a_5026_);
v_a_5269_ = lean_ctor_get(v___x_5268_, 0);
lean_inc(v_a_5269_);
lean_dec_ref(v___x_5268_);
v___x_5270_ = lean_unbox(v_a_5269_);
lean_dec(v_a_5269_);
if (v___x_5270_ == 0)
{
lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5274_; 
lean_dec(v_numParams_5099_);
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_dec(v_snd_5085_);
lean_dec(v_a_5080_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v___x_5271_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5272_ = l_Lean_MessageData_ofName(v___x_5179_);
if (v_isShared_5088_ == 0)
{
lean_ctor_set_tag(v___x_5087_, 7);
lean_ctor_set(v___x_5087_, 1, v___x_5272_);
lean_ctor_set(v___x_5087_, 0, v___x_5271_);
v___x_5274_ = v___x_5087_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5271_);
lean_ctor_set(v_reuseFailAlloc_5284_, 1, v___x_5272_);
v___x_5274_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
lean_object* v___x_5275_; lean_object* v_a_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5283_; 
v___x_5275_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5274_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
v_a_5276_ = lean_ctor_get(v___x_5275_, 0);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5275_);
if (v_isSharedCheck_5283_ == 0)
{
v___x_5278_ = v___x_5275_;
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_a_5276_);
lean_dec(v___x_5275_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5281_; 
if (v_isShared_5279_ == 0)
{
v___x_5281_ = v___x_5278_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
v___x_5281_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
return v___x_5281_;
}
}
}
}
else
{
lean_del_object(v___x_5087_);
v___y_5181_ = v_a_5023_;
v___y_5182_ = v_a_5024_;
v___y_5183_ = v_a_5025_;
v___y_5184_ = v_a_5026_;
goto v___jp_5180_;
}
v___jp_5180_:
{
lean_object* v___x_5185_; 
lean_inc(v___x_5179_);
v___x_5185_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___x_5179_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v_a_5186_; lean_object* v_dummy_5187_; lean_object* v_nargs_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v_type_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5257_; 
v_a_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_a_5186_);
lean_dec_ref_known(v___x_5185_, 1);
v_dummy_5187_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5188_ = l_Lean_Expr_getAppNumArgs(v_a_5059_);
lean_inc(v_nargs_5188_);
v___x_5189_ = lean_mk_array(v_nargs_5188_, v_dummy_5187_);
v___x_5190_ = lean_unsigned_to_nat(1u);
v___x_5191_ = lean_nat_sub(v_nargs_5188_, v___x_5190_);
lean_dec(v_nargs_5188_);
v___x_5192_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5059_, v___x_5189_, v___x_5191_);
lean_inc(v_numParams_5099_);
v___x_5193_ = l_Array_toSubarray___redArg(v___x_5192_, v___x_5175_, v_numParams_5099_);
v___x_5194_ = lean_array_get_size(v_snd_5085_);
v_type_5195_ = lean_ctor_get(v_a_5186_, 2);
v_isSharedCheck_5257_ = !lean_is_exclusive(v_a_5186_);
if (v_isSharedCheck_5257_ == 0)
{
lean_object* v_unused_5258_; lean_object* v_unused_5259_; 
v_unused_5258_ = lean_ctor_get(v_a_5186_, 1);
lean_dec(v_unused_5258_);
v_unused_5259_ = lean_ctor_get(v_a_5186_, 0);
lean_dec(v_unused_5259_);
v___x_5197_ = v_a_5186_;
v_isShared_5198_ = v_isSharedCheck_5257_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_type_5195_);
lean_dec(v_a_5186_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5257_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v_start_5199_; lean_object* v_stop_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; uint8_t v___x_5213_; 
v_start_5199_ = lean_ctor_get(v___x_5193_, 1);
v_stop_5200_ = lean_ctor_get(v___x_5193_, 2);
lean_inc(v_numParams_5099_);
v___x_5201_ = l_Array_toSubarray___redArg(v_snd_5085_, v_numParams_5099_, v___x_5194_);
v___x_5202_ = lean_array_get_size(v_snd_5093_);
v___x_5203_ = l_Subarray_copy___redArg(v___x_5201_);
v___x_5204_ = l_Array_toSubarray___redArg(v_snd_5093_, v_numParams_5099_, v___x_5202_);
v___x_5205_ = l_Subarray_copy___redArg(v___x_5204_);
v___x_5206_ = l_Lean_Expr_getNumHeadForalls(v_type_5195_);
lean_dec_ref(v_type_5195_);
v___x_5207_ = lean_nat_sub(v_stop_5200_, v_start_5199_);
v___x_5208_ = lean_array_get_size(v___x_5203_);
v___x_5209_ = lean_nat_add(v___x_5207_, v___x_5208_);
lean_dec(v___x_5207_);
v___x_5210_ = lean_array_get_size(v___x_5205_);
v___x_5211_ = lean_nat_add(v___x_5209_, v___x_5210_);
lean_dec(v___x_5209_);
v___x_5212_ = lean_nat_add(v___x_5211_, v___x_5033_);
lean_dec(v___x_5211_);
v___x_5213_ = lean_nat_dec_le(v___x_5212_, v___x_5206_);
if (v___x_5213_ == 0)
{
lean_object* v___x_5214_; lean_object* v___x_5215_; 
lean_dec(v___x_5212_);
lean_dec(v___x_5206_);
lean_dec_ref(v___x_5205_);
lean_dec_ref(v___x_5203_);
lean_del_object(v___x_5197_);
lean_dec_ref(v___x_5193_);
lean_dec(v___x_5179_);
lean_del_object(v___x_5095_);
lean_dec(v_a_5080_);
lean_dec(v_us_5072_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v___x_5214_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__22, &l_Lean_Meta_mkNoConfusion___closed__22_once, _init_l_Lean_Meta_mkNoConfusion___closed__22);
v___x_5215_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5214_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
return v___x_5215_;
}
else
{
lean_object* v___x_5217_; 
if (v_isShared_5096_ == 0)
{
lean_ctor_set_tag(v___x_5095_, 1);
lean_ctor_set(v___x_5095_, 1, v_us_5072_);
lean_ctor_set(v___x_5095_, 0, v_a_5080_);
v___x_5217_ = v___x_5095_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_a_5080_);
lean_ctor_set(v_reuseFailAlloc_5256_, 1, v_us_5072_);
v___x_5217_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5228_; 
v___x_5218_ = l_Lean_mkConst(v___x_5179_, v___x_5217_);
v___x_5219_ = l_Subarray_copy___redArg(v___x_5193_);
v___x_5220_ = l_Lean_mkAppN(v___x_5218_, v___x_5219_);
lean_dec_ref(v___x_5219_);
v___x_5221_ = lean_mk_empty_array_with_capacity(v___x_5190_);
v___x_5222_ = lean_array_push(v___x_5221_, v_target_5021_);
v___x_5223_ = l_Array_append___redArg(v___x_5222_, v___x_5203_);
lean_dec_ref(v___x_5203_);
v___x_5224_ = l_Array_append___redArg(v___x_5223_, v___x_5205_);
lean_dec_ref(v___x_5205_);
v___x_5225_ = l_Lean_mkAppN(v___x_5220_, v___x_5224_);
lean_dec_ref(v___x_5224_);
v___x_5226_ = lean_nat_sub(v___x_5206_, v___x_5212_);
lean_dec(v___x_5212_);
lean_dec(v___x_5206_);
if (v_isShared_5198_ == 0)
{
lean_ctor_set(v___x_5197_, 2, v___x_5190_);
lean_ctor_set(v___x_5197_, 1, v___x_5226_);
lean_ctor_set(v___x_5197_, 0, v___x_5175_);
v___x_5228_ = v___x_5197_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5175_);
lean_ctor_set(v_reuseFailAlloc_5255_, 1, v___x_5226_);
lean_ctor_set(v_reuseFailAlloc_5255_, 2, v___x_5190_);
v___x_5228_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
lean_object* v___x_5229_; 
v___x_5229_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5228_, v___x_5225_, v___x_5175_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
lean_dec_ref(v___x_5228_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5231_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
lean_inc_n(v_a_5230_, 2);
lean_dec_ref_known(v___x_5229_, 1);
lean_inc(v___y_5184_);
lean_inc_ref(v___y_5183_);
lean_inc(v___y_5182_);
lean_inc_ref(v___y_5181_);
v___x_5231_ = lean_infer_type(v_a_5230_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
if (lean_obj_tag(v___x_5231_) == 0)
{
lean_object* v_a_5232_; lean_object* v___x_5233_; 
v_a_5232_ = lean_ctor_get(v___x_5231_, 0);
lean_inc(v_a_5232_);
lean_dec_ref_known(v___x_5231_, 1);
v___x_5233_ = l_Lean_Meta_whnfForall(v_a_5232_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5254_; 
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5236_ = v___x_5233_;
v_isShared_5237_ = v_isSharedCheck_5254_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5233_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5254_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5238_; uint8_t v___x_5239_; 
v___x_5238_ = l_Lean_Expr_bindingDomain_x21(v_a_5234_);
lean_dec(v_a_5234_);
v___x_5239_ = l_Lean_Expr_isHEq(v___x_5238_);
lean_dec_ref(v___x_5238_);
if (v___x_5239_ == 0)
{
lean_object* v___x_5240_; lean_object* v___x_5242_; 
v___x_5240_ = l_Lean_Expr_app___override(v_a_5230_, v_h_5022_);
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 0, v___x_5240_);
v___x_5242_ = v___x_5236_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5240_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
else
{
lean_object* v___x_5244_; 
lean_del_object(v___x_5236_);
v___x_5244_ = l_Lean_Meta_mkHEqOfEq(v_h_5022_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
if (lean_obj_tag(v___x_5244_) == 0)
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5253_; 
v_a_5245_ = lean_ctor_get(v___x_5244_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5244_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5247_ = v___x_5244_;
v_isShared_5248_ = v_isSharedCheck_5253_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5244_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5253_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5249_; lean_object* v___x_5251_; 
v___x_5249_ = l_Lean_Expr_app___override(v_a_5230_, v_a_5245_);
if (v_isShared_5248_ == 0)
{
lean_ctor_set(v___x_5247_, 0, v___x_5249_);
v___x_5251_ = v___x_5247_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
else
{
lean_dec(v_a_5230_);
return v___x_5244_;
}
}
}
}
else
{
lean_dec(v_a_5230_);
lean_dec_ref(v_h_5022_);
return v___x_5233_;
}
}
else
{
lean_dec(v_a_5230_);
lean_dec_ref(v_h_5022_);
return v___x_5231_;
}
}
else
{
lean_dec_ref(v_h_5022_);
return v___x_5229_;
}
}
}
}
}
}
else
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
lean_dec(v___x_5179_);
lean_dec(v_numParams_5099_);
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_dec(v_snd_5085_);
lean_dec(v_a_5080_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v_a_5260_ = lean_ctor_get(v___x_5185_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5185_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5185_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
}
}
else
{
lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___f_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
lean_dec(v_numParams_5099_);
lean_dec_ref(v_toConstantVal_5097_);
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_del_object(v___x_5087_);
lean_dec(v_snd_5085_);
lean_dec(v_a_5080_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v_h_5022_);
v___x_5285_ = lean_box(v___x_5075_);
v___x_5286_ = lean_box(v___x_5176_);
v___f_5287_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5287_, 0, v___x_5285_);
lean_closure_set(v___f_5287_, 1, v___x_5286_);
v___x_5288_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__24));
v___x_5289_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5288_, v_target_5021_, v___f_5287_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
return v___x_5289_;
}
}
}
}
else
{
lean_dec(v_a_5090_);
lean_del_object(v___x_5087_);
lean_dec(v_snd_5085_);
lean_dec(v_fst_5084_);
lean_dec(v_a_5080_);
lean_dec_ref(v_val_5078_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v___y_5046_ = v_a_5023_;
v___y_5047_ = v_a_5024_;
v___y_5048_ = v_a_5025_;
v___y_5049_ = v_a_5026_;
goto v___jp_5045_;
}
}
else
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5298_; 
lean_del_object(v___x_5087_);
lean_dec(v_snd_5085_);
lean_dec(v_fst_5084_);
lean_dec(v_a_5080_);
lean_dec_ref(v_val_5078_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v_a_5291_ = lean_ctor_get(v___x_5089_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5293_ = v___x_5089_;
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5089_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5296_; 
if (v_isShared_5294_ == 0)
{
v___x_5296_ = v___x_5293_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
}
else
{
lean_dec(v_a_5082_);
lean_dec(v_a_5080_);
lean_dec_ref(v_val_5078_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v___y_5046_ = v_a_5023_;
v___y_5047_ = v_a_5024_;
v___y_5048_ = v_a_5025_;
v___y_5049_ = v_a_5026_;
goto v___jp_5045_;
}
}
else
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5307_; 
lean_dec(v_a_5080_);
lean_dec_ref(v_val_5078_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v_a_5300_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5302_ = v___x_5081_;
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5081_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5305_; 
if (v_isShared_5303_ == 0)
{
v___x_5305_ = v___x_5302_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
lean_dec_ref(v_val_5078_);
lean_dec(v_us_5072_);
lean_dec(v_a_5059_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v_a_5308_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5079_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5079_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
else
{
lean_dec(v_val_5077_);
lean_dec(v_us_5072_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v___y_5061_ = v_a_5023_;
v___y_5062_ = v_a_5024_;
v___y_5063_ = v_a_5025_;
v___y_5064_ = v_a_5026_;
goto v___jp_5060_;
}
}
}
else
{
lean_dec_ref(v___x_5070_);
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
v___y_5061_ = v_a_5023_;
v___y_5062_ = v_a_5024_;
v___y_5063_ = v_a_5025_;
v___y_5064_ = v_a_5026_;
goto v___jp_5060_;
}
v___jp_5060_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5065_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5066_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5067_ = l_Lean_indentExpr(v_a_5059_);
v___x_5068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5066_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
v___x_5069_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5065_, v___x_5068_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
return v___x_5069_;
}
}
else
{
lean_dec_ref(v___x_5044_);
lean_dec_ref(v___x_5043_);
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
return v___x_5058_;
}
v___jp_5045_:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5050_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__6, &l_Lean_Meta_mkNoConfusion___closed__6_once, _init_l_Lean_Meta_mkNoConfusion___closed__6);
v___x_5051_ = l_Lean_MessageData_ofExpr(v___x_5043_);
v___x_5052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5050_);
lean_ctor_set(v___x_5052_, 1, v___x_5051_);
v___x_5053_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__8, &l_Lean_Meta_mkNoConfusion___closed__8_once, _init_l_Lean_Meta_mkNoConfusion___closed__8);
v___x_5054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5052_);
lean_ctor_set(v___x_5054_, 1, v___x_5053_);
v___x_5055_ = l_Lean_MessageData_ofExpr(v___x_5044_);
v___x_5056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5054_);
lean_ctor_set(v___x_5056_, 1, v___x_5055_);
v___x_5057_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5056_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_);
return v___x_5057_;
}
}
}
else
{
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
return v___x_5030_;
}
}
else
{
lean_dec_ref(v_h_5022_);
lean_dec_ref(v_target_5021_);
return v___x_5028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5316_, lean_object* v_h_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_){
_start:
{
lean_object* v_res_5323_; 
v_res_5323_ = l_Lean_Meta_mkNoConfusion(v_target_5316_, v_h_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec_ref(v_a_5318_);
return v_res_5323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5324_, lean_object* v_b_5325_, lean_object* v_i_5326_, lean_object* v_hs_5327_, lean_object* v_hl_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5324_, v_b_5325_, v_i_5326_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5335_, lean_object* v_b_5336_, lean_object* v_i_5337_, lean_object* v_hs_5338_, lean_object* v_hl_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_){
_start:
{
lean_object* v_res_5345_; 
v_res_5345_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5335_, v_b_5336_, v_i_5337_, v_hs_5338_, v_hl_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
lean_dec_ref(v_range_5335_);
return v_res_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5346_, lean_object* v_name_5347_, uint8_t v_bi_5348_, lean_object* v_type_5349_, lean_object* v_k_5350_, uint8_t v_kind_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v___x_5357_; 
v___x_5357_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5347_, v_bi_5348_, v_type_5349_, v_k_5350_, v_kind_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5358_, lean_object* v_name_5359_, lean_object* v_bi_5360_, lean_object* v_type_5361_, lean_object* v_k_5362_, lean_object* v_kind_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_){
_start:
{
uint8_t v_bi_boxed_5369_; uint8_t v_kind_boxed_5370_; lean_object* v_res_5371_; 
v_bi_boxed_5369_ = lean_unbox(v_bi_5360_);
v_kind_boxed_5370_ = lean_unbox(v_kind_5363_);
v_res_5371_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5358_, v_name_5359_, v_bi_boxed_5369_, v_type_5361_, v_k_5362_, v_kind_boxed_5370_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_);
lean_dec(v___y_5367_);
lean_dec_ref(v___y_5366_);
lean_dec(v___y_5365_);
lean_dec_ref(v___y_5364_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5372_, lean_object* v_name_5373_, lean_object* v_type_5374_, lean_object* v_k_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
lean_object* v___x_5381_; 
v___x_5381_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5373_, v_type_5374_, v_k_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5382_, lean_object* v_name_5383_, lean_object* v_type_5384_, lean_object* v_k_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5382_, v_name_5383_, v_type_5384_, v_k_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5397_, lean_object* v_e_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5404_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5405_, 0, v_monad_5397_);
v___x_5406_ = lean_box(0);
v___x_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5407_, 0, v_e_5398_);
v___x_5408_ = lean_unsigned_to_nat(4u);
v___x_5409_ = lean_mk_empty_array_with_capacity(v___x_5408_);
v___x_5410_ = lean_array_push(v___x_5409_, v___x_5405_);
v___x_5411_ = lean_array_push(v___x_5410_, v___x_5406_);
v___x_5412_ = lean_array_push(v___x_5411_, v___x_5406_);
v___x_5413_ = lean_array_push(v___x_5412_, v___x_5407_);
v___x_5414_ = l_Lean_Meta_mkAppOptM(v___x_5404_, v___x_5413_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5415_, lean_object* v_e_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Lean_Meta_mkPure(v_monad_5415_, v_e_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_);
lean_dec(v_a_5420_);
lean_dec_ref(v_a_5419_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
return v_res_5422_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5432_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5433_ = l_Lean_MessageData_ofFormat(v___x_5432_);
return v___x_5433_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5437_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5438_ = l_Lean_MessageData_ofFormat(v___x_5437_);
return v___x_5438_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5443_ = l_Lean_MessageData_ofFormat(v___x_5442_);
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5444_, lean_object* v_fieldName_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_){
_start:
{
lean_object* v___x_5451_; 
lean_inc(v_a_5449_);
lean_inc_ref(v_a_5448_);
lean_inc(v_a_5447_);
lean_inc_ref(v_a_5446_);
lean_inc_ref(v_s_5444_);
v___x_5451_ = lean_infer_type(v_s_5444_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
if (lean_obj_tag(v___x_5451_) == 0)
{
lean_object* v_a_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5548_; 
v_a_5452_ = lean_ctor_get(v___x_5451_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5451_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5454_ = v___x_5451_;
v_isShared_5455_ = v_isSharedCheck_5548_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_a_5452_);
lean_dec(v___x_5451_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5548_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___x_5456_; 
lean_inc(v_a_5449_);
lean_inc_ref(v_a_5448_);
lean_inc(v_a_5447_);
lean_inc_ref(v_a_5446_);
v___x_5456_ = lean_whnf(v_a_5452_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5547_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5459_ = v___x_5456_;
v_isShared_5460_ = v_isSharedCheck_5547_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_a_5457_);
lean_dec(v___x_5456_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5547_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___y_5462_; lean_object* v___y_5463_; lean_object* v___y_5464_; lean_object* v___y_5465_; lean_object* v___x_5480_; 
v___x_5480_ = l_Lean_Expr_getAppFn(v_a_5457_);
if (lean_obj_tag(v___x_5480_) == 4)
{
lean_object* v_declName_5481_; lean_object* v_us_5482_; lean_object* v___x_5483_; lean_object* v_env_5484_; lean_object* v___y_5486_; lean_object* v___y_5487_; lean_object* v___y_5488_; lean_object* v___y_5489_; uint8_t v___x_5528_; 
v_declName_5481_ = lean_ctor_get(v___x_5480_, 0);
lean_inc_n(v_declName_5481_, 2);
v_us_5482_ = lean_ctor_get(v___x_5480_, 1);
lean_inc(v_us_5482_);
lean_dec_ref_known(v___x_5480_, 2);
v___x_5483_ = lean_st_ref_get(v_a_5449_);
v_env_5484_ = lean_ctor_get(v___x_5483_, 0);
lean_inc_ref_n(v_env_5484_, 2);
lean_dec(v___x_5483_);
v___x_5528_ = l_Lean_isStructure(v_env_5484_, v_declName_5481_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v___x_5529_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5530_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5457_);
lean_inc_ref(v_s_5444_);
v___x_5531_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5444_, v_a_5457_);
v___x_5532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5530_);
lean_ctor_set(v___x_5532_, 1, v___x_5531_);
v___x_5533_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5529_, v___x_5532_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_dec_ref_known(v___x_5533_, 1);
v___y_5486_ = v_a_5446_;
v___y_5487_ = v_a_5447_;
v___y_5488_ = v_a_5448_;
v___y_5489_ = v_a_5449_;
goto v___jp_5485_;
}
else
{
lean_object* v_a_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5541_; 
lean_dec_ref(v_env_5484_);
lean_dec(v_us_5482_);
lean_dec(v_declName_5481_);
lean_del_object(v___x_5459_);
lean_dec(v_a_5457_);
lean_del_object(v___x_5454_);
lean_dec(v_fieldName_5445_);
lean_dec_ref(v_s_5444_);
v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5536_ = v___x_5533_;
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_a_5534_);
lean_dec(v___x_5533_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5539_; 
if (v_isShared_5537_ == 0)
{
v___x_5539_ = v___x_5536_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_a_5534_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
else
{
v___y_5486_ = v_a_5446_;
v___y_5487_ = v_a_5447_;
v___y_5488_ = v_a_5448_;
v___y_5489_ = v_a_5449_;
goto v___jp_5485_;
}
v___jp_5485_:
{
lean_object* v___x_5490_; 
lean_inc(v_fieldName_5445_);
lean_inc(v_declName_5481_);
lean_inc_ref(v_env_5484_);
v___x_5490_ = l_Lean_getProjFnForField_x3f(v_env_5484_, v_declName_5481_, v_fieldName_5445_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v___x_5491_; lean_object* v___x_5492_; size_t v_sz_5493_; size_t v___x_5494_; lean_object* v___x_5495_; 
lean_dec(v_us_5482_);
lean_del_object(v___x_5459_);
lean_inc(v_declName_5481_);
lean_inc_ref(v_env_5484_);
v___x_5491_ = l_Lean_getStructureFields(v_env_5484_, v_declName_5481_);
v___x_5492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5493_ = lean_array_size(v___x_5491_);
v___x_5494_ = ((size_t)0ULL);
lean_inc(v_fieldName_5445_);
lean_inc_ref(v_s_5444_);
v___x_5495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5484_, v_declName_5481_, v_s_5444_, v_fieldName_5445_, v___x_5491_, v_sz_5493_, v___x_5494_, v___x_5492_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
lean_dec_ref(v___x_5491_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5506_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5498_ = v___x_5495_;
v_isShared_5499_ = v_isSharedCheck_5506_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_a_5496_);
lean_dec(v___x_5495_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5506_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v_fst_5500_; 
v_fst_5500_ = lean_ctor_get(v_a_5496_, 0);
lean_inc(v_fst_5500_);
lean_dec(v_a_5496_);
if (lean_obj_tag(v_fst_5500_) == 0)
{
lean_del_object(v___x_5498_);
v___y_5462_ = v___y_5489_;
v___y_5463_ = v___y_5488_;
v___y_5464_ = v___y_5487_;
v___y_5465_ = v___y_5486_;
goto v___jp_5461_;
}
else
{
lean_object* v_val_5501_; 
v_val_5501_ = lean_ctor_get(v_fst_5500_, 0);
lean_inc(v_val_5501_);
lean_dec_ref_known(v_fst_5500_, 1);
if (lean_obj_tag(v_val_5501_) == 0)
{
lean_del_object(v___x_5498_);
v___y_5462_ = v___y_5489_;
v___y_5463_ = v___y_5488_;
v___y_5464_ = v___y_5487_;
v___y_5465_ = v___y_5486_;
goto v___jp_5461_;
}
else
{
lean_object* v_val_5502_; lean_object* v___x_5504_; 
lean_dec(v_a_5457_);
lean_del_object(v___x_5454_);
lean_dec(v_fieldName_5445_);
lean_dec_ref(v_s_5444_);
v_val_5502_ = lean_ctor_get(v_val_5501_, 0);
lean_inc(v_val_5502_);
lean_dec_ref_known(v_val_5501_, 1);
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 0, v_val_5502_);
v___x_5504_ = v___x_5498_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_val_5502_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
}
else
{
lean_object* v_a_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5514_; 
lean_dec(v_a_5457_);
lean_del_object(v___x_5454_);
lean_dec(v_fieldName_5445_);
lean_dec_ref(v_s_5444_);
v_a_5507_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5514_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5514_ == 0)
{
v___x_5509_ = v___x_5495_;
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_a_5507_);
lean_dec(v___x_5495_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5512_; 
if (v_isShared_5510_ == 0)
{
v___x_5512_ = v___x_5509_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_a_5507_);
v___x_5512_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
return v___x_5512_;
}
}
}
}
else
{
lean_object* v_val_5515_; lean_object* v_dummy_5516_; lean_object* v_nargs_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5526_; 
lean_dec_ref(v_env_5484_);
lean_dec(v_declName_5481_);
lean_del_object(v___x_5454_);
lean_dec(v_fieldName_5445_);
v_val_5515_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_val_5515_);
lean_dec_ref_known(v___x_5490_, 1);
v_dummy_5516_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5517_ = l_Lean_Expr_getAppNumArgs(v_a_5457_);
lean_inc(v_nargs_5517_);
v___x_5518_ = lean_mk_array(v_nargs_5517_, v_dummy_5516_);
v___x_5519_ = lean_unsigned_to_nat(1u);
v___x_5520_ = lean_nat_sub(v_nargs_5517_, v___x_5519_);
lean_dec(v_nargs_5517_);
v___x_5521_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5457_, v___x_5518_, v___x_5520_);
v___x_5522_ = l_Lean_mkConst(v_val_5515_, v_us_5482_);
v___x_5523_ = l_Lean_mkAppN(v___x_5522_, v___x_5521_);
lean_dec_ref(v___x_5521_);
v___x_5524_ = l_Lean_Expr_app___override(v___x_5523_, v_s_5444_);
if (v_isShared_5460_ == 0)
{
lean_ctor_set(v___x_5459_, 0, v___x_5524_);
v___x_5526_ = v___x_5459_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v___x_5524_);
v___x_5526_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
return v___x_5526_;
}
}
}
}
else
{
lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; 
lean_dec_ref(v___x_5480_);
lean_del_object(v___x_5459_);
lean_del_object(v___x_5454_);
lean_dec(v_fieldName_5445_);
v___x_5542_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5543_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5544_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5444_, v_a_5457_);
v___x_5545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5543_);
lean_ctor_set(v___x_5545_, 1, v___x_5544_);
v___x_5546_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5542_, v___x_5545_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
return v___x_5546_;
}
v___jp_5461_:
{
lean_object* v___x_5466_; lean_object* v___x_5467_; uint8_t v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5471_; 
v___x_5466_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5467_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5468_ = 1;
v___x_5469_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5445_, v___x_5468_);
if (v_isShared_5455_ == 0)
{
lean_ctor_set_tag(v___x_5454_, 3);
lean_ctor_set(v___x_5454_, 0, v___x_5469_);
v___x_5471_ = v___x_5454_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v___x_5469_);
v___x_5471_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; 
v___x_5472_ = l_Lean_MessageData_ofFormat(v___x_5471_);
v___x_5473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5473_, 0, v___x_5467_);
lean_ctor_set(v___x_5473_, 1, v___x_5472_);
v___x_5474_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5475_, 0, v___x_5473_);
lean_ctor_set(v___x_5475_, 1, v___x_5474_);
v___x_5476_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5444_, v_a_5457_);
v___x_5477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5477_, 0, v___x_5475_);
lean_ctor_set(v___x_5477_, 1, v___x_5476_);
v___x_5478_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5466_, v___x_5477_, v___y_5465_, v___y_5464_, v___y_5463_, v___y_5462_);
return v___x_5478_;
}
}
}
}
else
{
lean_del_object(v___x_5454_);
lean_dec(v_fieldName_5445_);
lean_dec_ref(v_s_5444_);
return v___x_5456_;
}
}
}
else
{
lean_dec(v_fieldName_5445_);
lean_dec_ref(v_s_5444_);
return v___x_5451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5549_, lean_object* v_declName_5550_, lean_object* v_s_5551_, lean_object* v_fieldName_5552_, lean_object* v_as_5553_, size_t v_sz_5554_, size_t v_i_5555_, lean_object* v_b_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_){
_start:
{
lean_object* v_a_5563_; uint8_t v___x_5567_; 
v___x_5567_ = lean_usize_dec_lt(v_i_5555_, v_sz_5554_);
if (v___x_5567_ == 0)
{
lean_object* v___x_5568_; 
lean_dec(v_fieldName_5552_);
lean_dec_ref(v_s_5551_);
lean_dec(v_declName_5550_);
lean_dec_ref(v___x_5549_);
v___x_5568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5568_, 0, v_b_5556_);
return v___x_5568_;
}
else
{
lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v_a_5571_; lean_object* v___x_5572_; 
lean_dec_ref(v_b_5556_);
v___x_5569_ = lean_box(0);
v___x_5570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5571_ = lean_array_uget_borrowed(v_as_5553_, v_i_5555_);
lean_inc(v_a_5571_);
lean_inc(v_declName_5550_);
lean_inc_ref(v___x_5549_);
v___x_5572_ = l_Lean_isSubobjectField_x3f(v___x_5549_, v_declName_5550_, v_a_5571_);
if (lean_obj_tag(v___x_5572_) == 0)
{
v_a_5563_ = v___x_5570_;
goto v___jp_5562_;
}
else
{
lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5632_; 
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5632_ == 0)
{
lean_object* v_unused_5633_; 
v_unused_5633_ = lean_ctor_get(v___x_5572_, 0);
lean_dec(v_unused_5633_);
v___x_5574_ = v___x_5572_;
v_isShared_5575_ = v_isSharedCheck_5632_;
goto v_resetjp_5573_;
}
else
{
lean_dec(v___x_5572_);
v___x_5574_ = lean_box(0);
v_isShared_5575_ = v_isSharedCheck_5632_;
goto v_resetjp_5573_;
}
v_resetjp_5573_:
{
lean_object* v___x_5576_; 
lean_inc(v_a_5571_);
lean_inc_ref(v_s_5551_);
v___x_5576_ = l_Lean_Meta_mkProjection(v_s_5551_, v_a_5571_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_);
if (lean_obj_tag(v___x_5576_) == 0)
{
lean_object* v_a_5577_; lean_object* v___x_5578_; 
v_a_5577_ = lean_ctor_get(v___x_5576_, 0);
lean_inc(v_a_5577_);
lean_dec_ref_known(v___x_5576_, 1);
v___x_5578_ = l_Lean_Meta_saveState___redArg(v___y_5558_, v___y_5560_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v_a_5579_; lean_object* v___x_5580_; 
v_a_5579_ = lean_ctor_get(v___x_5578_, 0);
lean_inc(v_a_5579_);
lean_dec_ref_known(v___x_5578_, 1);
lean_inc(v_fieldName_5552_);
v___x_5580_ = l_Lean_Meta_mkProjection(v_a_5577_, v_fieldName_5552_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_);
if (lean_obj_tag(v___x_5580_) == 0)
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5593_; 
lean_dec(v_a_5579_);
lean_dec(v_fieldName_5552_);
lean_dec_ref(v_s_5551_);
lean_dec(v_declName_5550_);
lean_dec_ref(v___x_5549_);
v_a_5581_ = lean_ctor_get(v___x_5580_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5583_ = v___x_5580_;
v_isShared_5584_ = v_isSharedCheck_5593_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5580_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5593_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5586_; 
if (v_isShared_5575_ == 0)
{
lean_ctor_set(v___x_5574_, 0, v_a_5581_);
v___x_5586_ = v___x_5574_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_a_5581_);
v___x_5586_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5590_; 
v___x_5587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
v___x_5588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5587_);
lean_ctor_set(v___x_5588_, 1, v___x_5569_);
if (v_isShared_5584_ == 0)
{
lean_ctor_set(v___x_5583_, 0, v___x_5588_);
v___x_5590_ = v___x_5583_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5588_);
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
lean_object* v_a_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5615_; 
lean_del_object(v___x_5574_);
v_a_5594_ = lean_ctor_get(v___x_5580_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5596_ = v___x_5580_;
v_isShared_5597_ = v_isSharedCheck_5615_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_a_5594_);
lean_dec(v___x_5580_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5615_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
uint8_t v___x_5598_; 
v___x_5598_ = l_Lean_Exception_isInterrupt(v_a_5594_);
if (v___x_5598_ == 0)
{
uint8_t v___x_5599_; 
lean_inc(v_a_5594_);
v___x_5599_ = l_Lean_Exception_isRuntime(v_a_5594_);
if (v___x_5599_ == 0)
{
lean_object* v___x_5600_; 
lean_del_object(v___x_5596_);
lean_dec(v_a_5594_);
v___x_5600_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5579_, v___y_5558_, v___y_5560_);
if (lean_obj_tag(v___x_5600_) == 0)
{
lean_dec_ref_known(v___x_5600_, 1);
v_a_5563_ = v___x_5570_;
goto v___jp_5562_;
}
else
{
lean_object* v_a_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5608_; 
lean_dec(v_fieldName_5552_);
lean_dec_ref(v_s_5551_);
lean_dec(v_declName_5550_);
lean_dec_ref(v___x_5549_);
v_a_5601_ = lean_ctor_get(v___x_5600_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v___x_5600_);
if (v_isSharedCheck_5608_ == 0)
{
v___x_5603_ = v___x_5600_;
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_a_5601_);
lean_dec(v___x_5600_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5601_);
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
lean_object* v___x_5610_; 
lean_dec(v_a_5579_);
lean_dec(v_fieldName_5552_);
lean_dec_ref(v_s_5551_);
lean_dec(v_declName_5550_);
lean_dec_ref(v___x_5549_);
if (v_isShared_5597_ == 0)
{
v___x_5610_ = v___x_5596_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v_a_5594_);
v___x_5610_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
return v___x_5610_;
}
}
}
else
{
lean_object* v___x_5613_; 
lean_dec(v_a_5579_);
lean_dec(v_fieldName_5552_);
lean_dec_ref(v_s_5551_);
lean_dec(v_declName_5550_);
lean_dec_ref(v___x_5549_);
if (v_isShared_5597_ == 0)
{
v___x_5613_ = v___x_5596_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_a_5594_);
v___x_5613_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
return v___x_5613_;
}
}
}
}
}
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec(v_a_5577_);
lean_del_object(v___x_5574_);
lean_dec(v_fieldName_5552_);
lean_dec_ref(v_s_5551_);
lean_dec(v_declName_5550_);
lean_dec_ref(v___x_5549_);
v_a_5616_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5578_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5578_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_del_object(v___x_5574_);
lean_dec(v_fieldName_5552_);
lean_dec_ref(v_s_5551_);
lean_dec(v_declName_5550_);
lean_dec_ref(v___x_5549_);
v_a_5624_ = lean_ctor_get(v___x_5576_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5576_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5576_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5576_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
}
}
v___jp_5562_:
{
size_t v___x_5564_; size_t v___x_5565_; 
v___x_5564_ = ((size_t)1ULL);
v___x_5565_ = lean_usize_add(v_i_5555_, v___x_5564_);
lean_inc_ref(v_a_5563_);
v_i_5555_ = v___x_5565_;
v_b_5556_ = v_a_5563_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5634_, lean_object* v_declName_5635_, lean_object* v_s_5636_, lean_object* v_fieldName_5637_, lean_object* v_as_5638_, lean_object* v_sz_5639_, lean_object* v_i_5640_, lean_object* v_b_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_){
_start:
{
size_t v_sz_boxed_5647_; size_t v_i_boxed_5648_; lean_object* v_res_5649_; 
v_sz_boxed_5647_ = lean_unbox_usize(v_sz_5639_);
lean_dec(v_sz_5639_);
v_i_boxed_5648_ = lean_unbox_usize(v_i_5640_);
lean_dec(v_i_5640_);
v_res_5649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5634_, v_declName_5635_, v_s_5636_, v_fieldName_5637_, v_as_5638_, v_sz_boxed_5647_, v_i_boxed_5648_, v_b_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
lean_dec_ref(v_as_5638_);
return v_res_5649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5650_, lean_object* v_fieldName_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_){
_start:
{
lean_object* v_res_5657_; 
v_res_5657_ = l_Lean_Meta_mkProjection(v_s_5650_, v_fieldName_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_);
lean_dec(v_a_5655_);
lean_dec_ref(v_a_5654_);
lean_dec(v_a_5653_);
lean_dec_ref(v_a_5652_);
return v_res_5657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5658_, lean_object* v_cons_5659_, lean_object* v_x_5660_){
_start:
{
if (lean_obj_tag(v_x_5660_) == 0)
{
lean_dec_ref(v_cons_5659_);
lean_inc_ref(v_nil_5658_);
return v_nil_5658_;
}
else
{
lean_object* v_head_5661_; lean_object* v_tail_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; 
v_head_5661_ = lean_ctor_get(v_x_5660_, 0);
lean_inc(v_head_5661_);
v_tail_5662_ = lean_ctor_get(v_x_5660_, 1);
lean_inc(v_tail_5662_);
lean_dec_ref_known(v_x_5660_, 2);
lean_inc_ref(v_cons_5659_);
v___x_5663_ = l_Lean_Expr_app___override(v_cons_5659_, v_head_5661_);
v___x_5664_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5658_, v_cons_5659_, v_tail_5662_);
v___x_5665_ = l_Lean_Expr_app___override(v___x_5663_, v___x_5664_);
return v___x_5665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5666_, lean_object* v_cons_5667_, lean_object* v_x_5668_){
_start:
{
lean_object* v_res_5669_; 
v_res_5669_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5666_, v_cons_5667_, v_x_5668_);
lean_dec_ref(v_nil_5666_);
return v_res_5669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5679_, lean_object* v_xs_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_){
_start:
{
lean_object* v___x_5686_; 
lean_inc_ref(v_type_5679_);
v___x_5686_ = l_Lean_Meta_getDecLevel(v_type_5679_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_);
if (lean_obj_tag(v___x_5686_) == 0)
{
lean_object* v_a_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5706_; 
v_a_5687_ = lean_ctor_get(v___x_5686_, 0);
v_isSharedCheck_5706_ = !lean_is_exclusive(v___x_5686_);
if (v_isSharedCheck_5706_ == 0)
{
v___x_5689_ = v___x_5686_;
v_isShared_5690_ = v_isSharedCheck_5706_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_a_5687_);
lean_dec(v___x_5686_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5706_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; 
v___x_5691_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5692_ = lean_box(0);
v___x_5693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5693_, 0, v_a_5687_);
lean_ctor_set(v___x_5693_, 1, v___x_5692_);
lean_inc_ref(v___x_5693_);
v___x_5694_ = l_Lean_mkConst(v___x_5691_, v___x_5693_);
lean_inc_ref(v_type_5679_);
v___x_5695_ = l_Lean_Expr_app___override(v___x_5694_, v_type_5679_);
if (lean_obj_tag(v_xs_5680_) == 0)
{
lean_object* v___x_5697_; 
lean_dec_ref_known(v___x_5693_, 2);
lean_dec_ref(v_type_5679_);
if (v_isShared_5690_ == 0)
{
lean_ctor_set(v___x_5689_, 0, v___x_5695_);
v___x_5697_ = v___x_5689_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
else
{
lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5704_; 
v___x_5699_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5700_ = l_Lean_mkConst(v___x_5699_, v___x_5693_);
v___x_5701_ = l_Lean_Expr_app___override(v___x_5700_, v_type_5679_);
v___x_5702_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5695_, v___x_5701_, v_xs_5680_);
lean_dec_ref(v___x_5695_);
if (v_isShared_5690_ == 0)
{
lean_ctor_set(v___x_5689_, 0, v___x_5702_);
v___x_5704_ = v___x_5689_;
goto v_reusejp_5703_;
}
else
{
lean_object* v_reuseFailAlloc_5705_; 
v_reuseFailAlloc_5705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5705_, 0, v___x_5702_);
v___x_5704_ = v_reuseFailAlloc_5705_;
goto v_reusejp_5703_;
}
v_reusejp_5703_:
{
return v___x_5704_;
}
}
}
}
else
{
lean_object* v_a_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5714_; 
lean_dec(v_xs_5680_);
lean_dec_ref(v_type_5679_);
v_a_5707_ = lean_ctor_get(v___x_5686_, 0);
v_isSharedCheck_5714_ = !lean_is_exclusive(v___x_5686_);
if (v_isSharedCheck_5714_ == 0)
{
v___x_5709_ = v___x_5686_;
v_isShared_5710_ = v_isSharedCheck_5714_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_a_5707_);
lean_dec(v___x_5686_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5714_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v___x_5712_; 
if (v_isShared_5710_ == 0)
{
v___x_5712_ = v___x_5709_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_a_5707_);
v___x_5712_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
return v___x_5712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5715_, lean_object* v_xs_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_){
_start:
{
lean_object* v_res_5722_; 
v_res_5722_ = l_Lean_Meta_mkListLit(v_type_5715_, v_xs_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_);
lean_dec(v_a_5720_);
lean_dec_ref(v_a_5719_);
lean_dec(v_a_5718_);
lean_dec_ref(v_a_5717_);
return v_res_5722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5727_, lean_object* v_xs_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_){
_start:
{
lean_object* v___x_5734_; 
lean_inc_ref(v_type_5727_);
v___x_5734_ = l_Lean_Meta_getDecLevel(v_type_5727_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v_a_5735_; lean_object* v___x_5736_; 
v_a_5735_ = lean_ctor_get(v___x_5734_, 0);
lean_inc(v_a_5735_);
lean_dec_ref_known(v___x_5734_, 1);
lean_inc_ref(v_type_5727_);
v___x_5736_ = l_Lean_Meta_mkListLit(v_type_5727_, v_xs_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_);
if (lean_obj_tag(v___x_5736_) == 0)
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5750_; 
v_a_5737_ = lean_ctor_get(v___x_5736_, 0);
v_isSharedCheck_5750_ = !lean_is_exclusive(v___x_5736_);
if (v_isSharedCheck_5750_ == 0)
{
v___x_5739_ = v___x_5736_;
v_isShared_5740_ = v_isSharedCheck_5750_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5736_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5750_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5748_; 
v___x_5741_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5742_ = lean_box(0);
v___x_5743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5743_, 0, v_a_5735_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = l_Lean_mkConst(v___x_5741_, v___x_5743_);
v___x_5745_ = l_Lean_Expr_app___override(v___x_5744_, v_type_5727_);
v___x_5746_ = l_Lean_Expr_app___override(v___x_5745_, v_a_5737_);
if (v_isShared_5740_ == 0)
{
lean_ctor_set(v___x_5739_, 0, v___x_5746_);
v___x_5748_ = v___x_5739_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v___x_5746_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
}
else
{
lean_dec(v_a_5735_);
lean_dec_ref(v_type_5727_);
return v___x_5736_;
}
}
else
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5758_; 
lean_dec(v_xs_5728_);
lean_dec_ref(v_type_5727_);
v_a_5751_ = lean_ctor_get(v___x_5734_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5758_ == 0)
{
v___x_5753_ = v___x_5734_;
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5734_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5756_; 
if (v_isShared_5754_ == 0)
{
v___x_5756_ = v___x_5753_;
goto v_reusejp_5755_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_a_5751_);
v___x_5756_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5755_;
}
v_reusejp_5755_:
{
return v___x_5756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5759_, lean_object* v_xs_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_){
_start:
{
lean_object* v_res_5766_; 
v_res_5766_ = l_Lean_Meta_mkArrayLit(v_type_5759_, v_xs_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_);
lean_dec(v_a_5764_);
lean_dec_ref(v_a_5763_);
lean_dec(v_a_5762_);
lean_dec_ref(v_a_5761_);
return v_res_5766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_){
_start:
{
lean_object* v___x_5778_; 
lean_inc_ref(v_type_5772_);
v___x_5778_ = l_Lean_Meta_getDecLevel(v_type_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_);
if (lean_obj_tag(v___x_5778_) == 0)
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5791_; 
v_a_5779_ = lean_ctor_get(v___x_5778_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v___x_5778_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5781_ = v___x_5778_;
v_isShared_5782_ = v_isSharedCheck_5791_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5778_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5791_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5789_; 
v___x_5783_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5784_ = lean_box(0);
v___x_5785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5785_, 0, v_a_5779_);
lean_ctor_set(v___x_5785_, 1, v___x_5784_);
v___x_5786_ = l_Lean_mkConst(v___x_5783_, v___x_5785_);
v___x_5787_ = l_Lean_Expr_app___override(v___x_5786_, v_type_5772_);
if (v_isShared_5782_ == 0)
{
lean_ctor_set(v___x_5781_, 0, v___x_5787_);
v___x_5789_ = v___x_5781_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v___x_5787_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
}
else
{
lean_object* v_a_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5799_; 
lean_dec_ref(v_type_5772_);
v_a_5792_ = lean_ctor_get(v___x_5778_, 0);
v_isSharedCheck_5799_ = !lean_is_exclusive(v___x_5778_);
if (v_isSharedCheck_5799_ == 0)
{
v___x_5794_ = v___x_5778_;
v_isShared_5795_ = v_isSharedCheck_5799_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_a_5792_);
lean_dec(v___x_5778_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5799_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v___x_5797_; 
if (v_isShared_5795_ == 0)
{
v___x_5797_ = v___x_5794_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_a_5792_);
v___x_5797_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
return v___x_5797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_){
_start:
{
lean_object* v_res_5806_; 
v_res_5806_ = l_Lean_Meta_mkNone(v_type_5800_, v_a_5801_, v_a_5802_, v_a_5803_, v_a_5804_);
lean_dec(v_a_5804_);
lean_dec_ref(v_a_5803_);
lean_dec(v_a_5802_);
lean_dec_ref(v_a_5801_);
return v_res_5806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5811_, lean_object* v_value_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_){
_start:
{
lean_object* v___x_5818_; 
lean_inc_ref(v_type_5811_);
v___x_5818_ = l_Lean_Meta_getDecLevel(v_type_5811_, v_a_5813_, v_a_5814_, v_a_5815_, v_a_5816_);
if (lean_obj_tag(v___x_5818_) == 0)
{
lean_object* v_a_5819_; lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5831_; 
v_a_5819_ = lean_ctor_get(v___x_5818_, 0);
v_isSharedCheck_5831_ = !lean_is_exclusive(v___x_5818_);
if (v_isSharedCheck_5831_ == 0)
{
v___x_5821_ = v___x_5818_;
v_isShared_5822_ = v_isSharedCheck_5831_;
goto v_resetjp_5820_;
}
else
{
lean_inc(v_a_5819_);
lean_dec(v___x_5818_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5831_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5829_; 
v___x_5823_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5824_ = lean_box(0);
v___x_5825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5825_, 0, v_a_5819_);
lean_ctor_set(v___x_5825_, 1, v___x_5824_);
v___x_5826_ = l_Lean_mkConst(v___x_5823_, v___x_5825_);
v___x_5827_ = l_Lean_mkAppB(v___x_5826_, v_type_5811_, v_value_5812_);
if (v_isShared_5822_ == 0)
{
lean_ctor_set(v___x_5821_, 0, v___x_5827_);
v___x_5829_ = v___x_5821_;
goto v_reusejp_5828_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v___x_5827_);
v___x_5829_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5828_;
}
v_reusejp_5828_:
{
return v___x_5829_;
}
}
}
else
{
lean_object* v_a_5832_; lean_object* v___x_5834_; uint8_t v_isShared_5835_; uint8_t v_isSharedCheck_5839_; 
lean_dec_ref(v_value_5812_);
lean_dec_ref(v_type_5811_);
v_a_5832_ = lean_ctor_get(v___x_5818_, 0);
v_isSharedCheck_5839_ = !lean_is_exclusive(v___x_5818_);
if (v_isSharedCheck_5839_ == 0)
{
v___x_5834_ = v___x_5818_;
v_isShared_5835_ = v_isSharedCheck_5839_;
goto v_resetjp_5833_;
}
else
{
lean_inc(v_a_5832_);
lean_dec(v___x_5818_);
v___x_5834_ = lean_box(0);
v_isShared_5835_ = v_isSharedCheck_5839_;
goto v_resetjp_5833_;
}
v_resetjp_5833_:
{
lean_object* v___x_5837_; 
if (v_isShared_5835_ == 0)
{
v___x_5837_ = v___x_5834_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v_a_5832_);
v___x_5837_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
return v___x_5837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5840_, lean_object* v_value_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_){
_start:
{
lean_object* v_res_5847_; 
v_res_5847_ = l_Lean_Meta_mkSome(v_type_5840_, v_value_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_);
lean_dec(v_a_5845_);
lean_dec_ref(v_a_5844_);
lean_dec(v_a_5843_);
lean_dec_ref(v_a_5842_);
return v_res_5847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5859_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5860_, 0, v_p_5853_);
v___x_5861_ = lean_box(0);
v___x_5862_ = lean_unsigned_to_nat(2u);
v___x_5863_ = lean_mk_empty_array_with_capacity(v___x_5862_);
v___x_5864_ = lean_array_push(v___x_5863_, v___x_5860_);
v___x_5865_ = lean_array_push(v___x_5864_, v___x_5861_);
v___x_5866_ = l_Lean_Meta_mkAppOptM(v___x_5859_, v___x_5865_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_);
return v___x_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5867_, lean_object* v_a_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_){
_start:
{
lean_object* v_res_5873_; 
v_res_5873_ = l_Lean_Meta_mkDecide(v_p_5867_, v_a_5868_, v_a_5869_, v_a_5870_, v_a_5871_);
lean_dec(v_a_5871_);
lean_dec_ref(v_a_5870_);
lean_dec(v_a_5869_);
lean_dec_ref(v_a_5868_);
return v_res_5873_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
v___x_5879_ = lean_box(0);
v___x_5880_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5881_ = l_Lean_mkConst(v___x_5880_, v___x_5879_);
return v___x_5881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_){
_start:
{
lean_object* v___x_5891_; 
v___x_5891_ = l_Lean_Meta_mkDecide(v_p_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_);
if (lean_obj_tag(v___x_5891_) == 0)
{
lean_object* v_a_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; 
v_a_5892_ = lean_ctor_get(v___x_5891_, 0);
lean_inc(v_a_5892_);
lean_dec_ref_known(v___x_5891_, 1);
v___x_5893_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5894_ = l_Lean_Meta_mkEq(v_a_5892_, v___x_5893_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_);
if (lean_obj_tag(v___x_5894_) == 0)
{
lean_object* v_a_5895_; lean_object* v___x_5896_; 
v_a_5895_ = lean_ctor_get(v___x_5894_, 0);
lean_inc(v_a_5895_);
lean_dec_ref_known(v___x_5894_, 1);
v___x_5896_ = l_Lean_Meta_mkEqRefl(v___x_5893_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_);
if (lean_obj_tag(v___x_5896_) == 0)
{
lean_object* v_a_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; 
v_a_5897_ = lean_ctor_get(v___x_5896_, 0);
lean_inc(v_a_5897_);
lean_dec_ref_known(v___x_5896_, 1);
v___x_5898_ = l_Lean_Meta_mkExpectedPropHint(v_a_5897_, v_a_5895_);
v___x_5899_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5900_ = lean_unsigned_to_nat(1u);
v___x_5901_ = lean_mk_empty_array_with_capacity(v___x_5900_);
v___x_5902_ = lean_array_push(v___x_5901_, v___x_5898_);
v___x_5903_ = l_Lean_Meta_mkAppM(v___x_5899_, v___x_5902_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_);
return v___x_5903_;
}
else
{
lean_dec(v_a_5895_);
return v___x_5896_;
}
}
else
{
return v___x_5894_;
}
}
else
{
return v___x_5891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5904_, lean_object* v_a_5905_, lean_object* v_a_5906_, lean_object* v_a_5907_, lean_object* v_a_5908_, lean_object* v_a_5909_){
_start:
{
lean_object* v_res_5910_; 
v_res_5910_ = l_Lean_Meta_mkDecideProof(v_p_5904_, v_a_5905_, v_a_5906_, v_a_5907_, v_a_5908_);
lean_dec(v_a_5908_);
lean_dec_ref(v_a_5907_);
lean_dec(v_a_5906_);
lean_dec_ref(v_a_5905_);
return v_res_5910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5916_, lean_object* v_b_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_){
_start:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; 
v___x_5923_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_5924_ = lean_unsigned_to_nat(2u);
v___x_5925_ = lean_mk_empty_array_with_capacity(v___x_5924_);
v___x_5926_ = lean_array_push(v___x_5925_, v_a_5916_);
v___x_5927_ = lean_array_push(v___x_5926_, v_b_5917_);
v___x_5928_ = l_Lean_Meta_mkAppM(v___x_5923_, v___x_5927_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_);
return v___x_5928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_5929_, lean_object* v_b_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_){
_start:
{
lean_object* v_res_5936_; 
v_res_5936_ = l_Lean_Meta_mkLt(v_a_5929_, v_b_5930_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_);
lean_dec(v_a_5934_);
lean_dec_ref(v_a_5933_);
lean_dec(v_a_5932_);
lean_dec_ref(v_a_5931_);
return v_res_5936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_5942_, lean_object* v_b_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_){
_start:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; 
v___x_5949_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_5950_ = lean_unsigned_to_nat(2u);
v___x_5951_ = lean_mk_empty_array_with_capacity(v___x_5950_);
v___x_5952_ = lean_array_push(v___x_5951_, v_a_5942_);
v___x_5953_ = lean_array_push(v___x_5952_, v_b_5943_);
v___x_5954_ = l_Lean_Meta_mkAppM(v___x_5949_, v___x_5953_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_);
return v___x_5954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_5955_, lean_object* v_b_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_, lean_object* v_a_5961_){
_start:
{
lean_object* v_res_5962_; 
v_res_5962_ = l_Lean_Meta_mkLe(v_a_5955_, v_b_5956_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_);
lean_dec(v_a_5960_);
lean_dec_ref(v_a_5959_);
lean_dec(v_a_5958_);
lean_dec_ref(v_a_5957_);
return v_res_5962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_){
_start:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5974_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_5975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5975_, 0, v_00_u03b1_5968_);
v___x_5976_ = lean_box(0);
v___x_5977_ = lean_unsigned_to_nat(2u);
v___x_5978_ = lean_mk_empty_array_with_capacity(v___x_5977_);
v___x_5979_ = lean_array_push(v___x_5978_, v___x_5975_);
v___x_5980_ = lean_array_push(v___x_5979_, v___x_5976_);
v___x_5981_ = l_Lean_Meta_mkAppOptM(v___x_5974_, v___x_5980_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_);
return v___x_5981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_){
_start:
{
lean_object* v_res_5988_; 
v_res_5988_ = l_Lean_Meta_mkDefault(v_00_u03b1_5982_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_);
lean_dec(v_a_5986_);
lean_dec_ref(v_a_5985_);
lean_dec(v_a_5984_);
lean_dec_ref(v_a_5983_);
return v_res_5988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_){
_start:
{
lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6000_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_6001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6001_, 0, v_00_u03b1_5994_);
v___x_6002_ = lean_box(0);
v___x_6003_ = lean_unsigned_to_nat(2u);
v___x_6004_ = lean_mk_empty_array_with_capacity(v___x_6003_);
v___x_6005_ = lean_array_push(v___x_6004_, v___x_6001_);
v___x_6006_ = lean_array_push(v___x_6005_, v___x_6002_);
v___x_6007_ = l_Lean_Meta_mkAppOptM(v___x_6000_, v___x_6006_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_);
return v___x_6007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_){
_start:
{
lean_object* v_res_6014_; 
v_res_6014_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6008_, v_a_6009_, v_a_6010_, v_a_6011_, v_a_6012_);
lean_dec(v_a_6012_);
lean_dec_ref(v_a_6011_);
lean_dec(v_a_6010_);
lean_dec_ref(v_a_6009_);
return v_res_6014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
v___x_6024_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6025_ = lean_unsigned_to_nat(1u);
v___x_6026_ = lean_mk_empty_array_with_capacity(v___x_6025_);
v___x_6027_ = lean_array_push(v___x_6026_, v_h_6018_);
v___x_6028_ = l_Lean_Meta_mkAppM(v___x_6024_, v___x_6027_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_);
return v___x_6028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_, lean_object* v_a_6034_){
_start:
{
lean_object* v_res_6035_; 
v_res_6035_ = l_Lean_Meta_mkFunExt(v_h_6029_, v_a_6030_, v_a_6031_, v_a_6032_, v_a_6033_);
lean_dec(v_a_6033_);
lean_dec_ref(v_a_6032_);
lean_dec(v_a_6031_);
lean_dec_ref(v_a_6030_);
return v_res_6035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6039_, lean_object* v_a_6040_, lean_object* v_a_6041_, lean_object* v_a_6042_, lean_object* v_a_6043_){
_start:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___x_6045_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6046_ = lean_unsigned_to_nat(1u);
v___x_6047_ = lean_mk_empty_array_with_capacity(v___x_6046_);
v___x_6048_ = lean_array_push(v___x_6047_, v_h_6039_);
v___x_6049_ = l_Lean_Meta_mkAppM(v___x_6045_, v___x_6048_, v_a_6040_, v_a_6041_, v_a_6042_, v_a_6043_);
return v___x_6049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_){
_start:
{
lean_object* v_res_6056_; 
v_res_6056_ = l_Lean_Meta_mkPropExt(v_h_6050_, v_a_6051_, v_a_6052_, v_a_6053_, v_a_6054_);
lean_dec(v_a_6054_);
lean_dec_ref(v_a_6053_);
lean_dec(v_a_6052_);
lean_dec_ref(v_a_6051_);
return v_res_6056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6060_, lean_object* v_h_u2082_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_){
_start:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6067_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6068_ = lean_unsigned_to_nat(2u);
v___x_6069_ = lean_mk_empty_array_with_capacity(v___x_6068_);
v___x_6070_ = lean_array_push(v___x_6069_, v_h_u2081_6060_);
v___x_6071_ = lean_array_push(v___x_6070_, v_h_u2082_6061_);
v___x_6072_ = l_Lean_Meta_mkAppM(v___x_6067_, v___x_6071_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6073_, lean_object* v_h_u2082_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_, lean_object* v_a_6077_, lean_object* v_a_6078_, lean_object* v_a_6079_){
_start:
{
lean_object* v_res_6080_; 
v_res_6080_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6073_, v_h_u2082_6074_, v_a_6075_, v_a_6076_, v_a_6077_, v_a_6078_);
lean_dec(v_a_6078_);
lean_dec_ref(v_a_6077_);
lean_dec(v_a_6076_);
lean_dec_ref(v_a_6075_);
return v_res_6080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6084_, lean_object* v_h_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_){
_start:
{
lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6091_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6092_ = lean_unsigned_to_nat(2u);
v___x_6093_ = lean_mk_empty_array_with_capacity(v___x_6092_);
v___x_6094_ = lean_array_push(v___x_6093_, v_b_6084_);
v___x_6095_ = lean_array_push(v___x_6094_, v_h_6085_);
v___x_6096_ = l_Lean_Meta_mkAppM(v___x_6091_, v___x_6095_, v_a_6086_, v_a_6087_, v_a_6088_, v_a_6089_);
return v___x_6096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6097_, lean_object* v_h_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_, lean_object* v_a_6103_){
_start:
{
lean_object* v_res_6104_; 
v_res_6104_ = l_Lean_Meta_mkLetValCongr(v_b_6097_, v_h_6098_, v_a_6099_, v_a_6100_, v_a_6101_, v_a_6102_);
lean_dec(v_a_6102_);
lean_dec_ref(v_a_6101_);
lean_dec(v_a_6100_);
lean_dec_ref(v_a_6099_);
return v_res_6104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6108_, lean_object* v_h_6109_, lean_object* v_a_6110_, lean_object* v_a_6111_, lean_object* v_a_6112_, lean_object* v_a_6113_){
_start:
{
lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; 
v___x_6115_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6116_ = lean_unsigned_to_nat(2u);
v___x_6117_ = lean_mk_empty_array_with_capacity(v___x_6116_);
v___x_6118_ = lean_array_push(v___x_6117_, v_a_6108_);
v___x_6119_ = lean_array_push(v___x_6118_, v_h_6109_);
v___x_6120_ = l_Lean_Meta_mkAppM(v___x_6115_, v___x_6119_, v_a_6110_, v_a_6111_, v_a_6112_, v_a_6113_);
return v___x_6120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6121_, lean_object* v_h_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_, lean_object* v_a_6125_, lean_object* v_a_6126_, lean_object* v_a_6127_){
_start:
{
lean_object* v_res_6128_; 
v_res_6128_ = l_Lean_Meta_mkLetBodyCongr(v_a_6121_, v_h_6122_, v_a_6123_, v_a_6124_, v_a_6125_, v_a_6126_);
lean_dec(v_a_6126_);
lean_dec_ref(v_a_6125_);
lean_dec(v_a_6124_);
lean_dec_ref(v_a_6123_);
return v_res_6128_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; 
v___x_6132_ = lean_box(0);
v___x_6133_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6134_ = l_Lean_mkConst(v___x_6133_, v___x_6132_);
return v___x_6134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6138_, lean_object* v_h_6139_){
_start:
{
lean_object* v___x_6143_; uint8_t v___x_6144_; 
v___x_6143_ = l_Lean_Expr_cleanupAnnotations(v_h_6139_);
v___x_6144_ = l_Lean_Expr_isApp(v___x_6143_);
if (v___x_6144_ == 0)
{
lean_dec_ref(v___x_6143_);
goto v___jp_6140_;
}
else
{
lean_object* v___x_6145_; uint8_t v___x_6146_; 
v___x_6145_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6143_);
v___x_6146_ = l_Lean_Expr_isApp(v___x_6145_);
if (v___x_6146_ == 0)
{
lean_dec_ref(v___x_6145_);
lean_dec_ref(v___x_6143_);
goto v___jp_6140_;
}
else
{
lean_object* v___x_6147_; lean_object* v___x_6148_; uint8_t v___x_6149_; 
v___x_6147_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6145_);
lean_dec_ref(v___x_6145_);
v___x_6148_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6149_ = l_Lean_Expr_isConstOf(v___x_6147_, v___x_6148_);
lean_dec_ref(v___x_6147_);
if (v___x_6149_ == 0)
{
lean_dec_ref(v___x_6143_);
goto v___jp_6140_;
}
else
{
lean_object* v_arg_6150_; 
lean_dec_ref(v_h_6139_);
lean_dec_ref(v_p_6138_);
v_arg_6150_ = lean_ctor_get(v___x_6143_, 1);
lean_inc_ref(v_arg_6150_);
lean_dec_ref(v___x_6143_);
return v_arg_6150_;
}
}
}
v___jp_6140_:
{
lean_object* v___x_6141_; lean_object* v___x_6142_; 
v___x_6141_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6142_ = l_Lean_mkAppB(v___x_6141_, v_p_6138_, v_h_6139_);
return v___x_6142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6151_, lean_object* v_a_6152_, lean_object* v_a_6153_, lean_object* v_a_6154_, lean_object* v_a_6155_){
_start:
{
lean_object* v___y_6158_; lean_object* v___y_6159_; lean_object* v___y_6160_; lean_object* v___y_6161_; lean_object* v___x_6167_; 
lean_inc_ref(v_h_6151_);
v___x_6167_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6151_, v_a_6153_);
if (lean_obj_tag(v___x_6167_) == 0)
{
lean_object* v_a_6168_; lean_object* v___x_6170_; uint8_t v_isShared_6171_; uint8_t v_isSharedCheck_6183_; 
v_a_6168_ = lean_ctor_get(v___x_6167_, 0);
v_isSharedCheck_6183_ = !lean_is_exclusive(v___x_6167_);
if (v_isSharedCheck_6183_ == 0)
{
v___x_6170_ = v___x_6167_;
v_isShared_6171_ = v_isSharedCheck_6183_;
goto v_resetjp_6169_;
}
else
{
lean_inc(v_a_6168_);
lean_dec(v___x_6167_);
v___x_6170_ = lean_box(0);
v_isShared_6171_ = v_isSharedCheck_6183_;
goto v_resetjp_6169_;
}
v_resetjp_6169_:
{
lean_object* v___x_6172_; uint8_t v___x_6173_; 
v___x_6172_ = l_Lean_Expr_cleanupAnnotations(v_a_6168_);
lean_dec(v_a_6168_);
v___x_6173_ = l_Lean_Expr_isApp(v___x_6172_);
if (v___x_6173_ == 0)
{
lean_dec_ref(v___x_6172_);
lean_del_object(v___x_6170_);
v___y_6158_ = v_a_6152_;
v___y_6159_ = v_a_6153_;
v___y_6160_ = v_a_6154_;
v___y_6161_ = v_a_6155_;
goto v___jp_6157_;
}
else
{
lean_object* v___x_6174_; uint8_t v___x_6175_; 
v___x_6174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6172_);
v___x_6175_ = l_Lean_Expr_isApp(v___x_6174_);
if (v___x_6175_ == 0)
{
lean_dec_ref(v___x_6174_);
lean_dec_ref(v___x_6172_);
lean_del_object(v___x_6170_);
v___y_6158_ = v_a_6152_;
v___y_6159_ = v_a_6153_;
v___y_6160_ = v_a_6154_;
v___y_6161_ = v_a_6155_;
goto v___jp_6157_;
}
else
{
lean_object* v___x_6176_; lean_object* v___x_6177_; uint8_t v___x_6178_; 
v___x_6176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6174_);
lean_dec_ref(v___x_6174_);
v___x_6177_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6178_ = l_Lean_Expr_isConstOf(v___x_6176_, v___x_6177_);
lean_dec_ref(v___x_6176_);
if (v___x_6178_ == 0)
{
lean_dec_ref(v___x_6172_);
lean_del_object(v___x_6170_);
v___y_6158_ = v_a_6152_;
v___y_6159_ = v_a_6153_;
v___y_6160_ = v_a_6154_;
v___y_6161_ = v_a_6155_;
goto v___jp_6157_;
}
else
{
lean_object* v_arg_6179_; lean_object* v___x_6181_; 
lean_dec_ref(v_h_6151_);
v_arg_6179_ = lean_ctor_get(v___x_6172_, 1);
lean_inc_ref(v_arg_6179_);
lean_dec_ref(v___x_6172_);
if (v_isShared_6171_ == 0)
{
lean_ctor_set(v___x_6170_, 0, v_arg_6179_);
v___x_6181_ = v___x_6170_;
goto v_reusejp_6180_;
}
else
{
lean_object* v_reuseFailAlloc_6182_; 
v_reuseFailAlloc_6182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6182_, 0, v_arg_6179_);
v___x_6181_ = v_reuseFailAlloc_6182_;
goto v_reusejp_6180_;
}
v_reusejp_6180_:
{
return v___x_6181_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6151_);
return v___x_6167_;
}
v___jp_6157_:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; 
v___x_6162_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6163_ = lean_unsigned_to_nat(1u);
v___x_6164_ = lean_mk_empty_array_with_capacity(v___x_6163_);
v___x_6165_ = lean_array_push(v___x_6164_, v_h_6151_);
v___x_6166_ = l_Lean_Meta_mkAppM(v___x_6162_, v___x_6165_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_);
return v___x_6166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_, lean_object* v_a_6187_, lean_object* v_a_6188_, lean_object* v_a_6189_){
_start:
{
lean_object* v_res_6190_; 
v_res_6190_ = l_Lean_Meta_mkOfEqFalse(v_h_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_);
lean_dec(v_a_6188_);
lean_dec_ref(v_a_6187_);
lean_dec(v_a_6186_);
lean_dec_ref(v_a_6185_);
return v_res_6190_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6194_ = lean_box(0);
v___x_6195_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6196_ = l_Lean_mkConst(v___x_6195_, v___x_6194_);
return v___x_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6200_, lean_object* v_h_6201_){
_start:
{
lean_object* v___x_6205_; uint8_t v___x_6206_; 
v___x_6205_ = l_Lean_Expr_cleanupAnnotations(v_h_6201_);
v___x_6206_ = l_Lean_Expr_isApp(v___x_6205_);
if (v___x_6206_ == 0)
{
lean_dec_ref(v___x_6205_);
goto v___jp_6202_;
}
else
{
lean_object* v___x_6207_; uint8_t v___x_6208_; 
v___x_6207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6205_);
v___x_6208_ = l_Lean_Expr_isApp(v___x_6207_);
if (v___x_6208_ == 0)
{
lean_dec_ref(v___x_6207_);
lean_dec_ref(v___x_6205_);
goto v___jp_6202_;
}
else
{
lean_object* v___x_6209_; lean_object* v___x_6210_; uint8_t v___x_6211_; 
v___x_6209_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6207_);
lean_dec_ref(v___x_6207_);
v___x_6210_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6211_ = l_Lean_Expr_isConstOf(v___x_6209_, v___x_6210_);
lean_dec_ref(v___x_6209_);
if (v___x_6211_ == 0)
{
lean_dec_ref(v___x_6205_);
goto v___jp_6202_;
}
else
{
lean_object* v_arg_6212_; 
lean_dec_ref(v_h_6201_);
lean_dec_ref(v_p_6200_);
v_arg_6212_ = lean_ctor_get(v___x_6205_, 1);
lean_inc_ref(v_arg_6212_);
lean_dec_ref(v___x_6205_);
return v_arg_6212_;
}
}
}
v___jp_6202_:
{
lean_object* v___x_6203_; lean_object* v___x_6204_; 
v___x_6203_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6204_ = l_Lean_mkAppB(v___x_6203_, v_p_6200_, v_h_6201_);
return v___x_6204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6213_, lean_object* v_a_6214_, lean_object* v_a_6215_, lean_object* v_a_6216_, lean_object* v_a_6217_){
_start:
{
lean_object* v___y_6220_; lean_object* v___y_6221_; lean_object* v___y_6222_; lean_object* v___y_6223_; lean_object* v___x_6229_; 
lean_inc_ref(v_h_6213_);
v___x_6229_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6213_, v_a_6215_);
if (lean_obj_tag(v___x_6229_) == 0)
{
lean_object* v_a_6230_; lean_object* v___x_6232_; uint8_t v_isShared_6233_; uint8_t v_isSharedCheck_6245_; 
v_a_6230_ = lean_ctor_get(v___x_6229_, 0);
v_isSharedCheck_6245_ = !lean_is_exclusive(v___x_6229_);
if (v_isSharedCheck_6245_ == 0)
{
v___x_6232_ = v___x_6229_;
v_isShared_6233_ = v_isSharedCheck_6245_;
goto v_resetjp_6231_;
}
else
{
lean_inc(v_a_6230_);
lean_dec(v___x_6229_);
v___x_6232_ = lean_box(0);
v_isShared_6233_ = v_isSharedCheck_6245_;
goto v_resetjp_6231_;
}
v_resetjp_6231_:
{
lean_object* v___x_6234_; uint8_t v___x_6235_; 
v___x_6234_ = l_Lean_Expr_cleanupAnnotations(v_a_6230_);
lean_dec(v_a_6230_);
v___x_6235_ = l_Lean_Expr_isApp(v___x_6234_);
if (v___x_6235_ == 0)
{
lean_dec_ref(v___x_6234_);
lean_del_object(v___x_6232_);
v___y_6220_ = v_a_6214_;
v___y_6221_ = v_a_6215_;
v___y_6222_ = v_a_6216_;
v___y_6223_ = v_a_6217_;
goto v___jp_6219_;
}
else
{
lean_object* v___x_6236_; uint8_t v___x_6237_; 
v___x_6236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6234_);
v___x_6237_ = l_Lean_Expr_isApp(v___x_6236_);
if (v___x_6237_ == 0)
{
lean_dec_ref(v___x_6236_);
lean_dec_ref(v___x_6234_);
lean_del_object(v___x_6232_);
v___y_6220_ = v_a_6214_;
v___y_6221_ = v_a_6215_;
v___y_6222_ = v_a_6216_;
v___y_6223_ = v_a_6217_;
goto v___jp_6219_;
}
else
{
lean_object* v___x_6238_; lean_object* v___x_6239_; uint8_t v___x_6240_; 
v___x_6238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6236_);
lean_dec_ref(v___x_6236_);
v___x_6239_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6240_ = l_Lean_Expr_isConstOf(v___x_6238_, v___x_6239_);
lean_dec_ref(v___x_6238_);
if (v___x_6240_ == 0)
{
lean_dec_ref(v___x_6234_);
lean_del_object(v___x_6232_);
v___y_6220_ = v_a_6214_;
v___y_6221_ = v_a_6215_;
v___y_6222_ = v_a_6216_;
v___y_6223_ = v_a_6217_;
goto v___jp_6219_;
}
else
{
lean_object* v_arg_6241_; lean_object* v___x_6243_; 
lean_dec_ref(v_h_6213_);
v_arg_6241_ = lean_ctor_get(v___x_6234_, 1);
lean_inc_ref(v_arg_6241_);
lean_dec_ref(v___x_6234_);
if (v_isShared_6233_ == 0)
{
lean_ctor_set(v___x_6232_, 0, v_arg_6241_);
v___x_6243_ = v___x_6232_;
goto v_reusejp_6242_;
}
else
{
lean_object* v_reuseFailAlloc_6244_; 
v_reuseFailAlloc_6244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6244_, 0, v_arg_6241_);
v___x_6243_ = v_reuseFailAlloc_6244_;
goto v_reusejp_6242_;
}
v_reusejp_6242_:
{
return v___x_6243_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6213_);
return v___x_6229_;
}
v___jp_6219_:
{
lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v___x_6224_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6225_ = lean_unsigned_to_nat(1u);
v___x_6226_ = lean_mk_empty_array_with_capacity(v___x_6225_);
v___x_6227_ = lean_array_push(v___x_6226_, v_h_6213_);
v___x_6228_ = l_Lean_Meta_mkAppM(v___x_6224_, v___x_6227_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_);
return v___x_6228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6246_, lean_object* v_a_6247_, lean_object* v_a_6248_, lean_object* v_a_6249_, lean_object* v_a_6250_, lean_object* v_a_6251_){
_start:
{
lean_object* v_res_6252_; 
v_res_6252_ = l_Lean_Meta_mkOfEqTrue(v_h_6246_, v_a_6247_, v_a_6248_, v_a_6249_, v_a_6250_);
lean_dec(v_a_6250_);
lean_dec_ref(v_a_6249_);
lean_dec(v_a_6248_);
lean_dec_ref(v_a_6247_);
return v_res_6252_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6253_ = lean_box(0);
v___x_6254_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6255_ = l_Lean_mkConst(v___x_6254_, v___x_6253_);
return v___x_6255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6256_, lean_object* v_h_6257_){
_start:
{
lean_object* v___x_6261_; uint8_t v___x_6262_; 
v___x_6261_ = l_Lean_Expr_cleanupAnnotations(v_h_6257_);
v___x_6262_ = l_Lean_Expr_isApp(v___x_6261_);
if (v___x_6262_ == 0)
{
lean_dec_ref(v___x_6261_);
goto v___jp_6258_;
}
else
{
lean_object* v___x_6263_; uint8_t v___x_6264_; 
v___x_6263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6261_);
v___x_6264_ = l_Lean_Expr_isApp(v___x_6263_);
if (v___x_6264_ == 0)
{
lean_dec_ref(v___x_6263_);
lean_dec_ref(v___x_6261_);
goto v___jp_6258_;
}
else
{
lean_object* v___x_6265_; lean_object* v___x_6266_; uint8_t v___x_6267_; 
v___x_6265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6263_);
lean_dec_ref(v___x_6263_);
v___x_6266_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6267_ = l_Lean_Expr_isConstOf(v___x_6265_, v___x_6266_);
lean_dec_ref(v___x_6265_);
if (v___x_6267_ == 0)
{
lean_dec_ref(v___x_6261_);
goto v___jp_6258_;
}
else
{
lean_object* v_arg_6268_; 
lean_dec_ref(v_h_6257_);
lean_dec_ref(v_p_6256_);
v_arg_6268_ = lean_ctor_get(v___x_6261_, 1);
lean_inc_ref(v_arg_6268_);
lean_dec_ref(v___x_6261_);
return v_arg_6268_;
}
}
}
v___jp_6258_:
{
lean_object* v___x_6259_; lean_object* v___x_6260_; 
v___x_6259_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6260_ = l_Lean_mkAppB(v___x_6259_, v_p_6256_, v_h_6257_);
return v___x_6260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6269_, lean_object* v_a_6270_, lean_object* v_a_6271_, lean_object* v_a_6272_, lean_object* v_a_6273_){
_start:
{
lean_object* v___y_6276_; lean_object* v___y_6277_; lean_object* v___y_6278_; lean_object* v___y_6279_; lean_object* v___x_6291_; 
lean_inc_ref(v_h_6269_);
v___x_6291_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6269_, v_a_6271_);
if (lean_obj_tag(v___x_6291_) == 0)
{
lean_object* v_a_6292_; lean_object* v___x_6294_; uint8_t v_isShared_6295_; uint8_t v_isSharedCheck_6307_; 
v_a_6292_ = lean_ctor_get(v___x_6291_, 0);
v_isSharedCheck_6307_ = !lean_is_exclusive(v___x_6291_);
if (v_isSharedCheck_6307_ == 0)
{
v___x_6294_ = v___x_6291_;
v_isShared_6295_ = v_isSharedCheck_6307_;
goto v_resetjp_6293_;
}
else
{
lean_inc(v_a_6292_);
lean_dec(v___x_6291_);
v___x_6294_ = lean_box(0);
v_isShared_6295_ = v_isSharedCheck_6307_;
goto v_resetjp_6293_;
}
v_resetjp_6293_:
{
lean_object* v___x_6296_; uint8_t v___x_6297_; 
v___x_6296_ = l_Lean_Expr_cleanupAnnotations(v_a_6292_);
lean_dec(v_a_6292_);
v___x_6297_ = l_Lean_Expr_isApp(v___x_6296_);
if (v___x_6297_ == 0)
{
lean_dec_ref(v___x_6296_);
lean_del_object(v___x_6294_);
v___y_6276_ = v_a_6270_;
v___y_6277_ = v_a_6271_;
v___y_6278_ = v_a_6272_;
v___y_6279_ = v_a_6273_;
goto v___jp_6275_;
}
else
{
lean_object* v___x_6298_; uint8_t v___x_6299_; 
v___x_6298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6296_);
v___x_6299_ = l_Lean_Expr_isApp(v___x_6298_);
if (v___x_6299_ == 0)
{
lean_dec_ref(v___x_6298_);
lean_dec_ref(v___x_6296_);
lean_del_object(v___x_6294_);
v___y_6276_ = v_a_6270_;
v___y_6277_ = v_a_6271_;
v___y_6278_ = v_a_6272_;
v___y_6279_ = v_a_6273_;
goto v___jp_6275_;
}
else
{
lean_object* v___x_6300_; lean_object* v___x_6301_; uint8_t v___x_6302_; 
v___x_6300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6298_);
lean_dec_ref(v___x_6298_);
v___x_6301_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6302_ = l_Lean_Expr_isConstOf(v___x_6300_, v___x_6301_);
lean_dec_ref(v___x_6300_);
if (v___x_6302_ == 0)
{
lean_dec_ref(v___x_6296_);
lean_del_object(v___x_6294_);
v___y_6276_ = v_a_6270_;
v___y_6277_ = v_a_6271_;
v___y_6278_ = v_a_6272_;
v___y_6279_ = v_a_6273_;
goto v___jp_6275_;
}
else
{
lean_object* v_arg_6303_; lean_object* v___x_6305_; 
lean_dec_ref(v_h_6269_);
v_arg_6303_ = lean_ctor_get(v___x_6296_, 1);
lean_inc_ref(v_arg_6303_);
lean_dec_ref(v___x_6296_);
if (v_isShared_6295_ == 0)
{
lean_ctor_set(v___x_6294_, 0, v_arg_6303_);
v___x_6305_ = v___x_6294_;
goto v_reusejp_6304_;
}
else
{
lean_object* v_reuseFailAlloc_6306_; 
v_reuseFailAlloc_6306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_arg_6303_);
v___x_6305_ = v_reuseFailAlloc_6306_;
goto v_reusejp_6304_;
}
v_reusejp_6304_:
{
return v___x_6305_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6269_);
return v___x_6291_;
}
v___jp_6275_:
{
lean_object* v___x_6280_; 
lean_inc(v___y_6279_);
lean_inc_ref(v___y_6278_);
lean_inc(v___y_6277_);
lean_inc_ref(v___y_6276_);
lean_inc_ref(v_h_6269_);
v___x_6280_ = lean_infer_type(v_h_6269_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_);
if (lean_obj_tag(v___x_6280_) == 0)
{
lean_object* v_a_6281_; lean_object* v___x_6283_; uint8_t v_isShared_6284_; uint8_t v_isSharedCheck_6290_; 
v_a_6281_ = lean_ctor_get(v___x_6280_, 0);
v_isSharedCheck_6290_ = !lean_is_exclusive(v___x_6280_);
if (v_isSharedCheck_6290_ == 0)
{
v___x_6283_ = v___x_6280_;
v_isShared_6284_ = v_isSharedCheck_6290_;
goto v_resetjp_6282_;
}
else
{
lean_inc(v_a_6281_);
lean_dec(v___x_6280_);
v___x_6283_ = lean_box(0);
v_isShared_6284_ = v_isSharedCheck_6290_;
goto v_resetjp_6282_;
}
v_resetjp_6282_:
{
lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6288_; 
v___x_6285_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6286_ = l_Lean_mkAppB(v___x_6285_, v_a_6281_, v_h_6269_);
if (v_isShared_6284_ == 0)
{
lean_ctor_set(v___x_6283_, 0, v___x_6286_);
v___x_6288_ = v___x_6283_;
goto v_reusejp_6287_;
}
else
{
lean_object* v_reuseFailAlloc_6289_; 
v_reuseFailAlloc_6289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6289_, 0, v___x_6286_);
v___x_6288_ = v_reuseFailAlloc_6289_;
goto v_reusejp_6287_;
}
v_reusejp_6287_:
{
return v___x_6288_;
}
}
}
else
{
lean_dec_ref(v_h_6269_);
return v___x_6280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_, lean_object* v_a_6311_, lean_object* v_a_6312_, lean_object* v_a_6313_){
_start:
{
lean_object* v_res_6314_; 
v_res_6314_ = l_Lean_Meta_mkEqTrue(v_h_6308_, v_a_6309_, v_a_6310_, v_a_6311_, v_a_6312_);
lean_dec(v_a_6312_);
lean_dec_ref(v_a_6311_);
lean_dec(v_a_6310_);
lean_dec_ref(v_a_6309_);
return v_res_6314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_, lean_object* v_a_6318_, lean_object* v_a_6319_){
_start:
{
lean_object* v___y_6322_; lean_object* v___y_6323_; lean_object* v___y_6324_; lean_object* v___y_6325_; lean_object* v___x_6331_; uint8_t v___x_6332_; 
v___x_6331_ = l_Lean_Expr_cleanupAnnotations(v_h_6315_);
v___x_6332_ = l_Lean_Expr_isApp(v___x_6331_);
if (v___x_6332_ == 0)
{
lean_dec_ref(v___x_6331_);
v___y_6322_ = v_a_6316_;
v___y_6323_ = v_a_6317_;
v___y_6324_ = v_a_6318_;
v___y_6325_ = v_a_6319_;
goto v___jp_6321_;
}
else
{
lean_object* v___x_6333_; uint8_t v___x_6334_; 
v___x_6333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6331_);
v___x_6334_ = l_Lean_Expr_isApp(v___x_6333_);
if (v___x_6334_ == 0)
{
lean_dec_ref(v___x_6333_);
lean_dec_ref(v___x_6331_);
v___y_6322_ = v_a_6316_;
v___y_6323_ = v_a_6317_;
v___y_6324_ = v_a_6318_;
v___y_6325_ = v_a_6319_;
goto v___jp_6321_;
}
else
{
lean_object* v___x_6335_; lean_object* v___x_6336_; uint8_t v___x_6337_; 
v___x_6335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6333_);
lean_dec_ref(v___x_6333_);
v___x_6336_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6337_ = l_Lean_Expr_isConstOf(v___x_6335_, v___x_6336_);
lean_dec_ref(v___x_6335_);
if (v___x_6337_ == 0)
{
lean_dec_ref(v___x_6331_);
v___y_6322_ = v_a_6316_;
v___y_6323_ = v_a_6317_;
v___y_6324_ = v_a_6318_;
v___y_6325_ = v_a_6319_;
goto v___jp_6321_;
}
else
{
lean_object* v_arg_6338_; lean_object* v___x_6339_; 
lean_dec_ref(v_h_6315_);
v_arg_6338_ = lean_ctor_get(v___x_6331_, 1);
lean_inc_ref(v_arg_6338_);
lean_dec_ref(v___x_6331_);
v___x_6339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6339_, 0, v_arg_6338_);
return v___x_6339_;
}
}
}
v___jp_6321_:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; lean_object* v___x_6329_; lean_object* v___x_6330_; 
v___x_6326_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6327_ = lean_unsigned_to_nat(1u);
v___x_6328_ = lean_mk_empty_array_with_capacity(v___x_6327_);
v___x_6329_ = lean_array_push(v___x_6328_, v_h_6315_);
v___x_6330_ = l_Lean_Meta_mkAppM(v___x_6326_, v___x_6329_, v___y_6322_, v___y_6323_, v___y_6324_, v___y_6325_);
return v___x_6330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_, lean_object* v_a_6344_, lean_object* v_a_6345_){
_start:
{
lean_object* v_res_6346_; 
v_res_6346_ = l_Lean_Meta_mkEqFalse(v_h_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_);
lean_dec(v_a_6344_);
lean_dec_ref(v_a_6343_);
lean_dec(v_a_6342_);
lean_dec_ref(v_a_6341_);
return v_res_6346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6350_, lean_object* v_a_6351_, lean_object* v_a_6352_, lean_object* v_a_6353_, lean_object* v_a_6354_){
_start:
{
lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; 
v___x_6356_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6357_ = lean_unsigned_to_nat(1u);
v___x_6358_ = lean_mk_empty_array_with_capacity(v___x_6357_);
v___x_6359_ = lean_array_push(v___x_6358_, v_h_6350_);
v___x_6360_ = l_Lean_Meta_mkAppM(v___x_6356_, v___x_6359_, v_a_6351_, v_a_6352_, v_a_6353_, v_a_6354_);
return v___x_6360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6361_, lean_object* v_a_6362_, lean_object* v_a_6363_, lean_object* v_a_6364_, lean_object* v_a_6365_, lean_object* v_a_6366_){
_start:
{
lean_object* v_res_6367_; 
v_res_6367_ = l_Lean_Meta_mkEqFalse_x27(v_h_6361_, v_a_6362_, v_a_6363_, v_a_6364_, v_a_6365_);
lean_dec(v_a_6365_);
lean_dec_ref(v_a_6364_);
lean_dec(v_a_6363_);
lean_dec_ref(v_a_6362_);
return v_res_6367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6371_, lean_object* v_h_u2082_6372_, lean_object* v_a_6373_, lean_object* v_a_6374_, lean_object* v_a_6375_, lean_object* v_a_6376_){
_start:
{
lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6378_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6379_ = lean_unsigned_to_nat(2u);
v___x_6380_ = lean_mk_empty_array_with_capacity(v___x_6379_);
v___x_6381_ = lean_array_push(v___x_6380_, v_h_u2081_6371_);
v___x_6382_ = lean_array_push(v___x_6381_, v_h_u2082_6372_);
v___x_6383_ = l_Lean_Meta_mkAppM(v___x_6378_, v___x_6382_, v_a_6373_, v_a_6374_, v_a_6375_, v_a_6376_);
return v___x_6383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6384_, lean_object* v_h_u2082_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_){
_start:
{
lean_object* v_res_6391_; 
v_res_6391_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6384_, v_h_u2082_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_);
lean_dec(v_a_6389_);
lean_dec_ref(v_a_6388_);
lean_dec(v_a_6387_);
lean_dec_ref(v_a_6386_);
return v_res_6391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6395_, lean_object* v_h_u2082_6396_, lean_object* v_a_6397_, lean_object* v_a_6398_, lean_object* v_a_6399_, lean_object* v_a_6400_){
_start:
{
lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6402_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6403_ = lean_unsigned_to_nat(2u);
v___x_6404_ = lean_mk_empty_array_with_capacity(v___x_6403_);
v___x_6405_ = lean_array_push(v___x_6404_, v_h_u2081_6395_);
v___x_6406_ = lean_array_push(v___x_6405_, v_h_u2082_6396_);
v___x_6407_ = l_Lean_Meta_mkAppM(v___x_6402_, v___x_6406_, v_a_6397_, v_a_6398_, v_a_6399_, v_a_6400_);
return v___x_6407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6408_, lean_object* v_h_u2082_6409_, lean_object* v_a_6410_, lean_object* v_a_6411_, lean_object* v_a_6412_, lean_object* v_a_6413_, lean_object* v_a_6414_){
_start:
{
lean_object* v_res_6415_; 
v_res_6415_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6408_, v_h_u2082_6409_, v_a_6410_, v_a_6411_, v_a_6412_, v_a_6413_);
lean_dec(v_a_6413_);
lean_dec_ref(v_a_6412_);
lean_dec(v_a_6411_);
lean_dec_ref(v_a_6410_);
return v_res_6415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6419_, lean_object* v_h_u2082_6420_, lean_object* v_a_6421_, lean_object* v_a_6422_, lean_object* v_a_6423_, lean_object* v_a_6424_){
_start:
{
lean_object* v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v___x_6431_; 
v___x_6426_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6427_ = lean_unsigned_to_nat(2u);
v___x_6428_ = lean_mk_empty_array_with_capacity(v___x_6427_);
v___x_6429_ = lean_array_push(v___x_6428_, v_h_u2081_6419_);
v___x_6430_ = lean_array_push(v___x_6429_, v_h_u2082_6420_);
v___x_6431_ = l_Lean_Meta_mkAppM(v___x_6426_, v___x_6430_, v_a_6421_, v_a_6422_, v_a_6423_, v_a_6424_);
return v___x_6431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6432_, lean_object* v_h_u2082_6433_, lean_object* v_a_6434_, lean_object* v_a_6435_, lean_object* v_a_6436_, lean_object* v_a_6437_, lean_object* v_a_6438_){
_start:
{
lean_object* v_res_6439_; 
v_res_6439_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6432_, v_h_u2082_6433_, v_a_6434_, v_a_6435_, v_a_6436_, v_a_6437_);
lean_dec(v_a_6437_);
lean_dec_ref(v_a_6436_);
lean_dec(v_a_6435_);
lean_dec_ref(v_a_6434_);
return v_res_6439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6443_, lean_object* v_a_6444_, lean_object* v_a_6445_, lean_object* v_a_6446_, lean_object* v_a_6447_){
_start:
{
lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; 
v___x_6449_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6450_ = lean_unsigned_to_nat(1u);
v___x_6451_ = lean_mk_empty_array_with_capacity(v___x_6450_);
v___x_6452_ = lean_array_push(v___x_6451_, v_h_6443_);
v___x_6453_ = l_Lean_Meta_mkAppM(v___x_6449_, v___x_6452_, v_a_6444_, v_a_6445_, v_a_6446_, v_a_6447_);
return v___x_6453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6454_, lean_object* v_a_6455_, lean_object* v_a_6456_, lean_object* v_a_6457_, lean_object* v_a_6458_, lean_object* v_a_6459_){
_start:
{
lean_object* v_res_6460_; 
v_res_6460_ = l_Lean_Meta_mkForallCongr(v_h_6454_, v_a_6455_, v_a_6456_, v_a_6457_, v_a_6458_);
lean_dec(v_a_6458_);
lean_dec_ref(v_a_6457_);
lean_dec(v_a_6456_);
lean_dec_ref(v_a_6455_);
return v_res_6460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_, lean_object* v_a_6467_, lean_object* v_a_6468_){
_start:
{
lean_object* v___y_6471_; lean_object* v_a_6472_; lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; 
v___x_6477_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6478_ = lean_unsigned_to_nat(1u);
v___x_6479_ = lean_mk_empty_array_with_capacity(v___x_6478_);
v___x_6480_ = lean_array_push(v___x_6479_, v_m_6464_);
v___x_6481_ = l_Lean_Meta_mkAppM(v___x_6477_, v___x_6480_, v_a_6465_, v_a_6466_, v_a_6467_, v_a_6468_);
if (lean_obj_tag(v___x_6481_) == 0)
{
lean_object* v_a_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v_a_6482_ = lean_ctor_get(v___x_6481_, 0);
lean_inc(v_a_6482_);
lean_dec_ref_known(v___x_6481_, 1);
v___x_6483_ = lean_box(0);
v___x_6484_ = l_Lean_Meta_trySynthInstance(v_a_6482_, v___x_6483_, v_a_6465_, v_a_6466_, v_a_6467_, v_a_6468_);
if (lean_obj_tag(v___x_6484_) == 0)
{
lean_object* v_a_6485_; lean_object* v___x_6487_; uint8_t v_isShared_6488_; uint8_t v_isSharedCheck_6503_; 
v_a_6485_ = lean_ctor_get(v___x_6484_, 0);
v_isSharedCheck_6503_ = !lean_is_exclusive(v___x_6484_);
if (v_isSharedCheck_6503_ == 0)
{
v___x_6487_ = v___x_6484_;
v_isShared_6488_ = v_isSharedCheck_6503_;
goto v_resetjp_6486_;
}
else
{
lean_inc(v_a_6485_);
lean_dec(v___x_6484_);
v___x_6487_ = lean_box(0);
v_isShared_6488_ = v_isSharedCheck_6503_;
goto v_resetjp_6486_;
}
v_resetjp_6486_:
{
if (lean_obj_tag(v_a_6485_) == 1)
{
lean_object* v_a_6489_; lean_object* v___x_6491_; uint8_t v_isShared_6492_; uint8_t v_isSharedCheck_6499_; 
v_a_6489_ = lean_ctor_get(v_a_6485_, 0);
v_isSharedCheck_6499_ = !lean_is_exclusive(v_a_6485_);
if (v_isSharedCheck_6499_ == 0)
{
v___x_6491_ = v_a_6485_;
v_isShared_6492_ = v_isSharedCheck_6499_;
goto v_resetjp_6490_;
}
else
{
lean_inc(v_a_6489_);
lean_dec(v_a_6485_);
v___x_6491_ = lean_box(0);
v_isShared_6492_ = v_isSharedCheck_6499_;
goto v_resetjp_6490_;
}
v_resetjp_6490_:
{
lean_object* v___x_6494_; 
if (v_isShared_6492_ == 0)
{
v___x_6494_ = v___x_6491_;
goto v_reusejp_6493_;
}
else
{
lean_object* v_reuseFailAlloc_6498_; 
v_reuseFailAlloc_6498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6498_, 0, v_a_6489_);
v___x_6494_ = v_reuseFailAlloc_6498_;
goto v_reusejp_6493_;
}
v_reusejp_6493_:
{
lean_object* v___x_6496_; 
if (v_isShared_6488_ == 0)
{
lean_ctor_set(v___x_6487_, 0, v___x_6494_);
v___x_6496_ = v___x_6487_;
goto v_reusejp_6495_;
}
else
{
lean_object* v_reuseFailAlloc_6497_; 
v_reuseFailAlloc_6497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6497_, 0, v___x_6494_);
v___x_6496_ = v_reuseFailAlloc_6497_;
goto v_reusejp_6495_;
}
v_reusejp_6495_:
{
return v___x_6496_;
}
}
}
}
else
{
lean_object* v___x_6501_; 
lean_dec(v_a_6485_);
if (v_isShared_6488_ == 0)
{
lean_ctor_set(v___x_6487_, 0, v___x_6483_);
v___x_6501_ = v___x_6487_;
goto v_reusejp_6500_;
}
else
{
lean_object* v_reuseFailAlloc_6502_; 
v_reuseFailAlloc_6502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6502_, 0, v___x_6483_);
v___x_6501_ = v_reuseFailAlloc_6502_;
goto v_reusejp_6500_;
}
v_reusejp_6500_:
{
return v___x_6501_;
}
}
}
}
else
{
lean_object* v_a_6504_; lean_object* v___x_6506_; uint8_t v_isShared_6507_; uint8_t v_isSharedCheck_6511_; 
v_a_6504_ = lean_ctor_get(v___x_6484_, 0);
v_isSharedCheck_6511_ = !lean_is_exclusive(v___x_6484_);
if (v_isSharedCheck_6511_ == 0)
{
v___x_6506_ = v___x_6484_;
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
else
{
lean_inc(v_a_6504_);
lean_dec(v___x_6484_);
v___x_6506_ = lean_box(0);
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
v_resetjp_6505_:
{
lean_object* v___x_6509_; 
lean_inc(v_a_6504_);
if (v_isShared_6507_ == 0)
{
v___x_6509_ = v___x_6506_;
goto v_reusejp_6508_;
}
else
{
lean_object* v_reuseFailAlloc_6510_; 
v_reuseFailAlloc_6510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_a_6504_);
v___x_6509_ = v_reuseFailAlloc_6510_;
goto v_reusejp_6508_;
}
v_reusejp_6508_:
{
v___y_6471_ = v___x_6509_;
v_a_6472_ = v_a_6504_;
goto v___jp_6470_;
}
}
}
}
else
{
lean_object* v_a_6512_; lean_object* v___x_6514_; uint8_t v_isShared_6515_; uint8_t v_isSharedCheck_6519_; 
v_a_6512_ = lean_ctor_get(v___x_6481_, 0);
v_isSharedCheck_6519_ = !lean_is_exclusive(v___x_6481_);
if (v_isSharedCheck_6519_ == 0)
{
v___x_6514_ = v___x_6481_;
v_isShared_6515_ = v_isSharedCheck_6519_;
goto v_resetjp_6513_;
}
else
{
lean_inc(v_a_6512_);
lean_dec(v___x_6481_);
v___x_6514_ = lean_box(0);
v_isShared_6515_ = v_isSharedCheck_6519_;
goto v_resetjp_6513_;
}
v_resetjp_6513_:
{
lean_object* v___x_6517_; 
lean_inc(v_a_6512_);
if (v_isShared_6515_ == 0)
{
v___x_6517_ = v___x_6514_;
goto v_reusejp_6516_;
}
else
{
lean_object* v_reuseFailAlloc_6518_; 
v_reuseFailAlloc_6518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6518_, 0, v_a_6512_);
v___x_6517_ = v_reuseFailAlloc_6518_;
goto v_reusejp_6516_;
}
v_reusejp_6516_:
{
v___y_6471_ = v___x_6517_;
v_a_6472_ = v_a_6512_;
goto v___jp_6470_;
}
}
}
v___jp_6470_:
{
uint8_t v___x_6473_; 
v___x_6473_ = l_Lean_Exception_isInterrupt(v_a_6472_);
if (v___x_6473_ == 0)
{
uint8_t v___x_6474_; 
v___x_6474_ = l_Lean_Exception_isRuntime(v_a_6472_);
if (v___x_6474_ == 0)
{
lean_object* v___x_6475_; lean_object* v___x_6476_; 
lean_dec_ref(v___y_6471_);
v___x_6475_ = lean_box(0);
v___x_6476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6476_, 0, v___x_6475_);
return v___x_6476_;
}
else
{
return v___y_6471_;
}
}
else
{
lean_dec_ref(v_a_6472_);
return v___y_6471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6520_, lean_object* v_a_6521_, lean_object* v_a_6522_, lean_object* v_a_6523_, lean_object* v_a_6524_, lean_object* v_a_6525_){
_start:
{
lean_object* v_res_6526_; 
v_res_6526_ = l_Lean_Meta_isMonad_x3f(v_m_6520_, v_a_6521_, v_a_6522_, v_a_6523_, v_a_6524_);
lean_dec(v_a_6524_);
lean_dec_ref(v_a_6523_);
lean_dec(v_a_6522_);
lean_dec_ref(v_a_6521_);
return v_res_6526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6534_, lean_object* v_n_6535_, lean_object* v_a_6536_, lean_object* v_a_6537_, lean_object* v_a_6538_, lean_object* v_a_6539_){
_start:
{
lean_object* v___x_6541_; 
lean_inc_ref(v_type_6534_);
v___x_6541_ = l_Lean_Meta_getDecLevel(v_type_6534_, v_a_6536_, v_a_6537_, v_a_6538_, v_a_6539_);
if (lean_obj_tag(v___x_6541_) == 0)
{
lean_object* v_a_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; 
v_a_6542_ = lean_ctor_get(v___x_6541_, 0);
lean_inc(v_a_6542_);
lean_dec_ref_known(v___x_6541_, 1);
v___x_6543_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6544_ = lean_box(0);
v___x_6545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6545_, 0, v_a_6542_);
lean_ctor_set(v___x_6545_, 1, v___x_6544_);
lean_inc_ref(v___x_6545_);
v___x_6546_ = l_Lean_mkConst(v___x_6543_, v___x_6545_);
v___x_6547_ = l_Lean_mkRawNatLit(v_n_6535_);
lean_inc_ref(v___x_6547_);
lean_inc_ref(v_type_6534_);
v___x_6548_ = l_Lean_mkAppB(v___x_6546_, v_type_6534_, v___x_6547_);
v___x_6549_ = lean_box(0);
v___x_6550_ = l_Lean_Meta_synthInstance(v___x_6548_, v___x_6549_, v_a_6536_, v_a_6537_, v_a_6538_, v_a_6539_);
if (lean_obj_tag(v___x_6550_) == 0)
{
lean_object* v_a_6551_; lean_object* v___x_6553_; uint8_t v_isShared_6554_; uint8_t v_isSharedCheck_6561_; 
v_a_6551_ = lean_ctor_get(v___x_6550_, 0);
v_isSharedCheck_6561_ = !lean_is_exclusive(v___x_6550_);
if (v_isSharedCheck_6561_ == 0)
{
v___x_6553_ = v___x_6550_;
v_isShared_6554_ = v_isSharedCheck_6561_;
goto v_resetjp_6552_;
}
else
{
lean_inc(v_a_6551_);
lean_dec(v___x_6550_);
v___x_6553_ = lean_box(0);
v_isShared_6554_ = v_isSharedCheck_6561_;
goto v_resetjp_6552_;
}
v_resetjp_6552_:
{
lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6559_; 
v___x_6555_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6556_ = l_Lean_mkConst(v___x_6555_, v___x_6545_);
v___x_6557_ = l_Lean_mkApp3(v___x_6556_, v_type_6534_, v___x_6547_, v_a_6551_);
if (v_isShared_6554_ == 0)
{
lean_ctor_set(v___x_6553_, 0, v___x_6557_);
v___x_6559_ = v___x_6553_;
goto v_reusejp_6558_;
}
else
{
lean_object* v_reuseFailAlloc_6560_; 
v_reuseFailAlloc_6560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6560_, 0, v___x_6557_);
v___x_6559_ = v_reuseFailAlloc_6560_;
goto v_reusejp_6558_;
}
v_reusejp_6558_:
{
return v___x_6559_;
}
}
}
else
{
lean_dec_ref(v___x_6547_);
lean_dec_ref_known(v___x_6545_, 2);
lean_dec_ref(v_type_6534_);
return v___x_6550_;
}
}
else
{
lean_object* v_a_6562_; lean_object* v___x_6564_; uint8_t v_isShared_6565_; uint8_t v_isSharedCheck_6569_; 
lean_dec(v_n_6535_);
lean_dec_ref(v_type_6534_);
v_a_6562_ = lean_ctor_get(v___x_6541_, 0);
v_isSharedCheck_6569_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6569_ == 0)
{
v___x_6564_ = v___x_6541_;
v_isShared_6565_ = v_isSharedCheck_6569_;
goto v_resetjp_6563_;
}
else
{
lean_inc(v_a_6562_);
lean_dec(v___x_6541_);
v___x_6564_ = lean_box(0);
v_isShared_6565_ = v_isSharedCheck_6569_;
goto v_resetjp_6563_;
}
v_resetjp_6563_:
{
lean_object* v___x_6567_; 
if (v_isShared_6565_ == 0)
{
v___x_6567_ = v___x_6564_;
goto v_reusejp_6566_;
}
else
{
lean_object* v_reuseFailAlloc_6568_; 
v_reuseFailAlloc_6568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6568_, 0, v_a_6562_);
v___x_6567_ = v_reuseFailAlloc_6568_;
goto v_reusejp_6566_;
}
v_reusejp_6566_:
{
return v___x_6567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6570_, lean_object* v_n_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_, lean_object* v_a_6575_, lean_object* v_a_6576_){
_start:
{
lean_object* v_res_6577_; 
v_res_6577_ = l_Lean_Meta_mkNumeral(v_type_6570_, v_n_6571_, v_a_6572_, v_a_6573_, v_a_6574_, v_a_6575_);
lean_dec(v_a_6575_);
lean_dec_ref(v_a_6574_);
lean_dec(v_a_6573_);
lean_dec_ref(v_a_6572_);
return v_res_6577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6578_, lean_object* v_opName_6579_, lean_object* v_a_6580_, lean_object* v_b_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_){
_start:
{
lean_object* v___x_6587_; 
lean_inc(v_a_6585_);
lean_inc_ref(v_a_6584_);
lean_inc(v_a_6583_);
lean_inc_ref(v_a_6582_);
lean_inc_ref(v_a_6580_);
v___x_6587_ = lean_infer_type(v_a_6580_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_);
if (lean_obj_tag(v___x_6587_) == 0)
{
lean_object* v_a_6588_; lean_object* v___x_6589_; 
v_a_6588_ = lean_ctor_get(v___x_6587_, 0);
lean_inc_n(v_a_6588_, 2);
lean_dec_ref_known(v___x_6587_, 1);
v___x_6589_ = l_Lean_Meta_getDecLevel(v_a_6588_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_);
if (lean_obj_tag(v___x_6589_) == 0)
{
lean_object* v_a_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; 
v_a_6590_ = lean_ctor_get(v___x_6589_, 0);
lean_inc_n(v_a_6590_, 3);
lean_dec_ref_known(v___x_6589_, 1);
v___x_6591_ = lean_box(0);
v___x_6592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6592_, 0, v_a_6590_);
lean_ctor_set(v___x_6592_, 1, v___x_6591_);
v___x_6593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6593_, 0, v_a_6590_);
lean_ctor_set(v___x_6593_, 1, v___x_6592_);
v___x_6594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6594_, 0, v_a_6590_);
lean_ctor_set(v___x_6594_, 1, v___x_6593_);
lean_inc_ref(v___x_6594_);
v___x_6595_ = l_Lean_mkConst(v_className_6578_, v___x_6594_);
lean_inc_n(v_a_6588_, 3);
v___x_6596_ = l_Lean_mkApp3(v___x_6595_, v_a_6588_, v_a_6588_, v_a_6588_);
v___x_6597_ = lean_box(0);
v___x_6598_ = l_Lean_Meta_synthInstance(v___x_6596_, v___x_6597_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_);
if (lean_obj_tag(v___x_6598_) == 0)
{
lean_object* v_a_6599_; lean_object* v___x_6601_; uint8_t v_isShared_6602_; uint8_t v_isSharedCheck_6608_; 
v_a_6599_ = lean_ctor_get(v___x_6598_, 0);
v_isSharedCheck_6608_ = !lean_is_exclusive(v___x_6598_);
if (v_isSharedCheck_6608_ == 0)
{
v___x_6601_ = v___x_6598_;
v_isShared_6602_ = v_isSharedCheck_6608_;
goto v_resetjp_6600_;
}
else
{
lean_inc(v_a_6599_);
lean_dec(v___x_6598_);
v___x_6601_ = lean_box(0);
v_isShared_6602_ = v_isSharedCheck_6608_;
goto v_resetjp_6600_;
}
v_resetjp_6600_:
{
lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6606_; 
v___x_6603_ = l_Lean_mkConst(v_opName_6579_, v___x_6594_);
lean_inc_n(v_a_6588_, 2);
v___x_6604_ = l_Lean_mkApp6(v___x_6603_, v_a_6588_, v_a_6588_, v_a_6588_, v_a_6599_, v_a_6580_, v_b_6581_);
if (v_isShared_6602_ == 0)
{
lean_ctor_set(v___x_6601_, 0, v___x_6604_);
v___x_6606_ = v___x_6601_;
goto v_reusejp_6605_;
}
else
{
lean_object* v_reuseFailAlloc_6607_; 
v_reuseFailAlloc_6607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6607_, 0, v___x_6604_);
v___x_6606_ = v_reuseFailAlloc_6607_;
goto v_reusejp_6605_;
}
v_reusejp_6605_:
{
return v___x_6606_;
}
}
}
else
{
lean_dec_ref_known(v___x_6594_, 2);
lean_dec(v_a_6588_);
lean_dec_ref(v_b_6581_);
lean_dec_ref(v_a_6580_);
lean_dec(v_opName_6579_);
return v___x_6598_;
}
}
else
{
lean_object* v_a_6609_; lean_object* v___x_6611_; uint8_t v_isShared_6612_; uint8_t v_isSharedCheck_6616_; 
lean_dec(v_a_6588_);
lean_dec_ref(v_b_6581_);
lean_dec_ref(v_a_6580_);
lean_dec(v_opName_6579_);
lean_dec(v_className_6578_);
v_a_6609_ = lean_ctor_get(v___x_6589_, 0);
v_isSharedCheck_6616_ = !lean_is_exclusive(v___x_6589_);
if (v_isSharedCheck_6616_ == 0)
{
v___x_6611_ = v___x_6589_;
v_isShared_6612_ = v_isSharedCheck_6616_;
goto v_resetjp_6610_;
}
else
{
lean_inc(v_a_6609_);
lean_dec(v___x_6589_);
v___x_6611_ = lean_box(0);
v_isShared_6612_ = v_isSharedCheck_6616_;
goto v_resetjp_6610_;
}
v_resetjp_6610_:
{
lean_object* v___x_6614_; 
if (v_isShared_6612_ == 0)
{
v___x_6614_ = v___x_6611_;
goto v_reusejp_6613_;
}
else
{
lean_object* v_reuseFailAlloc_6615_; 
v_reuseFailAlloc_6615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6615_, 0, v_a_6609_);
v___x_6614_ = v_reuseFailAlloc_6615_;
goto v_reusejp_6613_;
}
v_reusejp_6613_:
{
return v___x_6614_;
}
}
}
}
else
{
lean_dec_ref(v_b_6581_);
lean_dec_ref(v_a_6580_);
lean_dec(v_opName_6579_);
lean_dec(v_className_6578_);
return v___x_6587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6617_, lean_object* v_opName_6618_, lean_object* v_a_6619_, lean_object* v_b_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_){
_start:
{
lean_object* v_res_6626_; 
v_res_6626_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6617_, v_opName_6618_, v_a_6619_, v_b_6620_, v_a_6621_, v_a_6622_, v_a_6623_, v_a_6624_);
lean_dec(v_a_6624_);
lean_dec_ref(v_a_6623_);
lean_dec(v_a_6622_);
lean_dec_ref(v_a_6621_);
return v_res_6626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6634_, lean_object* v_b_6635_, lean_object* v_a_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_){
_start:
{
lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; 
v___x_6641_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6642_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6643_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6641_, v___x_6642_, v_a_6634_, v_b_6635_, v_a_6636_, v_a_6637_, v_a_6638_, v_a_6639_);
return v___x_6643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6644_, lean_object* v_b_6645_, lean_object* v_a_6646_, lean_object* v_a_6647_, lean_object* v_a_6648_, lean_object* v_a_6649_, lean_object* v_a_6650_){
_start:
{
lean_object* v_res_6651_; 
v_res_6651_ = l_Lean_Meta_mkAdd(v_a_6644_, v_b_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_);
lean_dec(v_a_6649_);
lean_dec_ref(v_a_6648_);
lean_dec(v_a_6647_);
lean_dec_ref(v_a_6646_);
return v_res_6651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6659_, lean_object* v_b_6660_, lean_object* v_a_6661_, lean_object* v_a_6662_, lean_object* v_a_6663_, lean_object* v_a_6664_){
_start:
{
lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; 
v___x_6666_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6667_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6668_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6666_, v___x_6667_, v_a_6659_, v_b_6660_, v_a_6661_, v_a_6662_, v_a_6663_, v_a_6664_);
return v___x_6668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6669_, lean_object* v_b_6670_, lean_object* v_a_6671_, lean_object* v_a_6672_, lean_object* v_a_6673_, lean_object* v_a_6674_, lean_object* v_a_6675_){
_start:
{
lean_object* v_res_6676_; 
v_res_6676_ = l_Lean_Meta_mkSub(v_a_6669_, v_b_6670_, v_a_6671_, v_a_6672_, v_a_6673_, v_a_6674_);
lean_dec(v_a_6674_);
lean_dec_ref(v_a_6673_);
lean_dec(v_a_6672_);
lean_dec_ref(v_a_6671_);
return v_res_6676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6684_, lean_object* v_b_6685_, lean_object* v_a_6686_, lean_object* v_a_6687_, lean_object* v_a_6688_, lean_object* v_a_6689_){
_start:
{
lean_object* v___x_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; 
v___x_6691_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6692_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6693_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6691_, v___x_6692_, v_a_6684_, v_b_6685_, v_a_6686_, v_a_6687_, v_a_6688_, v_a_6689_);
return v___x_6693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6694_, lean_object* v_b_6695_, lean_object* v_a_6696_, lean_object* v_a_6697_, lean_object* v_a_6698_, lean_object* v_a_6699_, lean_object* v_a_6700_){
_start:
{
lean_object* v_res_6701_; 
v_res_6701_ = l_Lean_Meta_mkMul(v_a_6694_, v_b_6695_, v_a_6696_, v_a_6697_, v_a_6698_, v_a_6699_);
lean_dec(v_a_6699_);
lean_dec_ref(v_a_6698_);
lean_dec(v_a_6697_);
lean_dec_ref(v_a_6696_);
return v_res_6701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6702_, lean_object* v_rName_6703_, lean_object* v_a_6704_, lean_object* v_b_6705_, lean_object* v_a_6706_, lean_object* v_a_6707_, lean_object* v_a_6708_, lean_object* v_a_6709_){
_start:
{
lean_object* v___x_6711_; 
lean_inc(v_a_6709_);
lean_inc_ref(v_a_6708_);
lean_inc(v_a_6707_);
lean_inc_ref(v_a_6706_);
lean_inc_ref(v_a_6704_);
v___x_6711_ = lean_infer_type(v_a_6704_, v_a_6706_, v_a_6707_, v_a_6708_, v_a_6709_);
if (lean_obj_tag(v___x_6711_) == 0)
{
lean_object* v_a_6712_; lean_object* v___x_6713_; 
v_a_6712_ = lean_ctor_get(v___x_6711_, 0);
lean_inc_n(v_a_6712_, 2);
lean_dec_ref_known(v___x_6711_, 1);
v___x_6713_ = l_Lean_Meta_getDecLevel(v_a_6712_, v_a_6706_, v_a_6707_, v_a_6708_, v_a_6709_);
if (lean_obj_tag(v___x_6713_) == 0)
{
lean_object* v_a_6714_; lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; lean_object* v___x_6720_; 
v_a_6714_ = lean_ctor_get(v___x_6713_, 0);
lean_inc(v_a_6714_);
lean_dec_ref_known(v___x_6713_, 1);
v___x_6715_ = lean_box(0);
v___x_6716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6716_, 0, v_a_6714_);
lean_ctor_set(v___x_6716_, 1, v___x_6715_);
lean_inc_ref(v___x_6716_);
v___x_6717_ = l_Lean_mkConst(v_className_6702_, v___x_6716_);
lean_inc(v_a_6712_);
v___x_6718_ = l_Lean_Expr_app___override(v___x_6717_, v_a_6712_);
v___x_6719_ = lean_box(0);
v___x_6720_ = l_Lean_Meta_synthInstance(v___x_6718_, v___x_6719_, v_a_6706_, v_a_6707_, v_a_6708_, v_a_6709_);
if (lean_obj_tag(v___x_6720_) == 0)
{
lean_object* v_a_6721_; lean_object* v___x_6723_; uint8_t v_isShared_6724_; uint8_t v_isSharedCheck_6730_; 
v_a_6721_ = lean_ctor_get(v___x_6720_, 0);
v_isSharedCheck_6730_ = !lean_is_exclusive(v___x_6720_);
if (v_isSharedCheck_6730_ == 0)
{
v___x_6723_ = v___x_6720_;
v_isShared_6724_ = v_isSharedCheck_6730_;
goto v_resetjp_6722_;
}
else
{
lean_inc(v_a_6721_);
lean_dec(v___x_6720_);
v___x_6723_ = lean_box(0);
v_isShared_6724_ = v_isSharedCheck_6730_;
goto v_resetjp_6722_;
}
v_resetjp_6722_:
{
lean_object* v___x_6725_; lean_object* v___x_6726_; lean_object* v___x_6728_; 
v___x_6725_ = l_Lean_mkConst(v_rName_6703_, v___x_6716_);
v___x_6726_ = l_Lean_mkApp4(v___x_6725_, v_a_6712_, v_a_6721_, v_a_6704_, v_b_6705_);
if (v_isShared_6724_ == 0)
{
lean_ctor_set(v___x_6723_, 0, v___x_6726_);
v___x_6728_ = v___x_6723_;
goto v_reusejp_6727_;
}
else
{
lean_object* v_reuseFailAlloc_6729_; 
v_reuseFailAlloc_6729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6729_, 0, v___x_6726_);
v___x_6728_ = v_reuseFailAlloc_6729_;
goto v_reusejp_6727_;
}
v_reusejp_6727_:
{
return v___x_6728_;
}
}
}
else
{
lean_dec_ref_known(v___x_6716_, 2);
lean_dec(v_a_6712_);
lean_dec_ref(v_b_6705_);
lean_dec_ref(v_a_6704_);
lean_dec(v_rName_6703_);
return v___x_6720_;
}
}
else
{
lean_object* v_a_6731_; lean_object* v___x_6733_; uint8_t v_isShared_6734_; uint8_t v_isSharedCheck_6738_; 
lean_dec(v_a_6712_);
lean_dec_ref(v_b_6705_);
lean_dec_ref(v_a_6704_);
lean_dec(v_rName_6703_);
lean_dec(v_className_6702_);
v_a_6731_ = lean_ctor_get(v___x_6713_, 0);
v_isSharedCheck_6738_ = !lean_is_exclusive(v___x_6713_);
if (v_isSharedCheck_6738_ == 0)
{
v___x_6733_ = v___x_6713_;
v_isShared_6734_ = v_isSharedCheck_6738_;
goto v_resetjp_6732_;
}
else
{
lean_inc(v_a_6731_);
lean_dec(v___x_6713_);
v___x_6733_ = lean_box(0);
v_isShared_6734_ = v_isSharedCheck_6738_;
goto v_resetjp_6732_;
}
v_resetjp_6732_:
{
lean_object* v___x_6736_; 
if (v_isShared_6734_ == 0)
{
v___x_6736_ = v___x_6733_;
goto v_reusejp_6735_;
}
else
{
lean_object* v_reuseFailAlloc_6737_; 
v_reuseFailAlloc_6737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6737_, 0, v_a_6731_);
v___x_6736_ = v_reuseFailAlloc_6737_;
goto v_reusejp_6735_;
}
v_reusejp_6735_:
{
return v___x_6736_;
}
}
}
}
else
{
lean_dec_ref(v_b_6705_);
lean_dec_ref(v_a_6704_);
lean_dec(v_rName_6703_);
lean_dec(v_className_6702_);
return v___x_6711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6739_, lean_object* v_rName_6740_, lean_object* v_a_6741_, lean_object* v_b_6742_, lean_object* v_a_6743_, lean_object* v_a_6744_, lean_object* v_a_6745_, lean_object* v_a_6746_, lean_object* v_a_6747_){
_start:
{
lean_object* v_res_6748_; 
v_res_6748_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6739_, v_rName_6740_, v_a_6741_, v_b_6742_, v_a_6743_, v_a_6744_, v_a_6745_, v_a_6746_);
lean_dec(v_a_6746_);
lean_dec_ref(v_a_6745_);
lean_dec(v_a_6744_);
lean_dec_ref(v_a_6743_);
return v_res_6748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6751_, lean_object* v_b_6752_, lean_object* v_a_6753_, lean_object* v_a_6754_, lean_object* v_a_6755_, lean_object* v_a_6756_){
_start:
{
lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; 
v___x_6758_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6759_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6760_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6758_, v___x_6759_, v_a_6751_, v_b_6752_, v_a_6753_, v_a_6754_, v_a_6755_, v_a_6756_);
return v___x_6760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6761_, lean_object* v_b_6762_, lean_object* v_a_6763_, lean_object* v_a_6764_, lean_object* v_a_6765_, lean_object* v_a_6766_, lean_object* v_a_6767_){
_start:
{
lean_object* v_res_6768_; 
v_res_6768_ = l_Lean_Meta_mkLE(v_a_6761_, v_b_6762_, v_a_6763_, v_a_6764_, v_a_6765_, v_a_6766_);
lean_dec(v_a_6766_);
lean_dec_ref(v_a_6765_);
lean_dec(v_a_6764_);
lean_dec_ref(v_a_6763_);
return v_res_6768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6771_, lean_object* v_b_6772_, lean_object* v_a_6773_, lean_object* v_a_6774_, lean_object* v_a_6775_, lean_object* v_a_6776_){
_start:
{
lean_object* v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; 
v___x_6778_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6779_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6780_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6778_, v___x_6779_, v_a_6771_, v_b_6772_, v_a_6773_, v_a_6774_, v_a_6775_, v_a_6776_);
return v___x_6780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6781_, lean_object* v_b_6782_, lean_object* v_a_6783_, lean_object* v_a_6784_, lean_object* v_a_6785_, lean_object* v_a_6786_, lean_object* v_a_6787_){
_start:
{
lean_object* v_res_6788_; 
v_res_6788_ = l_Lean_Meta_mkLT(v_a_6781_, v_b_6782_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_);
lean_dec(v_a_6786_);
lean_dec_ref(v_a_6785_);
lean_dec(v_a_6784_);
lean_dec_ref(v_a_6783_);
return v_res_6788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6794_, lean_object* v_a_6795_, lean_object* v_a_6796_, lean_object* v_a_6797_, lean_object* v_a_6798_){
_start:
{
lean_object* v___x_6800_; lean_object* v___x_6801_; uint8_t v___x_6802_; 
v___x_6800_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6801_ = lean_unsigned_to_nat(3u);
v___x_6802_ = l_Lean_Expr_isAppOfArity(v_h_6794_, v___x_6800_, v___x_6801_);
if (v___x_6802_ == 0)
{
lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v___x_6807_; 
v___x_6803_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6804_ = lean_unsigned_to_nat(1u);
v___x_6805_ = lean_mk_empty_array_with_capacity(v___x_6804_);
v___x_6806_ = lean_array_push(v___x_6805_, v_h_6794_);
v___x_6807_ = l_Lean_Meta_mkAppM(v___x_6803_, v___x_6806_, v_a_6795_, v_a_6796_, v_a_6797_, v_a_6798_);
return v___x_6807_;
}
else
{
lean_object* v___x_6808_; lean_object* v___x_6809_; 
v___x_6808_ = l_Lean_Expr_appArg_x21(v_h_6794_);
lean_dec_ref(v_h_6794_);
v___x_6809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6809_, 0, v___x_6808_);
return v___x_6809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6810_, lean_object* v_a_6811_, lean_object* v_a_6812_, lean_object* v_a_6813_, lean_object* v_a_6814_, lean_object* v_a_6815_){
_start:
{
lean_object* v_res_6816_; 
v_res_6816_ = l_Lean_Meta_mkIffOfEq(v_h_6810_, v_a_6811_, v_a_6812_, v_a_6813_, v_a_6814_);
lean_dec(v_a_6814_);
lean_dec_ref(v_a_6813_);
lean_dec(v_a_6812_);
lean_dec_ref(v_a_6811_);
return v_res_6816_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6822_; lean_object* v___x_6823_; lean_object* v___x_6824_; 
v___x_6822_ = lean_box(0);
v___x_6823_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6824_ = l_Lean_mkConst(v___x_6823_, v___x_6822_);
return v___x_6824_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___x_6829_; 
v___x_6827_ = lean_box(0);
v___x_6828_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6829_ = l_Lean_mkConst(v___x_6828_, v___x_6827_);
return v___x_6829_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6830_; lean_object* v___x_6831_; lean_object* v___x_6832_; 
v___x_6830_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6831_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6832_, 0, v___x_6831_);
lean_ctor_set(v___x_6832_, 1, v___x_6830_);
return v___x_6832_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6837_; lean_object* v___x_6838_; lean_object* v___x_6839_; 
v___x_6837_ = lean_box(0);
v___x_6838_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6839_ = l_Lean_mkConst(v___x_6838_, v___x_6837_);
return v___x_6839_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6842_; lean_object* v___x_6843_; lean_object* v___x_6844_; 
v___x_6842_ = lean_box(0);
v___x_6843_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6844_ = l_Lean_mkConst(v___x_6843_, v___x_6842_);
return v___x_6844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6845_, lean_object* v_a_6846_, lean_object* v_a_6847_, lean_object* v_a_6848_, lean_object* v_a_6849_){
_start:
{
if (lean_obj_tag(v_a_6845_) == 0)
{
lean_object* v___x_6851_; lean_object* v___x_6852_; 
v___x_6851_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6852_, 0, v___x_6851_);
return v___x_6852_;
}
else
{
lean_object* v_tail_6853_; 
v_tail_6853_ = lean_ctor_get(v_a_6845_, 1);
if (lean_obj_tag(v_tail_6853_) == 0)
{
lean_object* v_head_6854_; lean_object* v___x_6856_; uint8_t v_isShared_6857_; uint8_t v_isSharedCheck_6878_; 
v_head_6854_ = lean_ctor_get(v_a_6845_, 0);
v_isSharedCheck_6878_ = !lean_is_exclusive(v_a_6845_);
if (v_isSharedCheck_6878_ == 0)
{
lean_object* v_unused_6879_; 
v_unused_6879_ = lean_ctor_get(v_a_6845_, 1);
lean_dec(v_unused_6879_);
v___x_6856_ = v_a_6845_;
v_isShared_6857_ = v_isSharedCheck_6878_;
goto v_resetjp_6855_;
}
else
{
lean_inc(v_head_6854_);
lean_dec(v_a_6845_);
v___x_6856_ = lean_box(0);
v_isShared_6857_ = v_isSharedCheck_6878_;
goto v_resetjp_6855_;
}
v_resetjp_6855_:
{
lean_object* v___x_6858_; 
lean_inc(v_a_6849_);
lean_inc_ref(v_a_6848_);
lean_inc(v_a_6847_);
lean_inc_ref(v_a_6846_);
lean_inc(v_head_6854_);
v___x_6858_ = lean_infer_type(v_head_6854_, v_a_6846_, v_a_6847_, v_a_6848_, v_a_6849_);
if (lean_obj_tag(v___x_6858_) == 0)
{
lean_object* v_a_6859_; lean_object* v___x_6861_; uint8_t v_isShared_6862_; uint8_t v_isSharedCheck_6869_; 
v_a_6859_ = lean_ctor_get(v___x_6858_, 0);
v_isSharedCheck_6869_ = !lean_is_exclusive(v___x_6858_);
if (v_isSharedCheck_6869_ == 0)
{
v___x_6861_ = v___x_6858_;
v_isShared_6862_ = v_isSharedCheck_6869_;
goto v_resetjp_6860_;
}
else
{
lean_inc(v_a_6859_);
lean_dec(v___x_6858_);
v___x_6861_ = lean_box(0);
v_isShared_6862_ = v_isSharedCheck_6869_;
goto v_resetjp_6860_;
}
v_resetjp_6860_:
{
lean_object* v___x_6864_; 
if (v_isShared_6857_ == 0)
{
lean_ctor_set_tag(v___x_6856_, 0);
lean_ctor_set(v___x_6856_, 1, v_a_6859_);
v___x_6864_ = v___x_6856_;
goto v_reusejp_6863_;
}
else
{
lean_object* v_reuseFailAlloc_6868_; 
v_reuseFailAlloc_6868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6868_, 0, v_head_6854_);
lean_ctor_set(v_reuseFailAlloc_6868_, 1, v_a_6859_);
v___x_6864_ = v_reuseFailAlloc_6868_;
goto v_reusejp_6863_;
}
v_reusejp_6863_:
{
lean_object* v___x_6866_; 
if (v_isShared_6862_ == 0)
{
lean_ctor_set(v___x_6861_, 0, v___x_6864_);
v___x_6866_ = v___x_6861_;
goto v_reusejp_6865_;
}
else
{
lean_object* v_reuseFailAlloc_6867_; 
v_reuseFailAlloc_6867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6867_, 0, v___x_6864_);
v___x_6866_ = v_reuseFailAlloc_6867_;
goto v_reusejp_6865_;
}
v_reusejp_6865_:
{
return v___x_6866_;
}
}
}
}
else
{
lean_object* v_a_6870_; lean_object* v___x_6872_; uint8_t v_isShared_6873_; uint8_t v_isSharedCheck_6877_; 
lean_del_object(v___x_6856_);
lean_dec(v_head_6854_);
v_a_6870_ = lean_ctor_get(v___x_6858_, 0);
v_isSharedCheck_6877_ = !lean_is_exclusive(v___x_6858_);
if (v_isSharedCheck_6877_ == 0)
{
v___x_6872_ = v___x_6858_;
v_isShared_6873_ = v_isSharedCheck_6877_;
goto v_resetjp_6871_;
}
else
{
lean_inc(v_a_6870_);
lean_dec(v___x_6858_);
v___x_6872_ = lean_box(0);
v_isShared_6873_ = v_isSharedCheck_6877_;
goto v_resetjp_6871_;
}
v_resetjp_6871_:
{
lean_object* v___x_6875_; 
if (v_isShared_6873_ == 0)
{
v___x_6875_ = v___x_6872_;
goto v_reusejp_6874_;
}
else
{
lean_object* v_reuseFailAlloc_6876_; 
v_reuseFailAlloc_6876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6876_, 0, v_a_6870_);
v___x_6875_ = v_reuseFailAlloc_6876_;
goto v_reusejp_6874_;
}
v_reusejp_6874_:
{
return v___x_6875_;
}
}
}
}
}
else
{
lean_object* v_head_6880_; lean_object* v___x_6881_; 
lean_inc(v_tail_6853_);
v_head_6880_ = lean_ctor_get(v_a_6845_, 0);
lean_inc(v_head_6880_);
lean_dec_ref_known(v_a_6845_, 2);
v___x_6881_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6853_, v_a_6846_, v_a_6847_, v_a_6848_, v_a_6849_);
if (lean_obj_tag(v___x_6881_) == 0)
{
lean_object* v_a_6882_; lean_object* v_fst_6883_; lean_object* v_snd_6884_; lean_object* v___x_6886_; uint8_t v_isShared_6887_; uint8_t v_isSharedCheck_6912_; 
v_a_6882_ = lean_ctor_get(v___x_6881_, 0);
lean_inc(v_a_6882_);
lean_dec_ref_known(v___x_6881_, 1);
v_fst_6883_ = lean_ctor_get(v_a_6882_, 0);
v_snd_6884_ = lean_ctor_get(v_a_6882_, 1);
v_isSharedCheck_6912_ = !lean_is_exclusive(v_a_6882_);
if (v_isSharedCheck_6912_ == 0)
{
v___x_6886_ = v_a_6882_;
v_isShared_6887_ = v_isSharedCheck_6912_;
goto v_resetjp_6885_;
}
else
{
lean_inc(v_snd_6884_);
lean_inc(v_fst_6883_);
lean_dec(v_a_6882_);
v___x_6886_ = lean_box(0);
v_isShared_6887_ = v_isSharedCheck_6912_;
goto v_resetjp_6885_;
}
v_resetjp_6885_:
{
lean_object* v___x_6888_; 
lean_inc(v_a_6849_);
lean_inc_ref(v_a_6848_);
lean_inc(v_a_6847_);
lean_inc_ref(v_a_6846_);
lean_inc(v_head_6880_);
v___x_6888_ = lean_infer_type(v_head_6880_, v_a_6846_, v_a_6847_, v_a_6848_, v_a_6849_);
if (lean_obj_tag(v___x_6888_) == 0)
{
lean_object* v_a_6889_; lean_object* v___x_6891_; uint8_t v_isShared_6892_; uint8_t v_isSharedCheck_6903_; 
v_a_6889_ = lean_ctor_get(v___x_6888_, 0);
v_isSharedCheck_6903_ = !lean_is_exclusive(v___x_6888_);
if (v_isSharedCheck_6903_ == 0)
{
v___x_6891_ = v___x_6888_;
v_isShared_6892_ = v_isSharedCheck_6903_;
goto v_resetjp_6890_;
}
else
{
lean_inc(v_a_6889_);
lean_dec(v___x_6888_);
v___x_6891_ = lean_box(0);
v_isShared_6892_ = v_isSharedCheck_6903_;
goto v_resetjp_6890_;
}
v_resetjp_6890_:
{
lean_object* v___x_6893_; lean_object* v___x_6894_; lean_object* v___x_6895_; lean_object* v___x_6896_; lean_object* v___x_6898_; 
v___x_6893_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6884_);
lean_inc(v_a_6889_);
v___x_6894_ = l_Lean_mkApp4(v___x_6893_, v_a_6889_, v_snd_6884_, v_head_6880_, v_fst_6883_);
v___x_6895_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6896_ = l_Lean_mkAppB(v___x_6895_, v_a_6889_, v_snd_6884_);
if (v_isShared_6887_ == 0)
{
lean_ctor_set(v___x_6886_, 1, v___x_6896_);
lean_ctor_set(v___x_6886_, 0, v___x_6894_);
v___x_6898_ = v___x_6886_;
goto v_reusejp_6897_;
}
else
{
lean_object* v_reuseFailAlloc_6902_; 
v_reuseFailAlloc_6902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6902_, 0, v___x_6894_);
lean_ctor_set(v_reuseFailAlloc_6902_, 1, v___x_6896_);
v___x_6898_ = v_reuseFailAlloc_6902_;
goto v_reusejp_6897_;
}
v_reusejp_6897_:
{
lean_object* v___x_6900_; 
if (v_isShared_6892_ == 0)
{
lean_ctor_set(v___x_6891_, 0, v___x_6898_);
v___x_6900_ = v___x_6891_;
goto v_reusejp_6899_;
}
else
{
lean_object* v_reuseFailAlloc_6901_; 
v_reuseFailAlloc_6901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6901_, 0, v___x_6898_);
v___x_6900_ = v_reuseFailAlloc_6901_;
goto v_reusejp_6899_;
}
v_reusejp_6899_:
{
return v___x_6900_;
}
}
}
}
else
{
lean_object* v_a_6904_; lean_object* v___x_6906_; uint8_t v_isShared_6907_; uint8_t v_isSharedCheck_6911_; 
lean_del_object(v___x_6886_);
lean_dec(v_snd_6884_);
lean_dec(v_fst_6883_);
lean_dec(v_head_6880_);
v_a_6904_ = lean_ctor_get(v___x_6888_, 0);
v_isSharedCheck_6911_ = !lean_is_exclusive(v___x_6888_);
if (v_isSharedCheck_6911_ == 0)
{
v___x_6906_ = v___x_6888_;
v_isShared_6907_ = v_isSharedCheck_6911_;
goto v_resetjp_6905_;
}
else
{
lean_inc(v_a_6904_);
lean_dec(v___x_6888_);
v___x_6906_ = lean_box(0);
v_isShared_6907_ = v_isSharedCheck_6911_;
goto v_resetjp_6905_;
}
v_resetjp_6905_:
{
lean_object* v___x_6909_; 
if (v_isShared_6907_ == 0)
{
v___x_6909_ = v___x_6906_;
goto v_reusejp_6908_;
}
else
{
lean_object* v_reuseFailAlloc_6910_; 
v_reuseFailAlloc_6910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6910_, 0, v_a_6904_);
v___x_6909_ = v_reuseFailAlloc_6910_;
goto v_reusejp_6908_;
}
v_reusejp_6908_:
{
return v___x_6909_;
}
}
}
}
}
else
{
lean_dec(v_head_6880_);
return v___x_6881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6913_, lean_object* v_a_6914_, lean_object* v_a_6915_, lean_object* v_a_6916_, lean_object* v_a_6917_, lean_object* v_a_6918_){
_start:
{
lean_object* v_res_6919_; 
v_res_6919_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_, v_a_6917_);
lean_dec(v_a_6917_);
lean_dec_ref(v_a_6916_);
lean_dec(v_a_6915_);
lean_dec_ref(v_a_6914_);
return v_res_6919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_6920_, lean_object* v_a_6921_, lean_object* v_a_6922_, lean_object* v_a_6923_, lean_object* v_a_6924_){
_start:
{
lean_object* v___x_6926_; 
v___x_6926_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_6920_, v_a_6921_, v_a_6922_, v_a_6923_, v_a_6924_);
if (lean_obj_tag(v___x_6926_) == 0)
{
lean_object* v_a_6927_; lean_object* v___x_6929_; uint8_t v_isShared_6930_; uint8_t v_isSharedCheck_6935_; 
v_a_6927_ = lean_ctor_get(v___x_6926_, 0);
v_isSharedCheck_6935_ = !lean_is_exclusive(v___x_6926_);
if (v_isSharedCheck_6935_ == 0)
{
v___x_6929_ = v___x_6926_;
v_isShared_6930_ = v_isSharedCheck_6935_;
goto v_resetjp_6928_;
}
else
{
lean_inc(v_a_6927_);
lean_dec(v___x_6926_);
v___x_6929_ = lean_box(0);
v_isShared_6930_ = v_isSharedCheck_6935_;
goto v_resetjp_6928_;
}
v_resetjp_6928_:
{
lean_object* v_fst_6931_; lean_object* v___x_6933_; 
v_fst_6931_ = lean_ctor_get(v_a_6927_, 0);
lean_inc(v_fst_6931_);
lean_dec(v_a_6927_);
if (v_isShared_6930_ == 0)
{
lean_ctor_set(v___x_6929_, 0, v_fst_6931_);
v___x_6933_ = v___x_6929_;
goto v_reusejp_6932_;
}
else
{
lean_object* v_reuseFailAlloc_6934_; 
v_reuseFailAlloc_6934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6934_, 0, v_fst_6931_);
v___x_6933_ = v_reuseFailAlloc_6934_;
goto v_reusejp_6932_;
}
v_reusejp_6932_:
{
return v___x_6933_;
}
}
}
else
{
lean_object* v_a_6936_; lean_object* v___x_6938_; uint8_t v_isShared_6939_; uint8_t v_isSharedCheck_6943_; 
v_a_6936_ = lean_ctor_get(v___x_6926_, 0);
v_isSharedCheck_6943_ = !lean_is_exclusive(v___x_6926_);
if (v_isSharedCheck_6943_ == 0)
{
v___x_6938_ = v___x_6926_;
v_isShared_6939_ = v_isSharedCheck_6943_;
goto v_resetjp_6937_;
}
else
{
lean_inc(v_a_6936_);
lean_dec(v___x_6926_);
v___x_6938_ = lean_box(0);
v_isShared_6939_ = v_isSharedCheck_6943_;
goto v_resetjp_6937_;
}
v_resetjp_6937_:
{
lean_object* v___x_6941_; 
if (v_isShared_6939_ == 0)
{
v___x_6941_ = v___x_6938_;
goto v_reusejp_6940_;
}
else
{
lean_object* v_reuseFailAlloc_6942_; 
v_reuseFailAlloc_6942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6942_, 0, v_a_6936_);
v___x_6941_ = v_reuseFailAlloc_6942_;
goto v_reusejp_6940_;
}
v_reusejp_6940_:
{
return v___x_6941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_6944_, lean_object* v_a_6945_, lean_object* v_a_6946_, lean_object* v_a_6947_, lean_object* v_a_6948_, lean_object* v_a_6949_){
_start:
{
lean_object* v_res_6950_; 
v_res_6950_ = l_Lean_Meta_mkAndIntroN(v_hs_6944_, v_a_6945_, v_a_6946_, v_a_6947_, v_a_6948_);
lean_dec(v_a_6948_);
lean_dec_ref(v_a_6947_);
lean_dec(v_a_6946_);
lean_dec_ref(v_a_6945_);
return v_res_6950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7007_; uint8_t v___x_7008_; lean_object* v___x_7009_; lean_object* v___x_7010_; 
v___x_7007_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7008_ = 0;
v___x_7009_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7010_ = l_Lean_registerTraceClass(v___x_7007_, v___x_7008_, v___x_7009_);
if (lean_obj_tag(v___x_7010_) == 0)
{
lean_object* v___x_7011_; uint8_t v___x_7012_; lean_object* v___x_7013_; 
lean_dec_ref_known(v___x_7010_, 1);
v___x_7011_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7012_ = 1;
v___x_7013_ = l_Lean_registerTraceClass(v___x_7011_, v___x_7012_, v___x_7009_);
if (lean_obj_tag(v___x_7013_) == 0)
{
lean_object* v___x_7014_; lean_object* v___x_7015_; 
lean_dec_ref_known(v___x_7013_, 1);
v___x_7014_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7015_ = l_Lean_registerTraceClass(v___x_7014_, v___x_7012_, v___x_7009_);
return v___x_7015_;
}
else
{
return v___x_7013_;
}
}
else
{
return v___x_7010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7016_){
_start:
{
lean_object* v_res_7017_; 
v_res_7017_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7017_;
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
